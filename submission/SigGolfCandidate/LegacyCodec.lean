import SigGolfCandidate.Cap776.CountForests
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

/-- Every route-C cost is monotone in the bucket price (needed for the cap-776 thinning). -/
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

/-! Route C data: inherited RC938 fee tables, with cap-776 moments and affine Scarf bounds. -/

namespace ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.RouteCFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rcPar : Par := ⟨826, (27/50 : ℚ), (10 : ℚ), (31929671/16000000 : ℚ), (19669/20000 : ℚ), (41661/5000000 : ℚ), (912809/10000000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3873, 18446744073709551616), (3874, 3874, 18386072743097911461), (3875, 3875, 18204032418908823229), (3876, 3876, 18023794474167151712), (3877, 3877, 17845341063531833378), (3878, 3878, 17668654518348349879), (3879, 3879, 17493717344899356316), (3880, 3880, 17320512222672630016), (3881, 3881, 17149022002646168333), (3882, 3882, 16979229705590265676), (3883, 3883, 16811118520386401659), (3884, 3884, 16644671802362773920), (3885, 3885, 16479873071646310812), (3886, 3886, 16316706011531000804), (3887, 3887, 16155154466862377034), (3888, 3888, 15995202442437997063), (3889, 3889, 15836834101423759468), (3890, 3890, 15680033763785900464), (3891, 3891, 15524785904738515311), (3892, 3892, 15371075153206450803), (3893, 3893, 15218886290303416636), (3894, 3894, 15068204247825164986), (3895, 3895, 14919014106757589095), (3896, 3896, 14771301095799593164), (3897, 3897, 14625050589900587291), (3898, 3898, 14480248108812462664), (3899, 3899, 14336879315655903628), (3900, 3900, 14194930015500894681), (3901, 3901, 14054386153961281863), (3902, 3902, 13915233815803249369), (3903, 3903, 13777459223567573633), (3904, 3904, 13641048736205518448), (3905, 3905, 13505988847728236087), (3906, 3906, 13372266185869540680), (3907, 3907, 13239867510761921466), (3908, 3908, 13108779713625664818), (3909, 3909, 12978989815470955265), (3910, 3910, 12850484965812826995), (3911, 3911, 12723252441398838609), (3912, 3912, 12597279644949345157), (3913, 3913, 12472554103910242730), (3914, 3914, 12349063469218062109), (3915, 3915, 12226795514077289217), (3916, 3916, 12105738132749791304), (3917, 3917, 11985879339356229014), (3918, 3918, 11867207266689335657), (3919, 3919, 11749710165038946195), (3920, 3920, 11633376401028659599), (3921, 3921, 11518194456464019405), (3922, 3922, 11404152927192098421), (3923, 3923, 11291240521972374674), (3924, 3924, 11179446061358786806), (3925, 3925, 11068758476592858224), (3926, 3926, 10959166808507780420), (3927, 3927, 10850660206443346950), (3928, 3928, 10743227927171630644), (3929, 3929, 10636859333833297667), (3930, 3930, 10531543894884453136), (3931, 3931, 10427271183053913996), (3932, 3932, 10324030874310805936), (3933, 3933, 10221812746842382115), (3934, 3934, 10120606680041962490), (3935, 3935, 10020402653506893555), (3936, 3936, 9921190746046429262), (3937, 3937, 9822961134699434913), (3938, 3938, 9725704093761816746), (3939, 3939, 9629409993823580936), (3940, 3940, 9534069300815426670), (3941, 3941, 9439672575064778881), (3942, 3942, 9346210470361167209), (3943, 3943, 9253673733030858623), (3944, 3944, 9162053201020652102), (3945, 3945, 9071339802990744655), (3946, 3946, 8981524557416578866), (3947, 3947, 8892598571699583036), (3948, 3948, 8804553041286715877), (3949, 3949, 8717379248798728591), (3950, 3950, 8631068563167058011), (3951, 3951, 8545612438779265358), (3952, 3952, 8461002414632935998), (3953, 3953, 8377230113497956433), (3954, 3954, 8294287241087085578), (3955, 3955, 8212165585234738196), (3956, 3956, 8130857015083899204), (3957, 3957, 8050353480281088320), (3958, 3958, 7970647010179295367), (3959, 3959, 7891729713048807294), (3960, 3960, 7813593775295848806), (3961, 3961, 7736231460688959214), (3962, 3962, 7659635109593028924), (3963, 3963, 7583797138210919727), (3964, 3964, 7508710037832593789), (3965, 3965, 7434366374091677019), (3966, 3966, 7360758786229383187), (3967, 3967, 7287879986365725928), (3968, 3968, 7215722758777946463), (3969, 3969, 7144279959186085607), (3970, 3970, 7073544514045629314), (3971, 3971, 7003509419847157737), (3972, 3972, 6934167742422928452), (3973, 3973, 6865512616260325200), (3974, 3974, 6797537243822104159), (3975, 3975, 6730234894873370454), (3976, 3976, 6663598905815218271), (3977, 3977, 6597622679024968585), (3978, 3978, 6532299682202939194), (3979, 3979, 6467623447725682370), (3980, 3980, 6403587572005626109), (3981, 3981, 6340185714857055553), (3982, 3982, 6277411598868371835), (3983, 3983, 6215259008780566173), (3984, 3984, 6153721790871847696), (3985, 3985, 6092793852348364056), (3986, 3986, 6032469160740954511), (3987, 3987, 5972741743307875753), (3988, 3988, 5913605686443441340), (3989, 3989, 5855055135092516178), (3990, 3990, 5797084292170808097), (3991, 3991, 5739687417990899106), (3992, 3992, 5682858829693959511), (3993, 3993, 5626592900687088625), (3994, 3994, 5570884060086226361), (3995, 3995, 5515726792164580555), (3996, 3996, 5461115635806515401), (3997, 3997, 5407045183966846932), (3998, 3998, 5353510083135492012), (3999, 3999, 5300505032807417834), (4000, 4000, 5248024784957839439), (4001, 4001, 5196064143522613306), (4002, 4002, 5144617963883775551), (4003, 4003, 5093681152360173813), (4004, 4004, 5043248665703142389), (4005, 4005, 4993315510597170682), (4006, 4006, 4943876743165515527), (4007, 4007, 4894927468480708442), (4008, 4008, 4846462840079909349), (4009, 4009, 4798478059485058761), (4010, 4010, 4750968375727780952), (4011, 4011, 4703929084878991041), (4012, 4012, 4657355529583159447), (4013, 4013, 4611243098597187571), (4014, 4014, 4565587226333849080), (4015, 4015, 4520383392409751565), (4016, 4016, 4475627121197773826), (4017, 4017, 4431313981383934481), (4018, 4018, 4387439585528648001), (4019, 4019, 4343999589632324754), (4020, 4020, 4300989692705272034), (4021, 4021, 4258405636341853499), (4022, 4022, 4216243204298864850), (4023, 4023, 4174498222078084010), (4024, 4024, 4133166556512954465), (4025, 4025, 4092244115359360857), (4026, 4026, 4051726846890456294), (4027, 4027, 4011610739495501281), (4028, 4028, 3971891821282674536), (4029, 4029, 3932566159685816372), (4030, 4030, 3893629861075065715), (4031, 4031, 3855079070371352193), (4032, 4032, 3816909970664705142), (4033, 4033, 3779118782836341724), (4034, 4034, 3741701765184496757), (4035, 4035, 3704655213053957185), (4036, 4036, 3667975458469264539), (4037, 4037, 3631658869771549049), (4038, 4038, 3595701851258959454), (4039, 4039, 3560100842830652925), (4040, 4040, 3524852319634309827), (4041, 4041, 3489952791717138443), (4042, 4042, 3455398803680335092), (4043, 4043, 3421186934336965437), (4044, 4044, 3387313796373233106), (4045, 4045, 3353776036013102085), (4046, 4046, 3320570332686239688), (4047, 4047, 3287693398699247216), (4048, 4048, 3255141978910145759), (4049, 4049, 3222912850406084910), (4050, 4050, 3191002822184242485), (4051, 4051, 3159408734835883648), (4052, 4052, 3128127460233548167), (4053, 4053, 3097155901221334818), (4054, 4054, 3066490991308252296), (4055, 4055, 3036129694364606233), (4056, 4056, 3006069004321392310), (4057, 4057, 2976305944872665654), (4058, 4058, 2946837569180857083), (4059, 4059, 2917660959585007013), (4060, 4060, 2888773227311888131), (4061, 4061, 2860171512189988249), (4062, 4062, 2831852982366324999), (4063, 4063, 2803814834026064355), (4064, 4064, 2776054291114915203), (4065, 4065, 2748568605064272479), (4066, 4066, 2721355054519081662), (4067, 4067, 2694410945068397685), (4068, 4068, 2667733608978611569), (4069, 4069, 2641320404929318386), (4070, 4070, 2615168717751800382), (4071, 4071, 2589275958170099388), (4072, 4072, 2563639562544652859), (4073, 4073, 2538256992618468177), (4074, 4074, 2513125735265810077), (4075, 4075, 2488243302243376314), (4076, 4076, 2463607229943936944), (4077, 4077, 2439215079152412816), (4078, 4078, 2415064434804369125), (4079, 4079, 2391152905746900124), (4080, 4080, 2367478124501881310), (4081, 4081, 2344037747031565654), (4082, 4082, 2320829452506500647), (4083, 4083, 2297850943075743215), (4084, 4084, 2275099943639349718), (4085, 4085, 2252574201623118533), (4086, 4086, 2230271486755562904), (4087, 4087, 2208189590847091984), (4088, 4088, 2186326327571378202), (4089, 4089, 2164679532248889309), (4090, 4090, 2143247061632563672), (4091, 4091, 2122026793695607596), (4092, 4092, 2101016627421393660), (4093, 4093, 2080214482595439267), (4094, 4094, 2059618299599444819), (4095, 4095, 2039226039207371108), (4096, 4096, 2019035682383535750), (4097, 4097, 1999045230082708663), (4098, 4098, 1979252703052186796), (4099, 4099, 1959656141635828510), (4100, 4100, 1940253605580028228), (4101, 4101, 1921043173841612107), (4102, 4102, 1902022944397635750), (4103, 4103, 1883191034057065099), (4104, 4104, 1864545578274321880), (4105, 4105, 1846084730964675129), (4106, 4106, 1827806664321460523), (4107, 4107, 1809709568635109429), (4108, 4108, 1791791652113969732), (4109, 4109, 1774051140706900724), (4110, 4110, 1756486277927624480), (4111, 4111, 1739095324680816317), (4112, 4112, 1721876559089917145), (4113, 4113, 1704828276326650639), (4114, 4114, 1687948788442228355), (4115, 4115, 1671236424200226094), (4116, 4116, 1654689528911114945), (4117, 4117, 1638306464268430638), (4118, 4118, 1622085608186564989), (4119, 4119, 1606025354640163355), (4120, 4120, 1590124113505112233), (4121, 4121, 1574380310401101220), (4122, 4122, 1558792386535743783), (4123, 4123, 1543358798550241369), (4124, 4124, 1528078018366575613), (4125, 4125, 1512948533036213478), (4126, 4126, 1497968844590310374), (4127, 4127, 1483137469891396410), (4128, 4128, 1468452940486531099), (4129, 4129, 1453913802461911979), (4130, 4130, 1439518616298922752), (4131, 4131, 1425265956731606685), (4132, 4132, 1411154412605551173), (4133, 4133, 1397182586738169479), (4134, 4134, 1383349095780365820), (4135, 4135, 1369652570079570119), (4136, 4136, 1356091653544128831), (4137, 4137, 1342665003509038446), (4138, 4138, 1329371290603008363), (4139, 4139, 1316209198616839963), (4140, 4140, 1303177424373108874), (4141, 4141, 1290274677597137499), (4142, 4142, 1277499680789245049), (4143, 4143, 1264851169098262425), (4144, 4144, 1252327890196299430), (4145, 4145, 1239928604154751911), (4146, 4146, 1227652083321536546), (4147, 4147, 1215497112199541135), (4148, 4148, 1203462487326278351), (4149, 4149, 1191547017154731041), (4150, 4150, 1179749521935377268), (4151, 4151, 1168068833599383434), (4152, 4152, 1156503795642953895), (4153, 4153, 1145053263012825638), (4154, 4154, 1133716101992896672), (4155, 4155, 1122491190091976903), (4156, 4156, 1111377415932650399), (4157, 4157, 1100373679141238018), (4158, 4158, 1089478890238849523), (4159, 4159, 1078691970533514379), (4160, 4160, 1068011852013380574), (4161, 4161, 1057437477240970865), (4162, 4162, 1046967799248486005), (4163, 4163, 1036601781434144559), (4164, 4164, 1026338397459549069), (4165, 4165, 1016176631148068385), (4166, 4166, 1006115476384226124), (4167, 4167, 996153937014085271), (4168, 4168, 986291026746619080), (4169, 4169, 976525769056058495), (4170, 4170, 966857197085206431), (4171, 4171, 957284353549709337), (4172, 4172, 947806290643276572), (4173, 4173, 938422069943838190), (4174, 4174, 929130762320631871), (4175, 4175, 919931447842209773), (4176, 4176, 910823215685356211), (4177, 4177, 901805164044907140), (4178, 4178, 892876400044462515), (4179, 4179, 884036039647982688), (4180, 4180, 875283207572260087), (4181, 4181, 866617037200257512), (4182, 4182, 858036670495304467), (4183, 4183, 849541257916143037), (4184, 4184, 841129958332814888), (4185, 4185, 832801938943381077), (4186, 4186, 824556375191466413), (4187, 4187, 816392450684620211), (4188, 4188, 808309357113485357), (4189, 4189, 800306294171767681), (4190, 4190, 792382469476997704), (4191, 4191, 784537098492076934), (4192, 4192, 776769404447600925), (4193, 4193, 769078618264951411), (4194, 4194, 761463978480149912), (4195, 4195, 753924731168465259), (4196, 4196, 746460129869767583), (4197, 4197, 739069435514621370), (4198, 4198, 731751916351110267), (4199, 4199, 724506847872386403), (4200, 4200, 717333512744937033), (4201, 4201, 710231200737561419), (4202, 4202, 703199208651050909), (4203, 4203, 696236840248565257), (4204, 4204, 689343406186698274), (4205, 4205, 682518223947226014), (4206, 4206, 675760617769530707), (4207, 4207, 669069918583693769), (4208, 4208, 662445463944251257), (4209, 4209, 655886597964605205), (4210, 4210, 649392671252084361), (4211, 4211, 642963040843647882), (4212, 4212, 636597070142225626), (4213, 4213, 630294128853688739), (4214, 4214, 624053592924444296), (4215, 4215, 617874844479647817), (4216, 4216, 611757271762027542), (4217, 4217, 605700269071314398), (4218, 4218, 599703236704271681), (4219, 4219, 593765580895318496), (4220, 4220, 587886713757741085), (4221, 4221, 582066053225486223), (4222, 4222, 576303022995530914), (4223, 4223, 570597052470822687), (4224, 4224, 564947576703784839), (4225, 4225, 559354036340381029), (4226, 4226, 553815877564733692), (4227, 4227, 548332552044290784), (4228, 4228, 542903516875535430), (4229, 4229, 537528234530233099), (4230, 4230, 532206172802210989), (4231, 4231, 526936804754664345), (4232, 4232, 521719608667984500), (4233, 4233, 516554067988103466), (4234, 4234, 511439671275349966), (4235, 4235, 506375912153811847), (4236, 4236, 501362289261199849), (4237, 4237, 496398306199207771), (4238, 4238, 491483471484364130), (4239, 4239, 486617298499370426), (4240, 4240, 481799305444921214), (4241, 4241, 477029015292001202), (4242, 4242, 472305955734654655), (4243, 4243, 467629659143222431), (4244, 4244, 462999662518042011), (4245, 4245, 458415507443605951), (4246, 4246, 453876740043174209), (4247, 4247, 449382910933835851), (4248, 4248, 444933575182015694), (4249, 4249, 440528292259421479), (4250, 4250, 436166625999427207), (4251, 4251, 431848144553888324), (4252, 4252, 427572420350384479), (4253, 4253, 423339030049885623), (4254, 4254, 419147554504837250), (4255, 4255, 414997578717660644), (4256, 4256, 410888691799664004), (4257, 4257, 406820486930360400), (4258, 4258, 402792561317188514), (4259, 4259, 398804516155632193), (4260, 4260, 394855956589734844), (4261, 4261, 390946491673004796), (4262, 4262, 387075734329707719), (4263, 4263, 383243301316542296), (4264, 4264, 379448813184695343), (4265, 4265, 375691894242272616), (4266, 4266, 371972172517101600), (4267, 4267, 368289279719902575), (4268, 4268, 364642851207824331), (4269, 4269, 361032525948340922), (4270, 4270, 357457946483505864), (4271, 4271, 353918758894560261), (4272, 4272, 350414612766891347), (4273, 4273, 346945161155337968), (4274, 4274, 343510060549839572), (4275, 4275, 340108970841425319), (4276, 4276, 336741555288539920), (4277, 4277, 333407480483702891), (4278, 4278, 330106416320497912), (4279, 4279, 326838035960889021), (4280, 4280, 323602015802860417), (4281, 4281, 320398035448376651), (4282, 4282, 317225777671660050), (4283, 4283, 314084928387782228), (4284, 4284, 310975176621566562), (4285, 4285, 307896214476798577), (4286, 4286, 304847737105741165), (4287, 4287, 301829442678951649), (4288, 4288, 298841032355397672), (4289, 4289, 295882210252868982), (4290, 4290, 292952683418682160), (4291, 4291, 290052161800675406), (4292, 4292, 287180358218490501), (4293, 4293, 284336988335139110), (4294, 4294, 281521770628850604), (4295, 4295, 278734426365198618), (4296, 4296, 275974679569503582), (4297, 4297, 273242256999508497), (4298, 4298, 270536888118325245), (4299, 4299, 267858305067648757), (4300, 4300, 265206242641236393), (4301, 4301, 262580438258649894), (4302, 4302, 259980631939257321), (4303, 4303, 257406566276492397), (4304, 4304, 254857986412368710), (4305, 4305, 252334640012246248), (4306, 4306, 249836277239847770), (4307, 4307, 247362650732522544), (4308, 4308, 244913515576754995), (4309, 4309, 242488629283915836), (4310, 4310, 240087751766253303), (4311, 4311, 237710645313122082), (4312, 4312, 235357074567447606), (4313, 4313, 233026806502423373), (4314, 4314, 230719610398438983), (4315, 4315, 228435257820236617), (4316, 4316, 226173522594293680), (4317, 4317, 223934180786429386), (4318, 4318, 221717010679633055), (4319, 4319, 219521792752111936), (4320, 4320, 217348309655556372), (4321, 4321, 215196346193620171), (4322, 4322, 213065689300614030), (4323, 4323, 210956128020409931), (4324, 4324, 208867453485554387), (4325, 4325, 206799458896588502), (4326, 4326, 204751939501572774), (4327, 4327, 202724692575814628), (4328, 4328, 200717517401796661), (4329, 4329, 198730215249303625), (4330, 4330, 196762589355746164), (4331, 4331, 194814444906679370), (4332, 4332, 192885589016514228), (4333, 4333, 190975830709420027), (4334, 4334, 189084980900415869), (4335, 4335, 187212852376649375), (4336, 4336, 185359259778860767), (4337, 4337, 183524019583030463), (4338, 4338, 181706950082208379), (4339, 4339, 179907871368523147), (4340, 4340, 178126605315369453), (4341, 4341, 176362975559771736), (4342, 4342, 174616807484922510), (4343, 4343, 172887928202893575), (4344, 4344, 171176166537518391), (4345, 4345, 169481353007443951), (4346, 4346, 167803319809350447), (4347, 4347, 166141900801337076), (4348, 7209, 164496931486472353)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 1901259529855630), (3001, 3001, 1920272125154186), (3002, 3002, 1939474846405728), (3003, 3003, 1958869594869786), (3004, 3004, 1978458290818483), (3005, 3005, 1998242873726668), (3006, 3006, 2018225302463935), (3007, 3007, 2038407555488574), (3008, 3008, 2058791631043460), (3009, 3009, 2079379547353895), (3010, 3010, 2100173342827434), (3011, 3011, 2121175076255708), (3012, 3012, 2142386827018265), (3013, 3013, 2163810695288448), (3014, 3014, 2185448802241332), (3015, 3015, 2207303290263745), (3016, 3016, 2229376323166383), (3017, 3017, 2251670086398047), (3018, 3018, 2274186787262027), (3019, 3019, 2296928655134647), (3020, 3020, 2319897941685994), (3021, 3021, 2343096921102854), (3022, 3022, 2366527890313882), (3023, 3023, 2390193169217021), (3024, 3024, 2414095100909191), (3025, 3025, 2438236051918283), (3026, 3026, 2462618412437466), (3027, 3027, 2487244596561841), (3028, 3028, 2512117042527459), (3029, 3029, 2537238212952734), (3030, 3030, 2562610595082261), (3031, 3031, 2588236701033084), (3032, 3032, 2614119068043415), (3033, 3033, 2640260258723849), (3034, 3034, 2666662861311087), (3035, 3035, 2693329489924198), (3036, 3036, 2720262784823440), (3037, 3037, 2747465412671674), (3038, 3038, 2774940066798391), (3039, 3039, 2802689467466375), (3040, 3040, 2830716362141039), (3041, 3041, 2859023525762449), (3042, 3042, 2887613761020074), (3043, 3043, 2916489898630274), (3044, 3044, 2945654797616577), (3045, 3045, 2975111345592743), (3046, 3046, 3004862459048670), (3047, 3047, 3034911083639157), (3048, 3048, 3065260194475549), (3049, 3049, 3095912796420304), (3050, 3050, 3126871924384507), (3051, 3051, 3158140643628352), (3052, 3052, 3189722050064636), (3053, 3053, 3221619270565282), (3054, 3054, 3253835463270935), (3055, 3055, 3286373817903644), (3056, 3056, 3319237556082681), (3057, 3057, 3352429931643507), (3058, 3058, 3385954230959942), (3059, 3059, 3419813773269542), (3060, 3060, 3454011911002237), (3061, 3061, 3488552030112260), (3062, 3062, 3523437550413382), (3063, 3063, 3558671925917516), (3064, 3064, 3594258645176691), (3065, 3065, 3630201231628458), (3066, 3066, 3666503243944743), (3067, 3067, 3703168276384190), (3068, 3068, 3740199959148032), (3069, 3069, 3777601958739512), (3070, 3070, 3815377978326907), (3071, 3071, 3853531758110177), (3072, 3072, 3892067075691278), (3073, 3073, 3930987746448191), (3074, 3074, 3970297623912673), (3075, 3075, 4010000600151800), (3076, 3076, 4050100606153318), (3077, 3077, 4090601612214851), (3078, 3078, 4131507628336999), (3079, 3079, 4172822704620369), (3080, 3080, 4214550931666573), (3081, 3081, 4256696440983239), (3082, 3082, 4299263405393071), (3083, 3083, 4342256039447002), (3084, 3084, 4385678599841472), (3085, 3085, 4429535385839887), (3086, 3086, 4473830739698285), (3087, 3087, 4518569047095268), (3088, 3088, 4563754737566221), (3089, 3089, 4609392284941883), (3090, 3090, 4655486207791302), (3091, 3091, 4702041069869215), (3092, 3092, 4749061480567907), (3093, 3093, 4796552095373586), (3094, 3094, 4844517616327322), (3095, 3095, 4892962792490595), (3096, 3096, 4941892420415501), (3097, 3097, 4991311344619656), (3098, 3098, 5041224458065853), (3099, 3099, 5091636702646511), (3100, 3100, 5142553069672976), (3101, 3101, 5193978600369706), (3102, 3102, 5245918386373403), (3103, 3103, 5298377570237137), (3104, 3104, 5351361345939509), (3105, 3105, 5404874959398904), (3106, 3106, 5458923708992893), (3107, 3107, 5513512946082822), (3108, 3108, 5568648075543650), (3109, 3109, 5624334556299086), (3110, 3110, 5680577901862077), (3111, 3111, 5737383680880698), (3112, 3112, 5794757517689505), (3113, 3113, 5852705092866400), (3114, 3114, 5911232143795064), (3115, 3115, 5970344465233015), (3116, 3116, 6030047909885345), (3117, 3117, 6090348388984198), (3118, 3118, 6151251872874040), (3119, 3119, 6212764391602781), (3120, 3120, 6274892035518808), (3121, 3121, 6337640955873997), (3122, 3122, 6401017365432736), (3123, 3123, 6465027539087064), (3124, 3124, 6529677814477934), (3125, 3125, 6594974592622714), (3126, 3126, 6660924338548941), (3127, 3127, 6727533581934430), (3128, 3128, 6794808917753775), (3129, 3129, 6862757006931312), (3130, 3130, 6931384577000626), (3131, 3131, 7000698422770632), (3132, 3132, 7070705406998338), (3133, 3133, 7141412461068321), (3134, 3134, 7212826585679005), (3135, 3135, 7284954851535795), (3136, 3136, 7357804400051153), (3137, 3137, 7431382444051664), (3138, 3138, 7505696268492181), (3139, 3139, 7580753231177103), (3140, 3140, 7656560763488874), (3141, 3141, 7733126371123762), (3142, 3142, 7810457634835000), (3143, 3143, 7888562211183350), (3144, 3144, 7967447833295183), (3145, 3145, 8047122311628135), (3146, 3146, 8127593534744417), (3147, 3147, 8208869470091861), (3148, 3148, 8290958164792779), (3149, 3149, 8373867746440707), (3150, 3150, 8457606423905114), (3151, 3151, 8542182488144165), (3152, 3152, 8627604313025607), (3153, 3153, 8713880356155863), (3154, 3154, 8801019159717422), (3155, 3155, 8889029351314596), (3156, 3156, 8977919644827742), (3157, 3157, 9067698841276019), (3158, 3158, 9158375829688780), (3159, 3159, 9249959587985667), (3160, 3160, 9342459183865524), (3161, 3161, 9435883775704179), (3162, 3162, 9530242613461221), (3163, 3163, 9625545039595833), (3164, 3164, 9721800489991792), (3165, 3165, 9819018494891709), (3166, 3166, 9917208679840627), (3167, 3167, 10016380766639033), (3168, 3168, 10116544574305423), (3169, 3169, 10217710020048477), (3170, 3170, 10319887120248962), (3171, 3171, 10423085991451452), (3172, 3172, 10527316851365966), (3173, 3173, 10632590019879626), (3174, 3174, 10738915920078422), (3175, 3175, 10846305079279206), (3176, 3176, 10954768130071998), (3177, 3177, 11064315811372718), (3178, 3178, 11174958969486446), (3179, 3179, 11286708559181310), (3180, 3180, 11399575644773123), (3181, 3181, 11513571401220854), (3182, 3182, 11628707115233063), (3183, 3183, 11744994186385394), (3184, 3184, 11862444128249247), (3185, 3185, 11981068569531740), (3186, 3186, 12100879255227057), (3187, 3187, 12221888047779328), (3188, 3188, 12344106928257121), (3189, 3189, 12467547997539692), (3190, 3190, 12592223477515089), (3191, 3191, 12718145712290240), (3192, 3192, 12845327169413143), (3193, 3193, 12973780441107274), (3194, 3194, 13103518245518347), (3195, 3195, 13234553427973530), (3196, 3196, 13366898962253265), (3197, 3197, 13500567951875798), (3198, 3198, 13635573631394556), (3199, 3199, 13771929367708502), (3200, 3200, 13909648661385587), (3201, 3201, 14048745147999443), (3202, 3202, 14189232599479437), (3203, 3203, 14331124925474231), (3204, 3204, 14474436174728974), (3205, 3205, 14619180536476263), (3206, 3206, 14765372341841026), (3207, 3207, 14913026065259436), (3208, 3208, 15062156325912031), (3209, 3209, 15212777889171151), (3210, 3210, 15364905668062862), (3211, 3211, 15518554724743491), (3212, 3212, 15673740271990926), (3213, 3213, 15830477674710835), (3214, 3214, 15988782451457944), (3215, 3215, 16148670275972523), (3216, 3216, 16310156978732248), (3217, 3217, 16473258548519571), (3218, 3218, 16637991134004766), (3219, 3219, 16804371045344814), (3220, 3220, 16972414755798262), (3221, 3221, 17142138903356245), (3222, 3222, 17313560292389807), (3223, 3223, 17486695895313705), (3224, 3224, 17661562854266842), (3225, 3225, 17838178482809511), (3226, 3226, 18016560267637606), (3227, 3227, 18196725870313982), (3228, 3228, 18378693129017122), (3229, 3229, 18562480060307293), (3230, 3230, 18748104860910366), (3231, 3231, 18935585909519470), (3232, 3232, 19124941768614664), (3233, 3233, 19316191186300811), (3234, 3234, 19509353098163819), (3235, 3235, 19704446629145457), (3236, 3236, 19901491095436912), (3237, 3237, 20100506006391281), (3238, 3238, 20301511066455194), (3239, 3239, 20504526177119746), (3240, 3240, 20709571438890943), (3241, 3241, 20916667153279852), (3242, 3242, 21125833824812651), (3243, 3243, 21337092163060777), (3244, 3244, 21550463084691385), (3245, 3245, 21765967715538299), (3246, 3246, 21983627392693682), (3247, 3247, 22203463666620619), (3248, 3248, 22425498303286825), (3249, 3249, 22649753286319693), (3250, 3250, 22876250819182890), (3251, 3251, 23105013327374719), (3252, 3252, 23336063460648466), (3253, 3253, 23569424095254951), (3254, 3254, 23805118336207500), (3255, 3255, 24043169519569575), (3256, 3256, 24283601214765271), (3257, 3257, 24526437226912924), (3258, 3258, 24771701599182053), (3259, 3259, 25019418615173874), (3260, 3260, 25269612801325612), (3261, 3261, 25522308929338869), (3262, 3262, 25777532018632257), (3263, 3263, 26035307338818580), (3264, 3264, 26295660412206766), (3265, 3265, 26558617016328833), (3266, 3266, 26824203186492122), (3267, 3267, 27092445218357043), (3268, 3268, 27363369670540613), (3269, 3269, 27637003367246019), (3270, 3270, 27913373400918480), (3271, 3271, 28192507134927664), (3272, 3272, 28474432206276941), (3273, 3273, 28759176528339710), (3274, 3274, 29046768293623107), (3275, 3275, 29337235976559339), (3276, 3276, 29630608336324932), (3277, 3277, 29926914419688181), (3278, 3278, 30226183563885063), (3279, 3279, 30528445399523914), (3280, 3280, 30833729853519153), (3281, 3281, 31142067152054344), (3282, 3282, 31453487823574888), (3283, 3283, 31768022701810637), (3284, 3284, 32085702928828743), (3285, 3285, 32406559958117030), (3286, 3286, 32730625557698201), (3287, 3287, 33057931813275183), (3288, 3288, 33388511131407935), (3289, 3289, 33722396242722014), (3290, 3290, 34059620205149234), (3291, 3291, 34400216407200726), (3292, 3292, 34744218571272734), (3293, 3293, 35091660756985461), (3294, 3294, 35442577364555316), (3295, 3295, 35797003138200869), (3296, 3296, 36154973169582877), (3297, 3297, 36516522901278706), (3298, 3298, 36881688130291493), (3299, 3299, 37250505011594408), (3300, 3300, 37623010061710352), (3301, 3301, 37999240162327456), (3302, 3302, 38379232563950730), (3303, 3303, 38763024889590238), (3304, 3304, 39150655138486140), (3305, 3305, 39542161689871001), (3306, 3306, 39937583306769711), (3307, 3307, 40336959139837408), (3308, 3308, 40740328731235783), (3309, 3309, 41147732018548140), (3310, 3310, 41559209338733622), (3311, 3311, 41974801432120958), (3312, 3312, 42394549446442168), (3313, 3313, 42818494940906589), (3314, 3314, 43246679890315655), (3315, 3315, 43679146689218812), (3316, 3316, 44115938156111000), (3317, 3317, 44557097537672110), (3318, 3318, 45002668513048831), (3319, 3319, 45452695198179319), (3320, 3320, 45907222150161112), (3321, 3321, 46366294371662723), (3322, 3322, 46829957315379351), (3323, 3323, 47298256888533144), (3324, 3324, 47771239457418476), (3325, 3325, 48248951851992660), (3326, 3326, 48731441370512587), (3327, 3327, 49218755784217713), (3328, 3328, 49710943342059890), (3329, 3329, 50208052775480489), (3330, 3330, 50710133303235294), (3331, 3331, 51217234636267647), (3332, 3332, 51729406982630323), (3333, 3333, 52246701052456626), (3334, 3334, 52769168062981193), (3335, 3335, 53296859743611005), (3336, 3336, 53829828341047115), (3337, 3337, 54368126624457586), (3338, 3338, 54911807890702162), (3339, 3339, 55460925969609183), (3340, 3340, 56015535229305275), (3341, 3341, 56575690581598328), (3342, 3342, 57141447487414311), (3343, 3343, 57712861962288454), (3344, 3344, 58289990581911339), (3345, 3345, 58872890487730452), (3346, 3346, 59461619392607757), (3347, 3347, 60056235586533834), (3348, 3348, 60656797942399172), (3349, 3349, 61263365921823164), (3350, 3350, 61875999581041396), (3351, 3351, 62494759576851810), (3352, 3352, 63119707172620328), (3353, 3353, 63750904244346531), (3354, 3354, 64388413286789996), (3355, 3355, 65032297419657896), (3356, 3356, 65682620393854475), (3357, 3357, 66339446597793020), (3358, 3358, 67002841063770950), (3359, 3359, 67672869474408660), (3360, 3360, 68349598169152746), (3361, 3361, 69033094150844274), (3362, 3362, 69723425092352717), (3363, 3363, 70420659343276244), (3364, 3364, 71124865936709006), (3365, 3365, 71836114596076096), (3366, 3366, 72554475742036857), (3367, 3367, 73280020499457226), (3368, 3368, 74012820704451798), (3369, 3369, 74752948911496316), (3370, 3370, 75500478400611279), (3371, 3371, 76255483184617392), (3372, 3372, 77018038016463566), (3373, 3373, 77788218396628201), (3374, 3374, 78566100580594483), (3375, 3375, 79351761586400428), (3376, 3376, 80145279202264433), (3377, 3377, 80946731994287077), (3378, 3378, 81756199314229948), (3379, 3379, 82573761307372247), (3380, 3380, 83399498920445970), (3381, 3381, 84233493909650429), (3382, 3382, 85075828848746934), (3383, 3383, 85926587137234403), (3384, 3384, 86785853008606747), (3385, 3385, 87653711538692814), (3386, 3386, 88530248654079743), (3387, 3387, 89415551140620540), (3388, 3388, 90309706652026745), (3389, 3389, 91212803718547013), (3390, 3390, 92124931755732483), (3391, 3391, 93046181073289808), (3392, 3392, 93976642884022706), (3393, 3393, 94916409312862933), (3394, 3394, 95865573405991562), (3395, 3395, 96824229140051478), (3396, 3396, 97792471431451993), (3397, 3397, 98770396145766513), (3398, 3398, 99758100107224178), (3399, 3399, 100755681108296419), (3400, 3400, 101763237919379384), (3401, 3401, 102780870298573177), (3402, 3402, 103808679001558909), (3403, 3403, 104846765791574498), (3404, 3404, 105895233449490243), (3405, 3405, 106954185783985146), (3406, 3406, 108023727641824997), (3407, 3407, 109103964918243247), (3408, 3408, 110195004567425680), (3409, 3409, 111296954613099936), (3410, 3410, 112409924159230936), (3411, 3411, 113534023400823245), (3412, 3412, 114669363634831478), (3413, 3413, 115816057271179792), (3414, 3414, 116974217843891590), (3415, 3415, 118143960022330506), (3416, 3416, 119325399622553811), (3417, 3417, 120518653618779349), (3418, 3418, 121723840154967143), (3419, 3419, 122941078556516814), (3420, 3420, 124170489342081982), (3421, 3421, 125412194235502802), (3422, 3422, 126666316177857830), (3423, 3423, 127932979339636408), (3424, 3424, 129212309133032773), (3425, 3425, 130504432224363100), (3426, 3426, 131809476546606731), (3427, 3427, 133127571312072799), (3428, 3428, 134458847025193527), (3429, 3429, 135803435495445462), (3430, 3430, 137161469850399916), (3431, 3431, 138533084548903916), (3432, 3432, 139918415394392955), (3433, 3433, 141317599548336884), (3434, 3434, 142730775543820253), (3435, 3435, 144158083299258456), (3436, 3436, 145599664132251040), (3437, 3437, 147055660773573551), (3438, 3438, 148526217381309286), (3439, 3439, 150011479555122379), (3440, 3440, 151511594350673603), (3441, 3441, 153026710294180339), (3442, 3442, 154556977397122142), (3443, 3443, 156102547171093364), (3444, 3444, 157663572642804297), (3445, 3445, 159240208369232340), (3446, 3446, 160832610452924664), (3447, 3447, 162440936557453910), (3448, 3448, 164065345923028449), (3449, 3449, 165705999382258734), (3450, 3450, 167363059376081321), (3451, 3451, 169036689969842134), (3452, 3452, 170727056869540556), (3453, 3453, 172434327438235961), (3454, 3454, 174158670712618321), (3455, 3455, 175900257419744504), (3456, 3456, 177659259993941949), (3457, 3457, 179435852593881369), (3458, 3458, 181230211119820182), (3459, 3459, 183042513231018384), (3460, 3460, 184872938363328568), (3461, 3461, 186721667746961854), (3462, 3462, 188588884424431472), (3463, 3463, 190474773268675787), (3464, 3464, 192379521001362545), (3465, 3465, 194303316211376170), (3466, 3466, 196246349373489932), (3467, 3467, 198208812867224831), (3468, 3468, 200190900995897079), (3469, 3469, 202192810005856050), (3470, 3470, 204214738105914611), (3471, 3471, 206256885486973757), (3472, 3472, 208319454341843494), (3473, 3473, 210402648885261929), (3474, 3474, 212506675374114549), (3475, 3475, 214631742127855694), (3476, 3476, 216778059549134251), (3477, 3477, 218945840144625593), (3478, 3478, 221135298546071849), (3479, 3479, 223346651531532568), (3480, 3480, 225580118046847894), (3481, 3481, 227835919227316373), (3482, 3482, 230114278419589536), (3483, 3483, 232415421203785432), (3484, 3484, 234739575415823286), (3485, 3485, 237086971169981519), (3486, 3486, 239457840881681334), (3487, 3487, 241852419290498147), (3488, 3488, 244270943483403129), (3489, 3489, 246713652918237160), (3490, 3490, 249180789447419532), (3491, 3491, 251672597341893727), (3492, 3492, 254189323315312664), (3493, 3493, 256731216548465791), (3494, 3494, 259298528713950449), (3495, 3495, 261891514001089953), (3496, 3496, 264510429141100853), (3497, 3497, 267155533432511861), (3498, 3498, 269827088766836980), (3499, 3499, 272525359654505350), (3500, 3500, 275250613251050403), (3501, 3501, 278003119383560907), (3502, 3502, 280783150577396516), (3503, 3503, 283590982083170481), (3504, 3504, 286426891904002186), (3505, 3505, 289291160823042208), (3506, 3506, 292184072431272630), (3507, 3507, 295105913155585356), (3508, 3508, 298056972287141210), (3509, 3509, 301037542010012622), (3510, 3510, 304047917430112748), (3511, 3511, 307088396604413876), (3512, 3512, 310159280570458015), (3513, 3513, 313260873376162595), (3514, 3514, 316393482109924221), (3515, 3515, 319557416931023463), (3516, 3516, 322752991100333697), (3517, 3517, 325980521011337034), (3518, 3518, 329240326221450405), (3519, 3519, 332532729483664909), (3520, 3520, 335858056778501558), (3521, 3521, 339216637346286573), (3522, 3522, 342608803719749439), (3523, 3523, 346034891756946934), (3524, 3524, 349495240674516403), (3525, 3525, 352990193081261567), (3526, 3526, 356520095012074183), (3527, 3527, 360085295962194924), (3528, 3528, 363686148921816874), (3529, 3529, 367323010411035042), (3530, 3530, 370996240515145393), (3531, 3531, 374706202920296847), (3532, 3532, 378453264949499815), (3533, 3533, 382237797598994813), (3534, 3534, 386060175574984761), (3535, 3535, 389920777330734609), (3536, 3536, 393819985104041955), (3537, 3537, 397758184955082375), (3538, 3538, 401735766804633198), (3539, 3539, 405753124472679530), (3540, 3540, 409810655717406326), (3541, 3541, 413908762274580389), (3542, 3542, 418047849897326193), (3543, 3543, 422228328396299455), (3544, 3544, 426450611680262449), (3545, 3545, 430715117797065074), (3546, 3546, 435022268975035725), (3547, 3547, 439372491664786082), (3548, 3548, 443766216581433943), (3549, 3549, 448203878747248282), (3550, 3550, 452685917534720765), (3551, 3551, 457212776710067972), (3552, 3552, 461784904477168652), (3553, 3553, 466402753521940339), (3554, 3554, 471066781057159742), (3555, 3555, 475777448867731340), (3556, 3556, 480535223356408653), (3557, 3557, 485340575589972739), (3558, 3558, 490193981345872467), (3559, 3559, 495095921159331191), (3560, 3560, 500046880370924503), (3561, 3561, 505047349174633748), (3562, 3562, 510097822666380086), (3563, 3563, 515198800893043887), (3564, 3564, 520350788901974326), (3565, 3565, 525554296790994069), (3566, 3566, 530809839758904010), (3567, 3567, 536117938156493050), (3568, 3568, 541479117538057980), (3569, 3569, 546893908713438560), (3570, 3570, 552362847800572946), (3571, 3571, 557886476278578675), (3572, 3572, 563465341041364462), (3573, 3573, 569099994451778106), (3574, 3574, 574790994396295887), (3575, 3575, 580538904340258846), (3576, 3576, 586344293383661435), (3577, 3577, 592207736317498049), (3578, 3578, 598129813680673030), (3579, 3579, 604111111817479760), (3580, 3580, 610152222935654557), (3581, 3581, 616253745165011103), (3582, 3582, 622416282616661214), (3583, 3583, 628640445442827826), (3584, 3584, 634926849897256104), (3585, 3585, 641276118396228665), (3586, 3586, 647688879580190952), (3587, 3587, 654165768375992862), (3588, 3588, 660707426059752790), (3589, 3589, 667314500320350318), (3590, 3590, 673987645323553821), (3591, 3591, 680727521776789360), (3592, 3592, 687534796994557253), (3593, 3593, 694410144964502826), (3594, 3594, 701354246414147854), (3595, 3595, 708367788878289332), (3596, 3596, 715451466767072226), (3597, 3597, 722605981434742948), (3598, 3598, 729832041249090377), (3599, 3599, 737130361661581281), (3600, 3600, 744501665278197094), (3601, 3601, 751946681930979065), (3602, 3602, 759466148750288856), (3603, 3603, 767060810237791744), (3604, 3604, 774731418340169662), (3605, 3605, 782478732523571358), (3606, 3606, 790303519848807072), (3607, 3607, 798206555047295142), (3608, 3608, 806188620597768094), (3609, 3609, 814250506803745775), (3610, 3610, 822393011871783233), (3611, 3611, 830616941990501065), (3612, 3612, 838923111410406076), (3613, 3613, 847312342524510136), (3614, 3614, 855785465949755238), (3615, 3615, 864343320609252790), (3616, 3616, 872986753815345318), (3617, 3617, 881716621353498771), (3618, 3618, 890533787567033759), (3619, 3619, 899439125442704096), (3620, 3620, 908433516697131137), (3621, 3621, 917517851864102449), (3622, 3622, 926693030382743473), (3623, 3623, 935959960686570908), (3624, 3624, 945319560293436617), (3625, 3625, 954772755896370983), (3626, 3626, 964320483455334693), (3627, 3627, 973963688289888040), (3628, 3628, 983703325172786920), (3629, 3629, 993540358424514790), (3630, 3630, 1003475762008759937), (3631, 3631, 1013510519628847537), (3632, 3632, 1023645624825136012), (3633, 3633, 1033882081073387372), (3634, 3634, 1044220901884121246), (3635, 3635, 1054663110902962458), (3636, 3636, 1065209742011992083), (3637, 3637, 1075861839432112004), (3638, 3638, 1086620457826433124), (3639, 3639, 1097486662404697455), (3640, 3640, 1108461529028744430), (3641, 3641, 1119546144319031874), (3642, 3642, 1130741605762222193), (3643, 3643, 1142049021819844415), (3644, 3644, 1153469512038042859), (3645, 3645, 1165004207158423287), (3646, 3646, 1176654249230007520), (3647, 3647, 1188420791722307595), (3648, 3648, 1200304999639530671), (3649, 3649, 1212308049635925978), (3650, 3650, 1224431130132285238), (3651, 3651, 1236675441433608090), (3652, 3652, 1249042195847944171), (3653, 3653, 1261532617806423613), (3654, 3654, 1274147943984487849), (3655, 3655, 1286889423424332727), (3656, 3656, 1299758317658576055), (3657, 3657, 1312755900835161815), (3658, 3658, 1325883459843513433), (3659, 3659, 1339142294441948568), (3660, 3660, 1352533717386368053), (3661, 3661, 1366059054560231734), (3662, 3662, 1379719645105834051), (3663, 3663, 1393516841556892392), (3664, 3664, 1407452009972461316), (3665, 3665, 1421526530072185929), (3666, 3666, 1435741795372907788), (3667, 3667, 1450099213326636866), (3668, 3668, 1464600205459903235), (3669, 3669, 1479246207514502267), (3670, 3670, 1494038669589647290), (3671, 3671, 1508979056285543763), (3672, 3672, 1524068846848399200), (3673, 3673, 1539309535316883192), (3674, 3674, 1554702630670052024), (3675, 3675, 1570249656976752544), (3676, 3676, 1585952153546520070), (3677, 3677, 1601811675081985270), (3678, 3678, 1617829791832805123), (3679, 3679, 1634008089751133174), (3680, 3680, 1650348170648644506), (3681, 3681, 1666851652355130951), (3682, 3682, 1683520168878682261), (3683, 3683, 1700355370567469083), (3684, 3684, 1717358924273143774), (3685, 3685, 1734532513515875212), (3686, 3686, 1751877838651033964), (3687, 3687, 1769396617037544304), (3688, 3688, 1787090583207919747), (3689, 3689, 1804961489039998944), (3690, 3690, 1823011103930398933), (3691, 3691, 1841241214969702923), (3692, 3692, 1859653627119399952), (3693, 3693, 1878250163390593952), (3694, 3694, 1897032665024499891), (3695, 3695, 1916002991674744890), (3696, 3696, 1935163021591492339), (3697, 3697, 1954514651807407262), (3698, 3698, 1974059798325481335), (3699, 3699, 1993800396308736148), (3700, 3700, 2013738400271823510), (3701, 3701, 2033875784274541745), (3702, 3702, 2054214542117287162), (3703, 3703, 2074756687538460034), (3704, 3704, 2095504254413844634), (3705, 3705, 2116459296957983080), (3706, 3706, 2137623889927562911), (3707, 3707, 2159000128826838540), (3708, 3708, 2180590130115106926), (3709, 3709, 2202396031416257995), (3710, 3710, 2224419991730420575), (3711, 3711, 2246664191647724781), (3712, 3712, 2269130833564202029), (3713, 3713, 2291822141899844049), (3714, 3714, 2314740363318842489), (3715, 3715, 2337887766952030914), (3716, 3716, 2361266644621551223), (3717, 3717, 2384879311067766736), (3718, 3718, 2408728104178444403), (3719, 3719, 2432815385220228847), (3720, 3720, 2457143539072431135), (3721, 3721, 2481714974463155447), (3722, 3722, 2506532124207787001), (3723, 3723, 2531597445449864871), (3724, 3724, 2556913419904363520), (3725, 3725, 2582482554103407155), (3726, 3726, 2608307379644441227), (3727, 3727, 2634390453440885639), (3728, 3728, 2660734357975294495), (3729, 3729, 2687341701555047440), (3730, 3730, 2714215118570597915), (3731, 3731, 2741357269756303894), (3732, 3732, 2768770842453866933), (3733, 3733, 2796458550878405602), (3734, 3734, 2824423136387189658), (3735, 3735, 2852667367751061555), (3736, 3736, 2881194041428572170), (3737, 3737, 2910005981842857892), (3738, 3738, 2939106041661286471), (3739, 3739, 2968497102077899335), (3740, 3740, 2998182073098678329), (3741, 3741, 3028163893829665112), (3742, 3742, 3058445532767961763), (3743, 3743, 3089029988095641381), (3744, 3744, 3119920287976597795), (3745, 3745, 3151119490856363773), (3746, 3746, 3182630685764927410), (3747, 3747, 3214456992622576684), (3748, 3748, 3246601562548802451), (3749, 3749, 3279067578174290476), (3750, 3750, 3311858253956033381), (3751, 3751, 3344976836495593714), (3752, 3752, 3378426604860549651), (3753, 3753, 3412210870909155148), (3754, 3754, 3446332979618246699), (3755, 3755, 3480796309414429166), (3756, 3756, 3515604272508573458), (3757, 3757, 3550760315233659193), (3758, 3758, 3586267918385995785), (3759, 3759, 3622130597569855742), (3760, 3760, 3658351903545554300), (3761, 3761, 3694935422581009843), (3762, 3762, 3731884776806819941), (3763, 3763, 3769203624574888141), (3764, 3764, 3806895660820637022), (3765, 3765, 3844964617428843392), (3766, 3766, 3883414263603131826), (3767, 3767, 3922248406239163144), (3768, 3768, 3961470890301554776), (3769, 3769, 4001085599204570324), (3770, 3770, 4041096455196616027), (3771, 3771, 4081507419748582187), (3772, 3772, 4122322493946068009), (3773, 3773, 4163545718885528689), (3774, 3774, 4205181176074383976), (3775, 3775, 4247232987835127816), (3776, 3776, 4289705317713479094), (3777, 3777, 4332602370890613885), (3778, 3778, 4375928394599520024), (3779, 3779, 4419687678545515224), (3780, 3780, 4463884555330970376), (3781, 3781, 4508523400884280080), (3782, 3782, 4553608634893122881), (3783, 3783, 4599144721242054110), (3784, 3784, 4645136168454474651), (3785, 3785, 4691587530139019397), (3786, 3786, 4738503405440409591), (3787, 3787, 4785888439494813687), (3788, 3788, 4833747323889761824), (3789, 3789, 4882084797128659442), (3790, 3790, 4930905645099946036), (3791, 3791, 4980214701550945497), (3792, 3792, 5030016848566454952), (3793, 3793, 5080317017052119501), (3794, 3794, 5131120187222640696), (3795, 3795, 5182431389094867103), (3796, 3796, 5234255702985815774), (3797, 3797, 5286598260015673932), (3798, 3798, 5339464242615830671), (3799, 3799, 5392858885041988978), (3800, 3800, 5446787473892408868), (3801, 3801, 5501255348631332957), (3802, 3802, 5556267902117646286), (3803, 3803, 5611830581138822749), (3804, 3804, 5667948886950210976), (3805, 3805, 5724628375819713086), (3806, 3806, 5781874659577910217), (3807, 3807, 5839693406173689319), (3808, 3808, 5898090340235426212), (3809, 3809, 5957071243637780475), (3810, 3810, 6016641956074158279), (3811, 3811, 6076808375634899862), (3812, 3812, 6137576459391248861), (3813, 3813, 6198952223985161349), (3814, 3814, 6260941746225012963), (3815, 3815, 6323551163687263092), (3816, 3816, 6386786675324135723), (3817, 3817, 6450654542077377081), (3818, 3818, 6515161087498150851), (3819, 3819, 6580312698373132360), (3820, 3820, 6646115825356863683), (3821, 3821, 6712576983610432320), (3822, 3822, 6779702753446536643), (3823, 3823, 6847499780981002010), (3824, 3824, 6915974778790812030), (3825, 3825, 6985134526578720150), (3826, 3826, 7054985871844507352), (3827, 3827, 7125535730562952425), (3828, 3828, 7196791087868581950), (3829, 3829, 7268758998747267769), (3830, 3830, 7341446588734740447), (3831, 3831, 7414861054622087851), (3832, 3832, 7489009665168308730), (3833, 3833, 7563899761819991817), (3834, 3834, 7639538759438191735), (3835, 3835, 7715934147032573652), (3836, 3836, 7793093488502899389), (3837, 3837, 7871024423387928383), (3838, 3838, 7949734667621807667), (3839, 3839, 8029232014298025743), (3840, 3840, 8109524334441006001), (3841, 3841, 8190619577785416061), (3842, 3842, 8272525773563270221), (3843, 3843, 8355251031298902924), (3844, 3844, 8438803541611891953), (3845, 3845, 8523191577028010872), (3846, 3846, 8608423492798290981), (3847, 3847, 8694507727726273891), (3848, 3848, 8781452805003536630), (3849, 3849, 8869267333053571996), (3850, 3850, 8957960006384107716), (3851, 3851, 9047539606447948793), (3852, 3852, 9138015002512428281), (3853, 3853, 9229395152537552564), (3854, 3854, 9321689104062928090), (3855, 3855, 9414905995103557370), (3856, 3856, 9509055055054592944), (3857, 3857, 9604145605605138874), (3858, 3858, 9700187061661190262), (3859, 3859, 9797188932277802165), (3860, 3860, 9895160821600580187), (3861, 3873, 9961241799803157873), (3874, 3874, 9928479281272872189), (3875, 3875, 9830177506210764544), (3876, 3876, 9732849016050261925), (3877, 3877, 9636484174307190024), (3878, 3878, 9541073439908108935), (3879, 3879, 9446607366245652411), (3880, 3880, 9353076600243220209), (3881, 3881, 9260471881428930900), (3882, 3882, 9168784041018743465), (3883, 3883, 9078004001008656896), (3884, 3884, 8988122773275897917), (3885, 3885, 8899131458689007839), (3886, 3886, 8811021246226740434), (3887, 3887, 8723783412105683598), (3888, 3888, 8637409318916518414), (3889, 3889, 8551890414768830113), (3890, 3890, 8467218232444386251), (3891, 3891, 8383384388558798268), (3892, 3892, 8300380582731483434), (3893, 3893, 8218198596763844984), (3894, 3894, 8136830293825589093), (3895, 3895, 8056267617649098112), (3896, 3896, 7976502591731780309), (3897, 3897, 7897527318546317137), (3898, 3898, 7819333978758729839), (3899, 3899, 7741914830454187959), (3900, 3900, 7665262208370483128), (3901, 3901, 7589368523139092206), (3902, 3902, 7514226260533754659), (3903, 3903, 7439827980726489762), (3904, 3904, 7366166317550979962), (3905, 3905, 7293233977773247487), (3906, 3906, 7221023740369551968), (3907, 3907, 7149528455811437592), (3908, 3908, 7078741045357859002), (3909, 3909, 7008654500354315843), (3910, 3910, 6939261881538926578), (3911, 3911, 6870556318355372849), (3912, 3912, 6802531008272646385), (3913, 3913, 6735179216111531074), (3914, 3914, 6668494273377753539), (3915, 3915, 6602469577601736177), (3916, 3916, 6537098591684887304), (3917, 3917, 6472374843252363668), (3918, 3918, 6408291924012241255), (3919, 3919, 6344843489121030946), (3920, 3920, 6282023256555476184), (3921, 3921, 6219825006490570479), (3922, 3922, 6158242580683733148), (3923, 3923, 6097269881865082324), (3924, 3924, 6036900873133744876), (3925, 3925, 5977129577360143441), (3926, 3926, 5917950076594201427), (3927, 3927, 5859356511479407353), (3928, 3928, 5801343080672680548), (3929, 3929, 5743904040269980740), (3930, 3930, 5687033703237604694), (3931, 3931, 5630726438849113558), (3932, 3932, 5574976672127835206), (3933, 3933, 5519778883294886342), (3934, 3934, 5465127607222659745), (3935, 3935, 5411017432893722520), (3936, 3936, 5357443002865071802), (3937, 3937, 5304399012737694853), (3938, 3938, 5251880210631381043), (3939, 3939, 5199881396664733706), (3940, 3940, 5148397422440330402), (3941, 3941, 5097423190534980596), (3942, 3942, 5046953653995030293), (3943, 3943, 4996983815836663656), (3944, 3944, 4947508728551152135), (3945, 3945, 4898523493615002114), (3946, 3946, 4850023261004952588), (3947, 3947, 4802003228717774840), (3948, 3948, 4754458642294826574), (3949, 3949, 4707384794351313440), (3950, 3950, 4660777024110211326), (3951, 3951, 4614630716940803293), (3952, 3952, 4568941303901785439), (3953, 3953, 4523704261288896474), (3954, 3954, 4478915110187026212), (3955, 3955, 4434569416026758626), (3956, 3956, 4390662788145305570), (3957, 3957, 4347190879351787693), (3958, 3958, 4304149385496819498), (3959, 3959, 4261534045046355939), (3960, 3960, 4219340638659758355), (3961, 3961, 4177564988772037976), (3962, 3962, 4136202959180235619), (3963, 3963, 4095250454633896653), (3964, 3964, 4054703420429600646), (3965, 3965, 4014557842009505590), (3966, 3966, 3974809744563866921), (3967, 3967, 3935455192637492001), (3968, 3968, 3896490289740091090), (3969, 3969, 3857911177960486228), (3970, 3970, 3819714037584639830), (3971, 3971, 3781895086717465178), (3972, 3972, 3744450580908381364), (3973, 3973, 3707376812780575608), (3974, 3974, 3670670111663936246), (3975, 3975, 3634326843231620045), (3976, 3976, 3598343409140217867), (3977, 3977, 3562716246673483036), (3978, 3978, 3527441828389587165), (3979, 3979, 3492516661771868480), (3980, 3980, 3457937288883038099), (3981, 3981, 3423700286022809999), (3982, 3982, 3389802263388920791), (3983, 3983, 3356239864741505734), (3984, 3984, 3323009767070797756), (3985, 3985, 3290108680268116590), (3986, 3986, 3257533346800115436), (3987, 3987, 3225280541386252907), (3988, 3988, 3193347070679458324), (3989, 3989, 3161729772949958736), (3990, 3990, 3130425517772236373), (3991, 3991, 3099431205715085517), (3992, 3992, 3068743768034738136), (3993, 3993, 3038360166371027857), (3994, 3994, 3008277392446562235), (3995, 3995, 2978492467768873500), (3996, 3996, 2949002443335518317), (3997, 3997, 2919804399342097344), (3998, 3998, 2890895444893165687), (3999, 3999, 2862272717716005630), (4000, 4000, 2833933383877233297), (4001, 4001, 2805874637502211186), (4002, 4002, 2778093700497238798), (4003, 4003, 2750587822274493859), (4004, 4004, 2723354279479696890), (4005, 4005, 2696390375722472168), (4006, 4006, 2669693441309378385), (4007, 4007, 2643260832979582559), (4008, 4008, 2617089933643151049), (4009, 4009, 2591178152121931731), (4010, 4010, 2565522922893001714), (4011, 4011, 2540121705834655162), (4012, 4012, 2514971985974906101), (4013, 4013, 2490071273242481289), (4014, 4014, 2465417102220278504), (4015, 4015, 2441007031901265845), (4016, 4016, 2416838645446797866), (4017, 4017, 2392909549947324620), (4018, 4018, 2369217376185469921), (4019, 4019, 2345759778401455367), (4020, 4020, 2322534434060846898), (4021, 4021, 2299539043624600889), (4022, 4022, 2276771330321387019), (4023, 4023, 2254229039922165366), (4024, 4024, 2231909940516995412), (4025, 4025, 2209811822294054863), (4026, 4026, 2187932497320846399), (4027, 4027, 2166269799327570692), (4028, 4028, 2144821583492644250), (4029, 4029, 2123585726230340841), (4030, 4030, 2102560124980535486), (4031, 4031, 2081742698000530184), (4032, 4032, 2061131384158940777), (4033, 4033, 2040724142731624531), (4034, 4034, 2020518953199628249), (4035, 4035, 2000513815049136880), (4036, 4036, 1980706747573402852), (4037, 4037, 1961095789676636487), (4038, 4038, 1941678999679838106), (4039, 4039, 1922454455128552580), (4040, 4040, 1903420252602527307), (4041, 4041, 1884574507527254759), (4042, 4042, 1865915353987380950), (4043, 4043, 1847440944541961336), (4044, 4044, 1829149450041545878), (4045, 4045, 1811039059447075126), (4046, 4046, 1793107979650569432), (4047, 4047, 1775354435297593497), (4048, 4048, 1757776668611478710), (4049, 4049, 1740372939219285851), (4050, 4050, 1723141523979490942), (4051, 4051, 1706080716811377170), (4052, 4052, 1689188828526116010), (4053, 4053, 1672464186659520802), (4054, 4054, 1655905135306456240), (4055, 4055, 1639510034956887366), (4056, 4056, 1623277262333551848), (4057, 4057, 1607205210231239453), (4058, 4058, 1591292287357662825), (4059, 4059, 1575536918175903787), (4060, 4060, 1559937542748419591), (4061, 4061, 1544492616582593655), (4062, 4062, 1529200610477815500), (4063, 4063, 1514060010374074752), (4064, 4064, 1499069317202054210), (4065, 4065, 1484227046734707139), (4066, 4066, 1469531729440304098), (4067, 4067, 1454981910336934750), (4068, 4068, 1440576148848450248), (4069, 4069, 1426313018661831928), (4070, 4070, 1412191107585972206), (4071, 4071, 1398209017411853670), (4072, 4072, 1384365363774112544), (4073, 4073, 1370658776013972816), (4074, 4074, 1357087897043537442), (4075, 4075, 1343651383211423210), (4076, 4076, 1330347904169725950), (4077, 4077, 1317176142742302921), (4078, 4078, 1304134794794359328), (4079, 4079, 1291222569103326067), (4080, 4080, 1278438187231015908), (4081, 4081, 1265780383397045453), (4082, 4082, 1253247904353510350), (4083, 4083, 1240839509260901336), (4084, 4084, 1228553969565248848), (4085, 4085, 1216390068876484008), (4086, 4086, 1204346602848003968), (4087, 4087, 1192422379057429672), (4088, 4088, 1180616216888544229), (4089, 4089, 1168926947414400227), (4090, 4090, 1157353413281584383), (4091, 4091, 1145894468595628102), (4092, 4092, 1134548978807552576), (4093, 4093, 1123315820601537204), (4094, 4094, 1112193881783700202), (4095, 4095, 1101182061171980398), (4096, 4096, 1090279268487109305), (4097, 4097, 1079484424244662679), (4098, 4098, 1068796459648180870), (4099, 4099, 1058214316483347396), (4100, 4100, 1047736947013215243), (4101, 4101, 1037363313874470538), (4102, 4102, 1027092389974723305), (4103, 4103, 1016923158390815153), (4104, 4104, 1006854612268133815), (4105, 4105, 996885754720924570), (4106, 4106, 987015598733588683), (4107, 4107, 977243167062959092), (4108, 4108, 967567492141543655), (4109, 4109, 957987615981726391), (4110, 4110, 948502590080917219), (4111, 4111, 939111475327640811), (4112, 4112, 929813341908555259), (4113, 4113, 920607269216391345), (4114, 4114, 911492345758803312), (4115, 4115, 902467669068122091), (4116, 4116, 893532345612002070), (4117, 4117, 884685490704952545), (4118, 4118, 875926228420745094), (4119, 4119, 867253691505688212), (4120, 4120, 858667021292760606), (4121, 4121, 850165367616594659), (4122, 4122, 841747888729301643), (4123, 4123, 833413751217130339), (4124, 4124, 825162129917950831), (4125, 4125, 816992207839555278), (4126, 4126, 808903176078767602), (4127, 4127, 800894233741354062), (4128, 4128, 792964587862726794), (4129, 4129, 785113453329432469), (4130, 4130, 777340052801418286), (4131, 4131, 769643616635067610), (4132, 4132, 762023382806997634), (4133, 4133, 754478596838611519), (4134, 4134, 747008511721397543), (4135, 4135, 739612387842967865), (4136, 4136, 732289492913829569), (4137, 4137, 725039101894880761), (4138, 4138, 717860496925624516), (4139, 4139, 710752967253093580), (4140, 4140, 703715809161478792), (4141, 4141, 696748325902454250), (4142, 4142, 689849827626192327), (4143, 4143, 683019631313061710), (4144, 4144, 676257060706001693), (4145, 4145, 669561446243566032), (4146, 4146, 662932124993629735), (4147, 4147, 656368440587752213), (4148, 4148, 649869743156190310), (4149, 4149, 643435389263554762), (4150, 4150, 637064741845103725), (4151, 4151, 630757170143667054), (4152, 4152, 624512049647195103), (4153, 4153, 618328762026925845), (4154, 4154, 612206695076164203), (4155, 4155, 606145242649667528), (4156, 4156, 600143804603631215), (4157, 4157, 594201786736268530), (4158, 4158, 588318600728978743), (4159, 4159, 582493664088097765), (4160, 4160, 576726400087225510), (4161, 4161, 571016237710124267), (4162, 4162, 565362611594182443), (4163, 4163, 559764961974438062), (4164, 4164, 554222734628156497), (4165, 4165, 548735380819956928), (4166, 4166, 543302357247482107), (4167, 4167, 537923125987606047), (4168, 4168, 532597154443174303), (4169, 4169, 527323915290271588), (4170, 4170, 522102886426011473), (4171, 4171, 516933550916843042), (4172, 4172, 511815396947369349), (4173, 4173, 506747917769672623), (4174, 4174, 501730611653141211), (4175, 4175, 496762981834793278), (4176, 4176, 491844536470092354), (4177, 4177, 486974788584249856), (4178, 4178, 482153256024009758), (4179, 4179, 477379461409910652), (4180, 4180, 472652932089020447), (4181, 4181, 467973200088139057), (4182, 4182, 463339802067464413), (4183, 4183, 458752279274717240), (4184, 4184, 454210177499720040), (4185, 4185, 449713047029425782), (4186, 4186, 445260442603391863), (4187, 4187, 440851923369694914), (4188, 4188, 436487052841282093), (4189, 4189, 432165398852754548), (4190, 4190, 427886533517578760), (4191, 4191, 423650033185721545), (4192, 4192, 419455478401704500), (4193, 4193, 415302453863073762), (4194, 4194, 411190548379280953), (4195, 4195, 407119354830971240), (4196, 4196, 403088470129674495), (4197, 4197, 399097495177895540), (4198, 4198, 395146034829599544), (4199, 4199, 391233697851088658), (4200, 4200, 387360096882265998), (4201, 4201, 383524848398283166), (4202, 4202, 379727572671567491), (4203, 4203, 375967893734225239), (4204, 4204, 372245439340817068), (4205, 4205, 368559840931502048), (4206, 4206, 364910733595546582), (4207, 4207, 361297756035194636), (4208, 4208, 357720550529895679), (4209, 4209, 354178762900886811), (4210, 4210, 350672042476125555), (4211, 4211, 347200042055569857), (4212, 4212, 343762417876801838), (4213, 4213, 340358829580991919), (4214, 4214, 336988940179199920), (4215, 4215, 333652416019009822), (4216, 4216, 330348926751494873), (4217, 4217, 327078145298509775), (4218, 4218, 323839747820306708), (4219, 4219, 320633413683471988), (4220, 4220, 317458825429180186), (4221, 4221, 314315668741762561), (4222, 4222, 311203632417586694), (4223, 4223, 308122408334244251), (4224, 4224, 305071691420043813), (4225, 4225, 302051179623805756), (4226, 4226, 299060573884956194), (4227, 4227, 296099578103917023), (4228, 4228, 293167899112789132), (4229, 4229, 290265246646325873), (4230, 4230, 287391333313193934), (4231, 4231, 284545874567518747), (4232, 4232, 281728588680711630), (4233, 4233, 278939196713575872), (4234, 4234, 276177422488688982), (4235, 4235, 273442992563058398), (4236, 4236, 270735636201047919), (4237, 4237, 268055085347572197), (4238, 4238, 265401074601556630), (4239, 4239, 262773341189660030), (4240, 4240, 260171624940257456), (4241, 4241, 257595668257680649), (4242, 4242, 255045216096713514), (4243, 4243, 252520015937340113), (4244, 4244, 250019817759742686), (4245, 4245, 247544374019547214), (4246, 4246, 245093439623314073), (4247, 4247, 242666771904271360), (4248, 4248, 240264130598288475), (4249, 4249, 237885277820087599), (4250, 4250, 235529978039690692), (4251, 4251, 233197998059099695), (4252, 4252, 230889106989207619), (4253, 4253, 228603076226938236), (4254, 4254, 226339679432612115), (4255, 4255, 224098692507536748), (4256, 4256, 221879893571818562), (4257, 4257, 219683062942394616), (4258, 4258, 217507983111281798), (4259, 4259, 215354438724041384), (4260, 4260, 213222216558456816), (4261, 4261, 211111105503422590), (4262, 4262, 209020896538042168), (4263, 4263, 206951382710932840), (4264, 4264, 204902359119735485), (4265, 4265, 202873622890827213), (4266, 4266, 200864973159234864), (4267, 4267, 198876211048747391), (4268, 4268, 196907139652225139), (4269, 4269, 194957564012104098), (4270, 4270, 193027291101093167), (4271, 4271, 191116129803062541), (4272, 4272, 189223890894121328), (4273, 4273, 187350387023882503), (4274, 4274, 185495432696913369), (4275, 4275, 183658844254369672), (4276, 4276, 181840439855811557), (4277, 4277, 180040039461199561), (4278, 4278, 178257464813068873), (4279, 4279, 176492539418880072), (4280, 4280, 174745088533544626), (4281, 4281, 173014939142123392), (4282, 4282, 171301919942696427), (4283, 4283, 169605861329402403), (4284, 4284, 167926595375645944), (4285, 4285, 166263955817471232), (4286, 4286, 164617778037100229), (4287, 4287, 162987899046633890), (4288, 4288, 161374157471914743), (4289, 4289, 159776393536549250), (4290, 4290, 158194449046088367), (4291, 4291, 156628167372364720), (4292, 4292, 155077393437984871), (4293, 4293, 153541973700975120), (4294, 4294, 152021756139579326), (4295, 4295, 150516590237207254), (4296, 4296, 149026326967531935), (4297, 4297, 147550818779734589), (4298, 4298, 146089919583895632), (4299, 4299, 144643484736530329), (4300, 4300, 143211371026267653), (4301, 4301, 141793436659670943), (4302, 4302, 140389541247198954), (4303, 4303, 138999545789305895), (4304, 4304, 137623312662679104), (4305, 4305, 136260705606612974), (4306, 4306, 134911589709517796), (4307, 4307, 133575831395562174), (4308, 4308, 132253298411447697), (4309, 4309, 130943859813314552), (4310, 4310, 129647385953776784), (4311, 4311, 128363748469085925), (4312, 4312, 127092820266421708), (4313, 4313, 125834475511308621), (4314, 4314, 124588589615157051), (4315, 4315, 123355039222927773), (4316, 4316, 122133702200918587), (4317, 4317, 120924457624671869), (4318, 4318, 119727185767001850), (4319, 4319, 118541768086140446), (4320, 4320, 117368087214000441), (4321, 4321, 116206026944554892), (4322, 4322, 115055472222331577), (4323, 4323, 113916309131021363), (4324, 4324, 112788424882199369), (4325, 4325, 111671707804157791), (4326, 4326, 110566047330849298), (4327, 4327, 109471333990939899), (4328, 4328, 108387459396970197), (4329, 4329, 107314316234623958), (4330, 4330, 106251798252102929), (4331, 4331, 105199800249606860), (4332, 4332, 104158218068917683), (4333, 4333, 103126948583086815), (4334, 4334, 102105889686224569), (4335, 4335, 101094940283390663), (4336, 4336, 100094000280584815), (4337, 4337, 99102970574836450), (4338, 4338, 98121753044392525), (4339, 4339, 97150250539002500), (4340, 4340, 96188366870299505), (4341, 4341, 95236006802276737), (4342, 4342, 94293076041858156), (4343, 4343, 93359481229562531), (4344, 4344, 92435129930259931), (4345, 4345, 91519930624019734), (4346, 4346, 90613792697049242), (4347, 4347, 89716626432722021), (4348, 7209, 88828343002695071)]

def glob1 : ℕ := 9961241799803157873

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3860, 0), (3861, 3873, 34160637173536206697), (3874, 3874, 34048282857588724928), (3875, 3875, 33711171146127450424), (3876, 3876, 33377397174383614281), (3877, 3877, 33046927895429321070), (3878, 3878, 32719730589533981258), (3879, 3879, 32395772860924733919), (3880, 3880, 32075022634578944474), (3881, 3881, 31757448153048459875), (3882, 3882, 31443017973315306807), (3883, 3883, 31131700963678521591), (3884, 3884, 30823466300671803556), (3885, 3885, 30518283466011686689), (3886, 3886, 30216122243575927414), (3887, 3887, 29916952716411809321), (3888, 3888, 29620745263774068635), (3889, 3889, 29327470558192147163), (3890, 3890, 29037099562566482340), (3891, 3891, 28749603527293546871), (3892, 3892, 28464953987419353338), (3893, 3893, 28183122759821141919), (3894, 3894, 27904081940416972197), (3895, 3895, 27627803901402942769), (3896, 3896, 27354261288517765118), (3897, 3897, 27083427018334420909), (3898, 3898, 26815274275578634563), (3899, 3899, 26549776510473895607), (3900, 3900, 26286907436112767928), (3901, 3901, 26026641025854225671), (3902, 3902, 25768951510746758090), (3903, 3903, 25513813376976988208), (3904, 3904, 25261201363343552681), (3905, 3905, 25011090458755992754), (3906, 3906, 24763455899758408667), (3907, 3907, 24518273168077632344), (3908, 3908, 24275517988195675588), (3909, 3909, 24035166324946213453), (3910, 3910, 23797194381134864805), (3911, 3911, 23561578595183034461), (3912, 3912, 23328295638795083624), (3913, 3913, 23097322414648597648), (3914, 3914, 22868636054107522424), (3915, 3915, 22642213914957942994), (3916, 3916, 22418033579166280192), (3917, 3917, 22196072850659683358), (3918, 3918, 21976309753128399365), (3919, 3919, 21758722527849900361), (3920, 3920, 21543289631534554813), (3921, 3921, 21329989734192628528), (3922, 3922, 21118801717022404483), (3923, 3923, 20909704670319212359), (3924, 3924, 20702677891405160752), (3925, 3925, 20497700882579367081), (3926, 3926, 20294753349088482258), (3927, 3927, 20093815197117309167), (3928, 3928, 19894866531799316007), (3929, 3929, 19697887655246847531), (3930, 3930, 19502859064600839140), (3931, 3931, 19309761450099840733), (3932, 3932, 19118575693168159141), (3933, 3933, 18929282864522929843), (3934, 3934, 18741864222299930537), (3935, 3935, 18556301210197951027), (3936, 3936, 18372575455641535670), (3937, 3937, 18190668767961916505), (3938, 3938, 18010563136595956936), (3939, 3939, 17832240729302927659), (3940, 3940, 17655683890398938277), (3941, 3941, 17480875139008849779), (3942, 3942, 17307797167335494831), (3943, 3943, 17136432838946034486), (3944, 3944, 16966765187075281669), (3945, 3945, 16798777412945823435), (3946, 3946, 16632452884104775678), (3947, 3947, 16467775132777005622), (3948, 3948, 16304727854234659031), (3949, 3949, 16143294905182830724), (3950, 3950, 15983460302161218539), (3951, 3951, 15825208219961602514), (3952, 3952, 15668522990060992588), (3953, 3953, 15513389099070289691), (3954, 3954, 15359791187198306625), (3955, 3955, 15207714046730996658), (3956, 3956, 15057142620525739265), (3957, 3957, 14908062000520533926), (3958, 3958, 14760457426257954382), (3959, 3959, 14614314283423717210), (3960, 3960, 14469618102399720010), (3961, 3961, 14326354556831405951), (3962, 3962, 14184509462209312822), (3963, 3963, 14044068774464666161), (3964, 3964, 13905018588578877387), (3965, 3965, 13767345137206809294), (3966, 3966, 13631034789313672568), (3967, 3967, 13496074048825418384), (3968, 3968, 13362449553292493450), (3969, 3969, 13230148072566825198), (3970, 3970, 13099156507491906137), (3971, 3971, 12969461888605847660), (3972, 3972, 12841051374857274911), (3973, 3973, 12713912252333935555), (3974, 3974, 12588031933003896590), (3975, 3975, 12463397953469204544), (3976, 3976, 12339997973731885687), (3977, 3977, 12217819775972164047), (3978, 3978, 12096851263338776284), (3979, 3979, 11977080458751263647), (3980, 3980, 11858495503714122423), (3981, 3981, 11741084657142695469), (3982, 3982, 11624836294200688583), (3983, 3983, 11509738905149196617), (3984, 3984, 11395781094207125363), (3985, 3985, 11282951578422896399), (3986, 3986, 11171239186557323167), (3987, 3987, 11060632857977547690), (3988, 3988, 10951121641561928406), (3989, 3989, 10842694694615770699), (3990, 3990, 10735341281797792772), (3991, 3991, 10629050774057220566), (3992, 3992, 10523812647581406501), (3993, 3993, 10419616482753867823), (3994, 3994, 10316451963122641409), (3995, 3995, 10214308874378852880), (3996, 3996, 10113177103345398891), (3997, 3997, 10013046636975642466), (3998, 3998, 9913907561362022244), (3999, 3999, 9815750060754477469), (4000, 4000, 9718564416588591554), (4001, 4001, 9622341006523357974), (4002, 4002, 9527070303488473242), (4003, 4003, 9432742874741062615), (4004, 4004, 9339349380931745164), (4005, 4005, 9246880575179945707), (4006, 4006, 9155327302158362086), (4007, 4007, 9064680497186497115), (4008, 4008, 8974931185333165460), (4009, 4009, 8886070480527886594), (4010, 4010, 8798089584681075836), (4011, 4011, 8710979786812946372), (4012, 4012, 8624732462191036012), (4013, 4013, 8539339071476273279), (4014, 4014, 8454791159877498296), (4015, 4015, 8371080356314354749), (4016, 4016, 8288198372588470048), (4017, 4017, 8206137002562841632), (4018, 4018, 8124888121349348150), (4019, 4019, 8044443684504305099), (4020, 4020, 7964795727231985247), (4021, 4021, 7885936363596024997), (4022, 4022, 7807857785738638611), (4023, 4023, 7730552263107562981), (4024, 4024, 7654012141690656417), (4025, 4025, 7578229843258075660), (4026, 4026, 7503197864611956099), (4027, 4027, 7428908776843520890), (4028, 4028, 7355355224597545436), (4029, 4029, 7282529925344104392), (4030, 4030, 7210425668657529101), (4031, 4031, 7139035315502504061), (4032, 4032, 7068351797527231743), (4033, 4033, 6998368116363595785), (4034, 4034, 6929077342934253253), (4035, 4035, 6860472616766587379), (4036, 4036, 6792547145313452850), (4037, 4037, 6725294203280646387), (4038, 4038, 6658707131961036026), (4039, 4039, 6592779338575283194), (4040, 4040, 6527504295619092272), (4041, 4041, 6462875540216923041), (4042, 4042, 6398886673482102021), (4043, 4043, 6335531359883269328), (4044, 4044, 6272803326617098344), (4045, 4045, 6210696362987226084), (4046, 4046, 6149204319789332756), (4047, 4047, 6088321108702309659), (4048, 4048, 6028040701685455108), (4049, 4049, 5968357130381638721), (4050, 4050, 5909264485526374971), (4051, 4051, 5850756916362747496), (4052, 4052, 5792828630062126234), (4053, 4053, 5735473891150620034), (4054, 4054, 5678687020941207954), (4055, 4055, 5622462396971493024), (4056, 4056, 5566794452447022796), (4057, 4057, 5511677675690121580), (4058, 4058, 5457106609594179782), (4059, 4059, 5403075851083346319), (4060, 4060, 5349580050577570613), (4061, 4061, 5296613911462941201), (4062, 4062, 5244172189567268516), (4063, 4063, 5192249692640859917), (4064, 4064, 5140841279842435561), (4065, 4065, 5089941861230134219), (4066, 4066, 5039546397257558633), (4067, 4067, 4989649898274810527), (4068, 4068, 4940247424034465869), (4069, 4069, 4891334083202441454), (4070, 4070, 4842905032873704410), (4071, 4071, 4794955478092776644), (4072, 4072, 4747480671378986776), (4073, 4073, 4700475912256422550), (4074, 4074, 4653936546788537179), (4075, 4075, 4607857967117363543), (4076, 4076, 4562235611007290637), (4077, 4077, 4517064961393357066), (4078, 4078, 4472341545934016897), (4079, 4079, 4428060936568333562), (4080, 4080, 4384218749077557982), (4081, 4081, 4340810642651047507), (4082, 4082, 4297832319456482680), (4083, 4083, 4255279524214339287), (4084, 4084, 4213148043776573552), (4085, 4085, 4171433706709478764), (4086, 4086, 4130132382880672044), (4087, 4087, 4089239983050170340), (4088, 4088, 4048752458465515188), (4089, 4089, 4008665800460906127), (4090, 4090, 3968976040060303096), (4091, 4091, 3929679247584458511), (4092, 4092, 3890771532261840110), (4093, 4093, 3852249041843406049), (4094, 4094, 3814107962221194108), (4095, 4095, 3776344517050687236), (4096, 4096, 3738954967376918055), (4097, 4097, 3701935611264275302), (4098, 4098, 3665282783429975547), (4099, 4099, 3628992854881163908), (4100, 4100, 3593062232555607830), (4101, 4101, 3557487358965948346), (4102, 4102, 3522264711847473610), (4103, 4103, 3487390803809379812), (4104, 4104, 3452862181989484962), (4105, 4105, 3418675427712361349), (4106, 4106, 3384827156150852821), (4107, 4107, 3351314015990943387), (4108, 4108, 3318132689099943947), (4109, 4109, 3285279890197964304), (4110, 4110, 3252752366532637925), (4111, 4111, 3220546897557067252), (4112, 4112, 3188660294610957676), (4113, 4113, 3157089400604908590), (4114, 4114, 3125831089707830287), (4115, 4115, 3094882267037455730), (4116, 4116, 3064239868353916564), (4117, 4117, 3033900859756353034), (4118, 4118, 3003862237382527756), (4119, 4119, 2974121027111413620), (4120, 4120, 2944674284268726356), (4121, 4121, 2915519093335372630), (4122, 4122, 2886652567658784782), (4123, 4123, 2858071849167113646), (4124, 4124, 2829774108086251134), (4125, 4125, 2801756542659654589), (4126, 4126, 2774016378870945137), (4127, 4127, 2746550870169252611), (4128, 4128, 2719357297197279813), (4129, 4129, 2692432967522059221), (4130, 4130, 2665775215368375466), (4131, 4131, 2639381401354827194), (4132, 4132, 2613248912232502172), (4133, 4133, 2587375160626239775), (4134, 4134, 2561757584778455222), (4135, 4135, 2536393648295500220), (4136, 4136, 2511280839896534872), (4137, 4137, 2486416673164886011), (4138, 4138, 2461798686301867338), (4139, 4139, 2437424441883036968), (4140, 4140, 2413291526616868286), (4141, 4141, 2389397551105810184), (4142, 4142, 2365740149609713053), (4143, 4143, 2342316979811597082), (4144, 4144, 2319125722585739686), (4145, 4145, 2296164081768059095), (4146, 4146, 2273429783928771381), (4147, 4147, 2250920578147298397), (4148, 4148, 2228634235789404353), (4149, 4149, 2206568550286538964), (4150, 4150, 2184721336917365311), (4151, 4151, 2163090432591450803), (4152, 4152, 2141673695635099805), (4153, 4153, 2120469005579306737), (4154, 4154, 2099474262949808651), (4155, 4155, 2078687389059216486), (4156, 4156, 2058106325801204441), (4157, 4157, 2037729035446737071), (4158, 4158, 2017553500442313931), (4159, 4159, 1997577723210211813), (4160, 4160, 1977799725950704766), (4161, 4161, 1958217550446242342), (4162, 4162, 1938829257867566675), (4163, 4163, 1919632928581749184), (4164, 4164, 1900626661962127905), (4165, 4165, 1881808576200126638), (4166, 4166, 1863176808118937266), (4167, 4167, 1844729512989046798), (4168, 4168, 1826464864345590889), (4169, 4169, 1808381053807515731), (4170, 4170, 1790476290898530427), (4171, 4171, 1772748802869832106), (4172, 4172, 1755196834524586244), (4173, 4173, 1737818648044144796), (4174, 4174, 1720612522815984946), (4175, 4175, 1703576755263351432), (4176, 4176, 1686709658676585576), (4177, 4177, 1670009563046124333), (4178, 4178, 1653474814897152805), (4179, 4179, 1637103777125893866), (4180, 4180, 1620894828837518679), (4181, 4181, 1604846365185662059), (4182, 4182, 1588956797213526791), (4183, 4183, 1573224551696561179), (4184, 4184, 1557648070986694237), (4185, 4185, 1542225812858113106), (4186, 4186, 1526956250354567431), (4187, 4187, 1511837871638185576), (4188, 4188, 1496869179839787699), (4189, 4189, 1482048692910680890), (4190, 4190, 1467374943475921673), (4191, 4191, 1452846478689031359), (4192, 4192, 1438461860088149861), (4193, 4193, 1424219663453613724), (4194, 4194, 1410118478666944281), (4195, 4195, 1396156909571231961), (4196, 4196, 1382333573832902932), (4197, 4197, 1368647102804854388), (4198, 4198, 1355096141390944939), (4199, 4199, 1341679347911826672), (4200, 4200, 1328395393972105616), (4201, 4201, 1315242964328817441), (4202, 4202, 1302220756761205387), (4203, 4203, 1289327481941787512), (4204, 4204, 1276561863308700507), (4205, 4205, 1263922636939307433), (4206, 4206, 1251408551425056864), (4207, 4207, 1239018367747581054), (4208, 4208, 1226750859156020845), (4209, 4209, 1214604811045565193), (4210, 4210, 1202579020837193261), (4211, 4211, 1190672297858607189), (4212, 4212, 1178883463226343751), (4213, 4213, 1167211349729053219), (4214, 4214, 1155654801711933880), (4215, 4215, 1144212674962310773), (4216, 4216, 1132883836596347300), (4217, 4217, 1121667164946878515), (4218, 4218, 1110561549452354965), (4219, 4219, 1099565890546886104), (4220, 4220, 1088679099551372380), (4221, 4221, 1077900098565715228), (4222, 4222, 1067227820362094285), (4223, 4223, 1056661208279301272), (4224, 4224, 1046199216118120072), (4225, 4225, 1035840808037742645), (4226, 4226, 1025584958453210540), (4227, 4227, 1015430651933871821), (4228, 4228, 1005376883102843388), (4229, 4229, 995422656537468701), (4230, 4230, 985566986670761090), (4231, 4231, 975808897693822861), (4232, 4232, 966147423459230556), (4233, 4233, 956581607385376788), (4234, 4234, 947110502361759196), (4235, 4235, 937733170655207124), (4236, 4236, 928448683817036757), (4237, 4237, 919256122591125502), (4238, 4238, 910154576822896537), (4239, 4239, 901143145369204492), (4240, 4240, 892220936009113358), (4241, 4241, 883387065355557780), (4242, 4242, 874640658767878990), (4243, 4243, 865980850265226723), (4244, 4244, 857406782440818538), (4245, 4245, 848917606377048057), (4246, 4246, 840512481561433720), (4247, 4247, 832190575803399723), (4248, 4248, 823951065151880914), (4249, 4249, 815793133813743479), (4250, 4250, 807715974073013345), (4251, 4251, 799718786210904302), (4252, 4252, 791800778426637923), (4253, 4253, 783961166759047449), (4254, 4254, 776199175008957870), (4255, 4255, 768514034662334525), (4256, 4256, 760904984814192599), (4257, 4257, 753371272093259999), (4258, 4258, 745912150587386137), (4259, 4259, 738526881769689245), (4260, 4260, 731214734425434896), (4261, 4261, 723974984579638511), (4262, 4262, 716806915425384664), (4263, 4263, 709709817252856103), (4264, 4264, 702682987379065449), (4265, 4265, 695725730078282623), (4266, 4266, 688837356513151111), (4267, 4267, 682017184666486249), (4268, 4268, 675264539273748761), (4269, 4269, 668578751756186892), (4270, 4270, 661959160154640488), (4271, 4271, 655405109064000483), (4272, 4272, 648915949568317310), (4273, 4273, 642491039176551792), (4274, 4274, 636129741758962170), (4275, 4275, 629831427484120960), (4276, 4276, 623595472756555406), (4277, 4277, 617421260155005353), (4278, 4278, 611308178371292429), (4279, 4279, 605255622149794484), (4280, 4280, 599262992227519291), (4281, 4281, 593329695274771575), (4282, 4282, 587455143836407500), (4283, 4283, 581638756273670792), (4284, 4284, 575879956706604745), (4285, 4285, 570178174957034401), (4286, 4286, 564532846492113268), (4287, 4287, 558943412368428978), (4288, 4288, 553409319176662355), (4289, 4289, 547930018986794411), (4290, 4290, 542504969293855852), (4291, 4291, 537133632964213715), (4292, 4292, 531815478182389817), (4293, 4293, 526549978398405759), (4294, 4294, 521336612275649267), (4295, 4295, 516174863639256700), (4296, 4296, 511064221425006633), (4297, 4297, 506004179628719439), (4298, 4298, 500994237256157860), (4299, 4299, 496033898273423624), (4300, 4300, 491122671557845172), (4301, 4301, 486260070849351656), (4302, 4302, 481445614702328372), (4303, 4303, 476678826437948883), (4304, 4304, 471959234096979092), (4305, 4305, 467286370393048606), (4306, 4306, 462659772666384759), (4307, 4307, 458078982838004712), (4308, 4308, 453543547364361101), (4309, 4309, 449053017192436733), (4310, 4310, 444606947715283894), (4311, 4311, 440204898728003856), (4312, 4312, 435846434384162233), (4313, 4313, 431531123152635875), (4314, 4314, 427258537774887005), (4315, 4315, 423028255222660401), (4316, 4316, 418839856656099407), (4317, 4317, 414692927382276640), (4318, 4318, 410587056814135287), (4319, 4319, 406521838429836918), (4320, 4320, 402496869732511800), (4321, 4321, 398511752210407723), (4322, 4322, 394566091297433389), (4323, 4323, 390659496334092464), (4324, 4324, 386791580528804420), (4325, 4325, 382961960919608337), (4326, 4326, 379170258336245878), (4327, 4327, 375416097362619681), (4328, 4328, 371699106299623447), (4329, 4329, 368018917128340046), (4330, 4330, 364375165473604006), (4331, 4331, 360767490567924759), (4332, 4332, 357195535215767088), (4333, 4333, 353658945758185235), (4334, 4334, 350157372037807164), (4335, 4335, 346690467364165509), (4336, 4336, 343257888479371791), (4337, 4337, 339859295524130486), (4338, 4338, 336494352004089590), (4339, 4339, 333162724756524347), (4340, 4340, 329864083917350838), (4341, 4341, 326598102888466176), (4342, 4342, 323364458305412056), (4343, 4343, 320162830005358471), (4344, 4344, 316992900995404427), (4345, 4345, 313854357421192502), (4346, 4346, 310746888535834160), (4347, 4347, 307670186669142733), (4348, 7209, 304623947197171023)]

def glob2 : ℕ := 34160637173536206697

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3860, 0), (3861, 3861, 60671330611640156), (3862, 3862, 242711654800728388), (3863, 3863, 422949599542399905), (3864, 3864, 601403010177718239), (3865, 3865, 778089555361201738), (3866, 3866, 953026728810195301), (3867, 3867, 1126231851036921601), (3868, 3868, 1297722071063383284), (3869, 3869, 1467514368119285941), (3870, 3870, 1635625553323149958), (3871, 3871, 1802072271346777697), (3872, 3872, 1966871002063240805), (3873, 3873, 2130038062178550813), (3874, 3874, 2291589606847174583), (3875, 3875, 2451541631271554554), (3876, 3876, 2609909972285792149), (3877, 3877, 2766710309923651153), (3878, 3878, 2921958168971036306), (3879, 3879, 3075668920503100814), (3880, 3880, 3227857783406134981), (3881, 3881, 3378539825884386631), (3882, 3882, 3527729966951962522), (3883, 3883, 3675442977909958453), (3884, 3884, 3821693483808964326), (3885, 3885, 3966495964897088953), (3886, 3886, 4109864758053647989), (3887, 3887, 4251814058208656936), (3888, 3888, 4392357919748269754), (3889, 3889, 4531510257906302248), (3890, 3890, 4669284850141977984), (3891, 3891, 4805695337504033169), (3892, 3892, 4940755225981315530), (3893, 3893, 5074477887840010937), (3894, 3894, 5206876562947630151), (3895, 3895, 5337964360083886799), (3896, 3896, 5467754258238596352), (3897, 3897, 5596259107896724622), (3898, 3898, 5723491632310713008), (3899, 3899, 5849464428760206460), (3900, 3900, 5974189969799308887), (3901, 3901, 6097680604491489508), (3902, 3902, 6219948559632262400), (3903, 3903, 6341005940959760313), (3904, 3904, 6460864734353322603), (3905, 3905, 6579536807020215960), (3906, 3906, 6697033908670605422), (3907, 3907, 6813367672680892018), (3908, 3908, 6928549617245532212), (3909, 3909, 7042591146517453196), (3910, 3910, 7155503551737176943), (3911, 3911, 7267298012350764811), (3912, 3912, 7377985597116693393), (3913, 3913, 7487577265201771197), (3914, 3914, 7596083867266204667), (3915, 3915, 7703516146537920973), (3916, 3916, 7809884739876253950), (3917, 3917, 7915200178825098481), (3918, 3918, 8019472890655637621), (3919, 3919, 8122713199398745681), (3920, 3920, 8224931326867169502), (3921, 3921, 8326137393667589127), (3922, 3922, 8426341420202658062), (3923, 3923, 8525553327663122355), (3924, 3924, 8623782939010116704), (3925, 3925, 8721039979947734871), (3926, 3926, 8817334079885970681), (3927, 3927, 8912674772894124947), (3928, 3928, 9007071498644772736), (3929, 3929, 9100533603348384408), (3930, 3930, 9193070340678692994), (3931, 3931, 9284690872688899515), (3932, 3932, 9375404270718806962), (3933, 3933, 9465219516292972751), (3934, 3934, 9554145502009968581), (3935, 3935, 9642191032422835740), (3936, 3936, 9729364824910823026), (3937, 3937, 9815675510542493606), (3938, 3938, 9901131634930286259), (3939, 3939, 9985741659076615619), (3940, 3940, 10069513960211595184), (3941, 3941, 10152456832622466039), (3942, 3942, 10234578488474813421), (3943, 3943, 10315887058625652413), (3944, 3944, 10396390593428463297), (3945, 3945, 10476097063530256250), (3946, 3946, 10555014360660744323), (3947, 3947, 10633150298413702811), (3948, 3948, 10710512613020592403), (3949, 3949, 10787108964116522693), (3950, 3950, 10862946935498631890), (3951, 3951, 10938034035876957828), (3952, 3952, 11012377699617874598), (3953, 3953, 11085985287480168430), (3954, 3954, 11158864087343825689), (3955, 3955, 11231021314931605154), (3956, 3956, 11302464114523466010), (3957, 3957, 11373199559663922303), (3958, 3958, 11443234653862393880), (3959, 3959, 11512576331286623165), (3960, 3960, 11581231457449226417), (3961, 3961, 11649206829887447458), (3962, 3962, 11716509178836181163), (3963, 3963, 11783145167894333346), (3964, 3964, 11849121394684583032), (3965, 3965, 11914444391506612423), (3966, 3966, 11979120625983869247), (3967, 3967, 12043156501703925508), (3968, 3968, 12106558358852496064), (3969, 3969, 12169332474841179782), (3970, 3970, 12231485064928985444), (3971, 3971, 12293022282837703921), (3972, 3972, 12353950221361187561), (3973, 3973, 12414274912968597106), (3974, 3974, 12474002330401675864), (3975, 3975, 12533138387266110277), (3976, 3976, 12591688938617035439), (3977, 3977, 12649659781538743520), (3978, 3978, 12707056655718652511), (3979, 3979, 12763885244015592106), (3980, 3980, 12820151173022462992), (3981, 3981, 12875860013623325256), (3982, 3982, 12931017281544971062), (3983, 3983, 12985628437903036216), (3984, 3984, 13039698889742704685), (3985, 3985, 13093233990574059605), (3986, 3986, 13146239040902133783), (3987, 3987, 13198719288751712178), (3988, 3988, 13250679930186938311), (3989, 3989, 13302126109825776066), (3990, 3990, 13353062921349377804), (3991, 3991, 13403495408006409228), (3992, 3992, 13453428563112380935), (3993, 3993, 13502867330544036090), (3994, 3994, 13551816605228843175), (3995, 3995, 13600281233629642268), (3996, 3996, 13648266014224492856), (3997, 3997, 13695775697981770665), (3998, 3998, 13742814988830560576), (3999, 3999, 13789388544126392170), (4000, 4000, 13835500975112364046), (4001, 4001, 13881156847375702537), (4002, 4002, 13926360681299800052), (4003, 4003, 13971116952511777791), (4004, 4004, 14015430092325617136), (4005, 4005, 14059304488180903616), (4006, 4006, 14102744484077226863), (4007, 4007, 14145754381004279583), (4008, 4008, 14188338437367698118), (4009, 4009, 14230500869410686767), (4010, 4010, 14272245851631467607), (4011, 4011, 14313577517196597152), (4012, 4012, 14354499958350190760), (4013, 4013, 14395017226819095323), (4014, 4014, 14435133334214050336), (4015, 4015, 14474852252426877081), (4016, 4016, 14514177914023735245), (4017, 4017, 14553114212634485902), (4018, 4018, 14591665003338199424), (4019, 4019, 14629834103044846475), (4020, 4020, 14667625290873209893), (4021, 4021, 14705042308525054860), (4022, 4022, 14742088860655594432), (4023, 4023, 14778768615240287078), (4024, 4024, 14815085203938002568), (4025, 4025, 14851042222450592163), (4026, 4026, 14886643230878898692), (4027, 4027, 14921891754075241790), (4028, 4028, 14956791281992413174), (4029, 4029, 14991345270029216525), (4030, 4030, 15025557139372586180), (4031, 4031, 15059430277336318511), (4032, 4032, 15092968037696449532), (4033, 4033, 15126173741023311929), (4034, 4034, 15159050675010304401), (4035, 4035, 15191602094799405858), (4036, 4036, 15223831223303466707), (4037, 4037, 15255741251525309132), (4038, 4038, 15287335338873667969), (4039, 4039, 15318616613476003450), (4040, 4040, 15349588172488216799), (4041, 4041, 15380253082401299321), (4042, 4042, 15410614379344945384), (4043, 4043, 15440675069388159307), (4044, 4044, 15470438128836885963), (4045, 4045, 15499906504528694534), (4046, 4046, 15529083114124544604), (4047, 4047, 15557970846397663486), (4048, 4048, 15586572561519563368), (4049, 4049, 15614891091343226618), (4050, 4050, 15642929239683487262), (4051, 4051, 15670689782594636414), (4052, 4052, 15698175468645279138), (4053, 4053, 15725389019190469955), (4054, 4054, 15752333128641153932), (4055, 4055, 15779010464730940048), (4056, 4056, 15805423668780233231), (4057, 4057, 15831575355957751235), (4058, 4058, 15857468115539452229), (4059, 4059, 15883104511164898758), (4060, 4060, 15908487081091083440), (4061, 4061, 15933618338443741540), (4062, 4062, 15958500771466175303), (4063, 4063, 15983136843765614673), (4064, 4064, 16007528994557138801), (4065, 4065, 16031679638905182492), (4066, 4066, 16055591167962651493), (4067, 4067, 16079265949207670307), (4068, 4068, 16102706326677985963), (4069, 4069, 16125914621203050970), (4070, 4070, 16148893130633808402), (4071, 4071, 16171644130070201899), (4072, 4072, 16194169872086433084), (4073, 4073, 16216472586953988713), (4074, 4074, 16238554482862459633), (4075, 4075, 16260417746138173415), (4076, 4076, 16282064541460662308), (4077, 4077, 16303497012076987945), (4078, 4078, 16324717280013944021), (4079, 4079, 16345727446288157957), (4080, 4080, 16366529591114112350), (4081, 4081, 16387125774110106798), (4082, 4082, 16407518034502180509), (4083, 4083, 16427708391326015867), (4084, 4084, 16447698843626842954), (4085, 4085, 16467491370657364821), (4086, 4086, 16487087932073723107), (4087, 4087, 16506490468129523389), (4088, 4088, 16525700899867939510), (4089, 4089, 16544721129311915867), (4090, 4090, 16563553039652486518), (4091, 4091, 16582198495435229737), (4092, 4092, 16600659342744876488), (4093, 4093, 16618937409388091094), (4094, 4094, 16637034505074442188), (4095, 4095, 16654952421595581885), (4096, 4096, 16672692933002650893), (4097, 4097, 16690257795781927137), (4098, 4098, 16707648749028735300), (4099, 4099, 16724867514619634472), (4100, 4100, 16741915797382900978), (4101, 4101, 16758795285267323262), (4102, 4102, 16775507649509325523), (4103, 4103, 16792054544798436672), (4104, 4104, 16808437609441120979), (4105, 4105, 16824658465522986628), (4106, 4106, 16840718719069388262), (4107, 4107, 16856619960204439384), (4108, 4108, 16872363763308450397), (4109, 4109, 16887951687173807834), (4110, 4110, 16903385275159310248), (4111, 4111, 16918666055342976004), (4112, 4112, 16933795540673338139), (4113, 4113, 16948775229119241243), (4114, 4114, 16963606603818155207), (4115, 4115, 16978291133223020518), (4116, 4116, 16992830271247639638), (4117, 4117, 17007225457410628865), (4118, 4118, 17021478116977944932), (4119, 4119, 17035589661104000444), (4120, 4120, 17049561486971382138), (4121, 4121, 17063394977929185797), (4122, 4122, 17077091503629981498), (4123, 4123, 17090652420165422786), (4124, 4124, 17104079070200513171), (4125, 4125, 17117372783106543254), (4126, 4126, 17130534875092711654), (4127, 4127, 17143566649336442743), (4128, 4128, 17156469396112414118), (4129, 4129, 17169244392920306568), (4130, 4130, 17181892904611289192), (4131, 4131, 17194416183513252187), (4132, 4132, 17206815469554799706), (4133, 4133, 17219091990388015071), (4134, 4134, 17231246961510010482), (4135, 4135, 17243281586383273266), (4136, 4136, 17255197056554820576), (4137, 4137, 17266994551774174349), (4138, 4138, 17278675240110168183), (4139, 4139, 17290240278066597722), (4140, 4140, 17301690810696725979), (4141, 4141, 17313027971716654945), (4142, 4142, 17324252883617574714), (4143, 4143, 17335366657776901218), (4144, 4144, 17346370394568313599), (4145, 4145, 17357265183470702094), (4146, 4146, 17368052103176037238), (4147, 4147, 17378732221696171043), (4148, 4148, 17389306596468580752), (4149, 4149, 17399776274461065612), (4150, 4150, 17410142292275407058), (4151, 4151, 17420405676250002548), (4152, 4152, 17430567442561483232), (4153, 4153, 17440628597325325493), (4154, 4154, 17450590136695466346), (4155, 4155, 17460453046962932537), (4156, 4156, 17470218304653493122), (4157, 4157, 17479886876624345186), (4158, 4158, 17489459720159842280), (4159, 4159, 17498937783066275045), (4160, 4160, 17508322003765713427), (4161, 4161, 17517613311388919746), (4162, 4162, 17526812625867341844), (4163, 4163, 17535920858024195406), (4164, 4164, 17544938909664644477), (4165, 4165, 17553867673665089102), (4166, 4166, 17562708034061568929), (4167, 4167, 17571460866137291530), (4168, 4168, 17580127036509294105), (4169, 4169, 17588707403214247150), (4170, 4170, 17597202815793408580), (4171, 4171, 17605614115376736729), (4172, 4172, 17613942134766170540), (4173, 4173, 17622187698518085204), (4174, 4174, 17630351623024931406), (4175, 4175, 17638434716596066260), (4176, 4176, 17646437779537783936), (4177, 4177, 17654361604232553913), (4178, 4178, 17662206975217474683), (4179, 4179, 17669974669261950692), (4180, 4180, 17677665455444600206), (4181, 4181, 17685280095229401705), (4182, 4182, 17692819342541086358), (4183, 4183, 17700283943839784034), (4184, 4184, 17707674638194930247), (4185, 4185, 17714992157358441350), (4186, 4186, 17722237225837165214), (4187, 4187, 17729410560964614584), (4188, 4188, 17736512872971990198), (4189, 4189, 17743544865058500708), (4190, 4190, 17750507233460986360), (4191, 4191, 17757400667522853343), (4192, 4192, 17764225849762325603), (4193, 4193, 17770983455940020910), (4194, 4194, 17777674155125857848), (4195, 4195, 17784298609765300360), (4196, 4196, 17790857475744946412), (4197, 4197, 17797351402457467256), (4198, 4198, 17803781032865903735), (4199, 4199, 17810147003567325991), (4200, 4200, 17816449944855862878), (4201, 4201, 17822690480785107321), (4202, 4202, 17828869229229903800), (4203, 4203, 17834986801947524075), (4204, 4204, 17841043804638237219), (4205, 4205, 17847040837005279936), (4206, 4206, 17852978492814233121), (4207, 4207, 17858857359951810532), (4208, 4208, 17864678020484065394), (4209, 4209, 17870441050714020703), (4210, 4210, 17876147021238728930), (4211, 4211, 17881796497005766778), (4212, 4212, 17887390037369170588), (4213, 4213, 17892928196144817925), (4214, 4214, 17898411521665260833), (4215, 4215, 17903840556834016187), (4216, 4216, 17909215839179318518), (4217, 4217, 17914537900907340628), (4218, 4218, 17919807268954887272), (4219, 4219, 17925024465041567117), (4220, 4220, 17930190005721448151), (4221, 4221, 17935304402434201651), (4222, 4222, 17940368161555739770), (4223, 4223, 17945381784448351768), (4224, 4224, 17950345767510343846), (4225, 4225, 17955260602225187487), (4226, 4226, 17960126775210181191), (4227, 4227, 17964944768264630403), (4228, 4228, 17969715058417550415), (4229, 4229, 17974438117974896962), (4230, 4230, 17979114414566329186), (4231, 4231, 17983744411191509606), (4232, 4232, 17988328566265945666), (4233, 4233, 17992867333666377408), (4234, 4234, 17997361162775715766), (4235, 4235, 18001810498527535923), (4236, 4236, 18006215781450130138), (4237, 4237, 18010577447710124410), (4238, 4238, 18014895929155663293), (4239, 4239, 18019171653359167138), (4240, 4240, 18023405043659665994), (4241, 4241, 18027596519204714367), (4242, 4242, 18031746494991890973), (4243, 4243, 18035855381909887613), (4244, 4244, 18039923586779191217), (4245, 4245, 18043951512392363103), (4246, 4246, 18047939557553919424), (4247, 4247, 18051888117119816773), (4248, 4248, 18055797582036546821), (4249, 4249, 18059668339379843898), (4250, 4250, 18063500772393009321), (4251, 4251, 18067295260524856274), (4252, 4252, 18071052179467279001), (4253, 4253, 18074771901192450017), (4254, 4254, 18078454793989649042), (4255, 4255, 18082101222501727286), (4256, 4256, 18085711547761210695), (4257, 4257, 18089286127226045753), (4258, 4258, 18092825314814991356), (4259, 4259, 18096329460942660270), (4260, 4260, 18099798912554213649), (4261, 4261, 18103234013159712045), (4262, 4262, 18106635102868126298), (4263, 4263, 18110002518421011697), (4264, 4264, 18113336593225848726), (4265, 4265, 18116637657389053705), (4266, 4266, 18119906037748662596), (4267, 4267, 18123142057906691200), (4268, 4268, 18126346038261174966), (4269, 4269, 18129518296037891567), (4270, 4270, 18132659145321769389), (4271, 4271, 18135768897087985055), (4272, 4272, 18138847859232753040), (4273, 4273, 18141896336603810452), (4274, 4274, 18144914631030599968), (4275, 4275, 18147903041354153945), (4276, 4276, 18150861863456682635), (4277, 4277, 18153791390290869457), (4278, 4278, 18156691911908876211), (4279, 4279, 18159563715491061116), (4280, 4280, 18162407085374412507), (4281, 4281, 18165222303080701013), (4282, 4282, 18168009647344352999), (4283, 4283, 18170769394140048035), (4284, 4284, 18173501816710043120), (4285, 4285, 18176207185591226372), (4286, 4286, 18178885768641902860), (4287, 4287, 18181537831068315224), (4288, 4288, 18184163635450901723), (4289, 4289, 18186763441770294296), (4290, 4290, 18189337507433059220), (4291, 4291, 18191886087297182907), (4292, 4292, 18194409433697305369), (4293, 4293, 18196907796469703847), (4294, 4294, 18199381422977029073), (4295, 4295, 18201830558132796622), (4296, 4296, 18204255444425635781), (4297, 4297, 18206656321943298314), (4298, 4298, 18209033428396429535), (4299, 4299, 18211386999142104011), (4300, 4300, 18213717267207128244), (4301, 4301, 18216024463311112634), (4302, 4302, 18218308815889315000), (4303, 4303, 18220570551115257937), (4304, 4304, 18222809892923122231), (4305, 4305, 18225027063029918562), (4306, 4306, 18227222280957439681), (4307, 4307, 18229395764053995245), (4308, 4308, 18231547727515931446), (4309, 4309, 18233678384408937587), (4310, 4310, 18235787945689141686), (4311, 4311, 18237876620223997230), (4312, 4312, 18239944614812963115), (4313, 4313, 18241992134207978843), (4314, 4314, 18244019381133736989), (4315, 4315, 18246026556307754956), (4316, 4316, 18248013858460247992), (4317, 4317, 18249981484353805453), (4318, 4318, 18251929628802872247), (4319, 4319, 18253858484693037389), (4320, 4320, 18255768243000131590), (4321, 4321, 18257659092809135748), (4322, 4322, 18259531221332902242), (4323, 4323, 18261384813930690850), (4324, 4324, 18263220054126521154), (4325, 4325, 18265037123627343238), (4326, 4326, 18266836202341028470), (4327, 4327, 18268617468394182164), (4328, 4328, 18270381098149779881), (4329, 4329, 18272127266224629107), (4330, 4330, 18273856145506658042), (4331, 4331, 18275567907172033226), (4332, 4332, 18277262720702107666), (4333, 4333, 18278940753900201170), (4334, 4334, 18280602172908214541), (4335, 4335, 18282247142223079264), (4336, 4336, 18283875824713044337), (4337, 4337, 18285488381633801835), (4338, 4338, 18287084972644452823), (4339, 4339, 18288665755823315187), (4340, 4340, 18290230887683574954), (4341, 4341, 18291780523188782644), (4342, 4342, 18293314815768196198), (4343, 4343, 18294833917331971994), (4344, 4344, 18296337978286205456), (4345, 4345, 18297827147547822744), (4346, 4346, 18299301572559325010), (4347, 4347, 18300761399303386660), (4348, 7209, 18446744073709489023)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 184562536381678622725), (3001, 3001, 184563487668158046902), (3002, 3002, 184564448474137684376), (3003, 3003, 184565418894945962054), (3004, 3004, 184566399026867274551), (3005, 3005, 184567388967151597856), (3006, 3006, 184568388814024200214), (3007, 3007, 184569398666695451231), (3008, 3008, 184570418625370730200), (3009, 3009, 184571448791260434662), (3010, 3010, 184572489266590090231), (3011, 3011, 184573540154610562716), (3012, 3012, 184574601559608373590), (3013, 3013, 184575673586916119867), (3014, 3014, 184576756342922999442), (3015, 3015, 184577849935085442997), (3016, 3016, 184578954471937853542), (3017, 3017, 184580070063103454713), (3018, 3018, 184581196819305248926), (3019, 3019, 184582334852377086526), (3020, 3020, 184583484275274847062), (3021, 3021, 184584645202087733840), (3022, 3022, 184585817748049682916), (3023, 3023, 184587002029550887708), (3024, 3024, 184588198164149440404), (3025, 3025, 184589406270583091375), (3026, 3026, 184590626468781127804), (3027, 3027, 184591858879876372744), (3028, 3028, 184593103626217305862), (3029, 3029, 184594360831380307105), (3030, 3030, 184595630620182024553), (3031, 3031, 184596913118691867746), (3032, 3032, 184598208454244627766), (3033, 3033, 184599516755453225382), (3034, 3034, 184600838152221588575), (3035, 3035, 184602172775757660779), (3036, 3036, 184603520758586541177), (3037, 3037, 184604882234563758420), (3038, 3038, 184606257338888679139), (3039, 3039, 184607646208118052641), (3040, 3040, 184609048980179693192), (3041, 3041, 184610465794386301311), (3042, 3042, 184611896791449425496), (3043, 3043, 184613342113493565855), (3044, 3044, 184614801904070421076), (3045, 3045, 184616276308173280245), (3046, 3046, 184617765472251560989), (3047, 3047, 184619269544225495464), (3048, 3048, 184620788673500965715), (3049, 3049, 184622323010984489953), (3050, 3050, 184623872709098361306), (3051, 3051, 184625437921795940625), (3052, 3052, 184627018804577104943), (3053, 3053, 184628615514503853185), (3054, 3054, 184630228210216070775), (3055, 3055, 184631857051947454774), (3056, 3056, 184633502201541601214), (3057, 3057, 184635163822468256316), (3058, 3058, 184636842079839733281), (3059, 3059, 184638537140427496386), (3060, 3060, 184640249172678914102), (3061, 3061, 184641978346734183006), (3062, 3062, 184643724834443424257), (3063, 3063, 184645488809383954414), (3064, 3064, 184647270446877732430), (3065, 3065, 184649069924008984640), (3066, 3066, 184650887419642009593), (3067, 3067, 184652723114439164606), (3068, 3068, 184654577190879035930), (3069, 3069, 184656449833274794434), (3070, 3070, 184658341227792738743), (3071, 3071, 184660251562471027789), (3072, 3072, 184662181027238604735), (3073, 3073, 184664129813934314284), (3074, 3074, 184666098116326215377), (3075, 3075, 184668086130131091330), (3076, 3076, 184670094053034159457), (3077, 3077, 184672122084708982284), (3078, 3078, 184674170426837582435), (3079, 3079, 184676239283130763342), (3080, 3080, 184678328859348637915), (3081, 3081, 184680439363321367357), (3082, 3082, 184682571004970112319), (3083, 3083, 184684723996328198619), (3084, 3084, 184686898551562499777), (3085, 3085, 184689094886995038629), (3086, 3086, 184691313221124810330), (3087, 3087, 184693553774649829053), (3088, 3088, 184695816770489400744), (3089, 3089, 184698102433806624302), (3090, 3090, 184700410992031123579), (3091, 3091, 184702742674882012636), (3092, 3092, 184705097714391096694), (3093, 3093, 184707476344926311269), (3094, 3094, 184709878803215401997), (3095, 3095, 184712305328369847674), (3096, 3096, 184714756161909029090), (3097, 3097, 184717231547784646221), (3098, 3098, 184719731732405386431), (3099, 3099, 184722256964661846300), (3100, 3100, 184724807495951709779), (3101, 3101, 184727383580205185363), (3102, 3102, 184729985473910705024), (3103, 3103, 184732613436140887676), (3104, 3104, 184735267728578769961), (3105, 3105, 184737948615544307192), (3106, 3106, 184740656364021147301), (3107, 3107, 184743391243683680706), (3108, 3108, 184746153526924368995), (3109, 3109, 184748943488881355404), (3110, 3110, 184751761407466360067), (3111, 3111, 184754607563392863067), (3112, 3112, 184757482240204578344), (3113, 3113, 184760385724304221544), (3114, 3114, 184763318304982574951), (3115, 3115, 184766280274447852639), (3116, 3116, 184769271927855369064), (3117, 3117, 184772293563337514313), (3118, 3118, 184775345482034039283), (3119, 3119, 184778427988122654095), (3120, 3120, 184781541388849943085), (3121, 3121, 184784685994562599751), (3122, 3122, 184787862118738985081), (3123, 3123, 184791070078021012704), (3124, 3124, 184794310192246364377), (3125, 3125, 184797582784481039330), (3126, 3126, 184800888181052241058), (3127, 3127, 184804226711581605157), (3128, 3128, 184807598709018771882), (3129, 3129, 184811004509675307112), (3130, 3130, 184814444453258975469), (3131, 3131, 184817918882908369366), (3132, 3132, 184821428145227897831), (3133, 3133, 184824972590323138947), (3134, 3134, 184828552571836559851), (3135, 3135, 184832168446983608237), (3136, 3136, 184835820576589179364), (3137, 3137, 184839509325124462634), (3138, 3138, 184843235060744171826), (3139, 3139, 184846998155324163130), (3140, 3140, 184850798984499445185), (3141, 3141, 184854637927702585338), (3142, 3142, 184858515368202516447), (3143, 3143, 184862431693143748531), (3144, 3144, 184866387293585989679), (3145, 3145, 184870382564544180655), (3146, 3146, 184874417905028947681), (3147, 3147, 184878493718087477945), (3148, 3148, 184882610410844822439), (3149, 3149, 184886768394545630766), (3150, 3150, 184890968084596322618), (3151, 3151, 184895209900607700699), (3152, 3152, 184899494266438009885), (3153, 3153, 184903821610236447516), (3154, 3154, 184908192364487129720), (3155, 3155, 184912606966053518784), (3156, 3156, 184917065856223316589), (3157, 3157, 184921569480753829226), (3158, 3158, 184926118289917807960), (3159, 3159, 184930712738549771749), (3160, 3160, 184935353286092816621), (3161, 3161, 184940040396645917246), (3162, 3162, 184944774539011726120), (3163, 3163, 184949556186744875830), (3164, 3164, 184954385818200789947), (3165, 3165, 184959263916585008150), (3166, 3166, 184964190970003031249), (3167, 3167, 184969167471510691858), (3168, 3168, 184974193919165056513), (3169, 3169, 184979270816075865123), (3170, 3170, 184984398670457513703), (3171, 3171, 184989577995681586394), (3172, 3172, 184994809310329942882), (3173, 3173, 185000093138248367364), (3174, 3174, 185005430008600785312), (3175, 3175, 185010820455924054336), (3176, 3176, 185016265020183335549), (3177, 3177, 185021764246828051893), (3178, 3178, 185027318686848439974), (3179, 3179, 185032928896832702032), (3180, 3180, 185038595439024764746), (3181, 3181, 185044318881382651668), (3182, 3182, 185050099797637476149), (3183, 3183, 185055938767353061710), (3184, 3184, 185061836375986196901), (3185, 3185, 185067793214947531761), (3186, 3186, 185073809881663123106), (3187, 3187, 185079886979636635923), (3188, 3188, 185086025118512208278), (3189, 3189, 185092224914137987205), (3190, 3190, 185098486988630343153), (3191, 3191, 185104811970438770654), (3192, 3192, 185111200494411482970), (3193, 3193, 185117653201861708582), (3194, 3194, 185124170740634697459), (3195, 3195, 185130753765175445178), (3196, 3196, 185137402936597143028), (3197, 3197, 185144118922750362362), (3198, 3198, 185150902398292981550), (3199, 3199, 185157754044760863995), (3200, 3200, 185164674550639295772), (3201, 3201, 185171664611435191569), (3202, 3202, 185178724929750077715), (3203, 3203, 185185856215353861175), (3204, 3204, 185193059185259393535), (3205, 3205, 185200334563797839073), (3206, 3206, 185207683082694856174), (3207, 3207, 185215105481147601414), (3208, 3208, 185222602505902565801), (3209, 3209, 185230174911334252755), (3210, 3210, 185237823459524707532), (3211, 3211, 185245548920343907935), (3212, 3212, 185253352071531026270), (3213, 3213, 185261233698776572626), (3214, 3214, 185269194595805429712), (3215, 3215, 185277235564460789578), (3216, 3216, 185285357414789002717), (3217, 3217, 185293560965125350158), (3218, 3218, 185301847042180749294), (3219, 3219, 185310216481129404351), (3220, 3220, 185318670125697412513), (3221, 3221, 185327208828252336897), (3222, 3222, 185335833449893757679), (3223, 3223, 185344544860544812850), (3224, 3224, 185353343939044740215), (3225, 3225, 185362231573242432404), (3226, 3226, 185371208660091016817), (3227, 3227, 185380276105743472580), (3228, 3228, 185389434825649296752), (3229, 3229, 185398685744652232175), (3230, 3230, 185408029797089069540), (3231, 3231, 185417467926889536378), (3232, 3232, 185427001087677285890), (3233, 3233, 185436630242871998667), (3234, 3234, 185446356365792610553), (3235, 3235, 185456180439761680050), (3236, 3236, 185466103458210908879), (3237, 3237, 185476126424787829451), (3238, 3238, 185486250353463673232), (3239, 3239, 185496476268642434123), (3240, 3240, 185506805205271141218), (3241, 3241, 185517238208951355442), (3242, 3242, 185527776336051904822), (3243, 3243, 185538420653822873293), (3244, 3244, 185549172240510858182), (3245, 3245, 185560032185475511679), (3246, 3246, 185571001589307381869), (3247, 3247, 185582081563947069034), (3248, 3248, 185593273232805713221), (3249, 3249, 185604577730886829252), (3250, 3250, 185615996204909505571), (3251, 3251, 185627529813432983568), (3252, 3252, 185639179726982634235), (3253, 3253, 185650947128177349243), (3254, 3254, 185662833211858363768), (3255, 3255, 185674839185219528631), (3256, 3256, 185686966267939049557), (3257, 3257, 185699215692312711616), (3258, 3258, 185711588703388607148), (3259, 3259, 185724086559103385731), (3260, 3260, 185736710530420045018), (3261, 3261, 185749461901467281532), (3262, 3262, 185762341969680420755), (3263, 3263, 185775352045943946148), (3264, 3264, 185788493454735647002), (3265, 3265, 185801767534272405288), (3266, 3266, 185815175636657641986), (3267, 3267, 185828719128030443639), (3268, 3268, 185842399388716390186), (3269, 3269, 185856217813380105420), (3270, 3270, 185870175811179551726), (3271, 3271, 185884274805922091064), (3272, 3272, 185898516236222334469), (3273, 3273, 185912901555661802666), (3274, 3274, 185927432232950420721), (3275, 3275, 185942109752089869980), (3276, 3276, 185956935612538820877), (3277, 3277, 185971911329380070543), (3278, 3278, 185987038433489609491), (3279, 3279, 186002318471707641999), (3280, 3280, 186017753007011585169), (3281, 3281, 186033343618691072032), (3282, 3282, 186049091902524984397), (3283, 3283, 186064999470960541544), (3284, 3284, 186081067953294471247), (3285, 3285, 186097298995856289996), (3286, 3286, 186113694262193719660), (3287, 3287, 186130255433260268292), (3288, 3288, 186146984207605003120), (3289, 3289, 186163882301564544237), (3290, 3290, 186180951449457307894), (3291, 3291, 186198193403780028751), (3292, 3292, 186215609935406590861), (3293, 3293, 186233202833789197622), (3294, 3294, 186250973907161911389), (3295, 3295, 186268924982746593865), (3296, 3296, 186287057906961278917), (3297, 3297, 186305374545631009877), (3298, 3298, 186323876784201173922), (3299, 3299, 186342566527953366597), (3300, 3300, 186361445702223820050), (3301, 3301, 186380516252624429058), (3302, 3302, 186399780145266409463), (3303, 3303, 186419239366986624122), (3304, 3304, 186438895925576612063), (3305, 3305, 186458751850014357060), (3306, 3306, 186478809190698832389), (3307, 3307, 186499070019687359119), (3308, 3308, 186519536430935815855), (3309, 3309, 186540210540541738437), (3310, 3310, 186561094486990348693), (3311, 3311, 186582190431403551975), (3312, 3312, 186603500557791943792), (3313, 3313, 186625027073309866509), (3314, 3314, 186646772208513557724), (3315, 3315, 186668738217622432563), (3316, 3316, 186690927378783542829), (3317, 3317, 186713341994339256597), (3318, 3318, 186735984391098202542), (3319, 3319, 186758856920609523994), (3320, 3320, 186781961959440488415), (3321, 3321, 186805301909457498736), (3322, 3322, 186828879198110553719), (3323, 3323, 186852696278721205273), (3324, 3324, 186876755630774061408), (3325, 3325, 186901059760211884314), (3326, 3326, 186925611199734333816), (3327, 3327, 186950412509100407306), (3328, 3328, 186975466275434628036), (3329, 3329, 187000775113537034538), (3330, 3330, 187026341666197024758), (3331, 3331, 187052168604511109387), (3332, 3332, 187078258628204629752), (3333, 3333, 187104614465957496529), (3334, 3334, 187131238875734006471), (3335, 3335, 187158134645116795281), (3336, 3336, 187185304591644985713), (3337, 3337, 187212751563156590956), (3338, 3338, 187240478438135234359), (3339, 3339, 187268488126061247562), (3340, 3340, 187296783567767210110), (3341, 3341, 187325367735797994721), (3342, 3342, 187354243634775383394), (3343, 3343, 187383414301767320679), (3344, 3344, 187412882806661871515), (3345, 3345, 187442652252545952186), (3346, 3346, 187472725776088904089), (3347, 3347, 187503106547930981201), (3348, 3348, 187533797773076823307), (3349, 3349, 187564802691293988291), (3350, 3350, 187596124577516618029), (3351, 3351, 187627766742254313698), (3352, 3352, 187659732532006297585), (3353, 3353, 187692025329680939846), (3354, 3354, 187724648555020729954), (3355, 3355, 187757605665032773983), (3356, 3356, 187790900154424900257), (3357, 3357, 187824535556047457327), (3358, 3358, 187858515441340889666), (3359, 3359, 187892843420789177992), (3360, 3360, 187927523144379232607), (3361, 3361, 187962558302066329678), (3362, 3362, 187997952624245681997), (3363, 3363, 188033709882230237292), (3364, 3364, 188069833888734798856), (3365, 3365, 188106328498366564889), (3366, 3366, 188143197608122184650), (3367, 3367, 188180445157891431270), (3368, 3368, 188218075130967592807), (3369, 3369, 188256091554564684960), (3370, 3370, 188294498500341590682), (3371, 3371, 188333300084933233798), (3372, 3372, 188372500470488895665), (3373, 3373, 188412103865217785849), (3374, 3374, 188452114523941979790), (3375, 3375, 188492536748656838455), (3376, 3376, 188533374889099027052), (3377, 3377, 188574633343322251994), (3378, 3378, 188616316558280837449), (3379, 3379, 188658429030421265039), (3380, 3380, 188700975306281802457), (3381, 3381, 188743959983100349113), (3382, 3382, 188787387709430629209), (3383, 3383, 188831263185766865074), (3384, 3384, 188875591165177066001), (3385, 3385, 188920376453945070323), (3386, 3386, 188965623912221481004), (3387, 3387, 189011338454683637622), (3388, 3388, 189057525051204770245), (3389, 3389, 189104188727532483425), (3390, 3390, 189151334565976721275), (3391, 3391, 189198967706107367427), (3392, 3392, 189247093345461636520), (3393, 3393, 189295716740261416824), (3394, 3394, 189344843206140726588), (3395, 3395, 189394478118883449765), (3396, 3396, 189444626915171519892), (3397, 3397, 189495295093343724087), (3398, 3398, 189546488214165302399), (3399, 3399, 189598211901608521052), (3400, 3400, 189650471843644401543), (3401, 3401, 189703273793045791012), (3402, 3402, 189756623568201962858), (3403, 3403, 189810527053944940183), (3404, 3404, 189864990202387738370), (3405, 3405, 189920019033774726838), (3406, 3406, 189975619637344313931), (3407, 3407, 190031798172204162802), (3408, 3408, 190088560868219150195), (3409, 3409, 190145914026912284155), (3410, 3410, 190203864022378800887), (3411, 3411, 190262417302213665302), (3412, 3412, 190321580388452704161), (3413, 3413, 190381359878527605236), (3414, 3414, 190441762446235020481), (3415, 3415, 190502794842720015906), (3416, 3416, 190564463897474115628), (3417, 3417, 190626776519348192479), (3418, 3418, 190689739697580462555), (3419, 3419, 190753360502839846213), (3420, 3420, 190817646088284963240), (3421, 3421, 190882603690639035279), (3422, 3422, 190948240631280974067), (3423, 3423, 191014564317352939617), (3424, 3424, 191081582242884658199), (3425, 3425, 191149301989934795817), (3426, 3426, 191217731229749688860), (3427, 3427, 191286877723939739700), (3428, 3428, 191356749325673791283), (3429, 3429, 191427353980891801117), (3430, 3430, 191498699729536141621), (3431, 3431, 191570794706801860483), (3432, 3432, 191643647144406241492), (3433, 3433, 191717265371878013309), (3434, 3434, 191791657817866560817), (3435, 3435, 191866833011471500973), (3436, 3436, 191942799583592992589), (3437, 3437, 192019566268303157132), (3438, 3438, 192097141904238995445), (3439, 3439, 192175535436017193342), (3440, 3440, 192254755915671217197), (3441, 3441, 192334812504111109060), (3442, 3442, 192415714472606399431), (3443, 3443, 192497471204292564576), (3444, 3444, 192580092195701464318), (3445, 3445, 192663587058316205380), (3446, 3446, 192747965520150884848), (3447, 3447, 192833237427355677905), (3448, 3448, 192919412745847743896), (3449, 3449, 193006501562968434893), (3450, 3450, 193094514089167301244), (3451, 3451, 193183460659713399220), (3452, 3452, 193273351736434416694), (3453, 3453, 193364197909484143899), (3454, 3454, 193456009899138827685), (3455, 3455, 193548798557622959320), (3456, 3456, 193642574870965057835), (3457, 3457, 193737349960884023091), (3458, 3458, 193833135086706645255), (3459, 3459, 193929941647316870216), (3460, 3460, 194027781183137433524), (3461, 3461, 194126665378144488946), (3462, 3462, 194226606061915871428), (3463, 3463, 194327615211713648413), (3464, 3464, 194429704954601627868), (3465, 3465, 194532887569598506195), (3466, 3466, 194637175489867354357), (3467, 3467, 194742581304942156094), (3468, 3468, 194849117762992128025), (3469, 3469, 194956797773124567734), (3470, 3470, 195065634407726992697), (3471, 3471, 195175640904849349987), (3472, 3472, 195286830670627094323), (3473, 3473, 195399217281745949978), (3474, 3474, 195512814487949190551), (3475, 3475, 195627636214588289507), (3476, 3476, 195743696565217813797), (3477, 3477, 195861009824235452735), (3478, 3478, 195979590459568094727), (3479, 3479, 196099453125404885301), (3480, 3480, 196220612664978221374), (3481, 3481, 196343084113393658640), (3482, 3482, 196466882700509731501), (3483, 3483, 196592023853868708101), (3484, 3484, 196718523201679326725), (3485, 3485, 196846396575852584126), (3486, 3486, 196975660015091671318), (3487, 3487, 197106329768037177957), (3488, 3488, 197238422296468712653), (3489, 3489, 197371954278564113548), (3490, 3490, 197506942612217451077), (3491, 3491, 197643404418417053211), (3492, 3492, 197781357044684812580), (3493, 3493, 197920818068578064716), (3494, 3494, 198061805301255357320), (3495, 3495, 198204336791107461888), (3496, 3496, 198348430827455011330), (3497, 3497, 198494105944314180335), (3498, 3498, 198641380924231859260), (3499, 3499, 198790274802191807229), (3500, 3500, 198940806869593305984), (3501, 3501, 199092996678303872838), (3502, 3502, 199246864044787628857), (3503, 3503, 199402429054310957223), (3504, 3504, 199559712065227126574), (3505, 3505, 199718733713341595039), (3506, 3506, 199879514916359752729), (3507, 3507, 200042076878418903605), (3508, 3508, 200206441094706332010), (3509, 3509, 200372629356165344696), (3510, 3510, 200540663754291225963), (3511, 3511, 200710566686019091660), (3512, 3512, 200882360858705677125), (3513, 3513, 201056069295207144980), (3514, 3514, 201231715339055050805), (3515, 3515, 201409322659732658355), (3516, 3516, 201588915258053851059), (3517, 3517, 201770517471646943176), (3518, 3518, 201954153980545752190), (3519, 3519, 202139849812890353848), (3520, 3520, 202327630350740002760), (3521, 3521, 202517521336000764724), (3522, 3522, 202709548876470471937), (3523, 3523, 202903739452003679132), (3524, 3524, 203100119920799367413), (3525, 3525, 203298717525814213254), (3526, 3526, 203499559901304312866), (3527, 3527, 203702675079498326881), (3528, 3528, 203908091497405087268), (3529, 3529, 204115838003758787507), (3530, 3530, 204325943866104958449), (3531, 3531, 204538438778030516068), (3532, 3532, 204753352866541253472), (3533, 3533, 204970716699590238216), (3534, 3534, 205190561293760667217), (3535, 3535, 205412918122106825496), (3536, 3536, 205637819122156891589), (3537, 3537, 205865296704081432014), (3538, 3538, 206095383759031529536), (3539, 3539, 206328113667650595443), (3540, 3540, 206563520308764024557), (3541, 3541, 206801638068250963488), (3542, 3542, 207042501848102577672), (3543, 3543, 207286147075671321291), (3544, 3544, 207532609713115836153), (3545, 3545, 207781926267046231339), (3546, 3546, 208034133798374624888), (3547, 3547, 208289269932375962117), (3548, 3548, 208547372868964262613), (3549, 3549, 208808481393189589421), (3550, 3550, 209072634885961179850), (3551, 3551, 209339873335002327539), (3552, 3552, 209610237346042760339), (3553, 3553, 209883768154254418126), (3554, 3554, 210160507635936699210), (3555, 3555, 210440498320457413501), (3556, 3556, 210723783402455855456), (3557, 3557, 211010406754314589973), (3558, 3558, 211300412938906730241), (3559, 3559, 211593847222625678074), (3560, 3560, 211890755588704494879), (3561, 3561, 212191184750832275062), (3562, 3562, 212495182167075103869), (3563, 3563, 212802796054109398359), (3564, 3564, 213114075401775653798), (3565, 3565, 213429069987960848401), (3566, 3566, 213747830393817997362), (3567, 3567, 214070408019331592595), (3568, 3568, 214396855099237918067), (3569, 3569, 214727224719309492042), (3570, 3570, 215061570833013157473), (3571, 3571, 215399948278551620364), (3572, 3572, 215742412796298523475), (3573, 3573, 216089021046637439661), (3574, 3574, 216439830628215475625), (3575, 3575, 216794900096622493426), (3576, 3576, 217154288983507283889), (3577, 3577, 217518057816142363637), (3578, 3578, 217886268137449416141), (3579, 3579, 218258982526497757277), (3580, 3580, 218636264619488577947), (3581, 3581, 219018179131238100697), (3582, 3582, 219404791877173184400), (3583, 3583, 219796169795853321477), (3584, 3584, 220192380972033396242), (3585, 3585, 220593494660282011304), (3586, 3586, 220999581309170642052), (3587, 3587, 221410712586049347618), (3588, 3588, 221826961402425250958), (3589, 3589, 222248401939960501354), (3590, 3590, 222675109677106950350), (3591, 3591, 223107161416395307532), (3592, 3592, 223544635312397096312), (3593, 3593, 223987610900378302610), (3594, 3594, 224436169125664201844), (3595, 3595, 224890392373735462611), (3596, 3596, 225350364501076259678), (3597, 3597, 225816170866795785179), (3598, 3598, 226287898365045226115), (3599, 3599, 226765635458252979195), (3600, 3600, 227249472211201601680), (3601, 3601, 227739500325970750130), (3602, 3602, 228235813177771138814), (3603, 3603, 228738505851695357001), (3604, 3604, 229247675180412220516), (3605, 3605, 229763419782832198932), (3606, 3606, 230285840103772356698), (3607, 3607, 230815038454650175622), (3608, 3608, 231351119055236588683), (3609, 3609, 231894188076499552423), (3610, 3610, 232444353684570518588), (3611, 3611, 233001726085867236626), (3612, 3612, 233566417573407428616), (3613, 3613, 234138542574349028751), (3614, 3614, 234718217698793872225), (3615, 3615, 235305561789892954996), (3616, 3616, 235900695975292668160), (3617, 3617, 236503743719962740369), (3618, 3618, 237114830880448000894), (3619, 3619, 237734085760587506390), (3620, 3620, 238361639168746058459), (3621, 3621, 238997624476604678708), (3622, 3622, 239642177679558205598), (3623, 3623, 240295437458769835248), (3624, 3624, 240957545244934149025), (3625, 3625, 241628645283801956784), (3626, 3626, 242308884703522138754), (3627, 3627, 242998413583857594082), (3628, 3628, 243697385027334402958), (3629, 3629, 244405955232385385061), (3630, 3630, 245124283568551393103), (3631, 3631, 245852532653805919810), (3632, 3632, 246590868434070923308), (3633, 3633, 247339460264994193288), (3634, 3634, 248098480996061092333), (3635, 3635, 248868107057116117458), (3636, 3636, 249648518547372440416), (3637, 3637, 250439899326990406146), (3638, 3638, 251242437111308901418), (3639, 3639, 252056323567816555126), (3640, 3640, 252881754415952902908), (3641, 3641, 253718929529832947009), (3642, 3642, 254568053043991973180), (3643, 3643, 255429333462251055704), (3644, 3644, 256302983769807395430), (3645, 3645, 257189221548657500308), (3646, 3646, 258088269096465240086), (3647, 3647, 259000353548990993503), (3648, 3648, 259925707006202464757), (3649, 3649, 260864566662192284061), (3650, 3650, 261817174939032232544), (3651, 3651, 262783779624698853280), (3652, 3652, 263764634015210336452), (3653, 3653, 264759997061119907025), (3654, 3654, 265770133518516507381), (3655, 3655, 266795314104689365492), (3656, 3656, 267835815658619081936), (3657, 3657, 268891921306464167768), (3658, 3658, 269963920632218531554), (3659, 3659, 271052109853722260279), (3660, 3660, 272156792004215178237), (3661, 3661, 273278277119630114039), (3662, 3662, 274416882431830572901), (3663, 3663, 275572932568005614349), (3664, 3664, 276746759756443190281), (3665, 3665, 277938704038912021434), (3666, 3666, 279149113489891299319), (3667, 3667, 280378344442897113718), (3668, 3668, 281626761724164542361), (3669, 3669, 282894738893954819527), (3670, 3670, 284182658495767945348), (3671, 3671, 285490912313752530061), (3672, 3672, 286819901638616610718), (3673, 3673, 288170037542355656878), (3674, 3674, 289541741162127022573), (3675, 3675, 290935443993613731823), (3676, 3676, 292351588194234733081), (3677, 3677, 293790626896573654636), (3678, 3678, 295253024532413670233), (3679, 3679, 296739257167782375694), (3680, 3680, 298249812849427618758), (3681, 3681, 299785191963163053032), (3682, 3682, 301345907604540842461), (3683, 3683, 302932485962328466520), (3684, 3684, 304545466715287012419), (3685, 3685, 306185403442769735020), (3686, 3686, 307852864049682066855), (3687, 3687, 309548431206367720828), (3688, 3688, 311272702804010101270), (3689, 3689, 313026292426163982132), (3690, 3690, 314809829837059384709), (3691, 3691, 316623961487347855122), (3692, 3692, 318469351037990971126), (3693, 3693, 320346679903021969822), (3694, 3694, 322256647811943957487), (3695, 3695, 324199973392562319438), (3696, 3696, 326177394775084775239), (3697, 3697, 328189670218360111377), (3698, 3698, 330237578759166063211), (3699, 3699, 332321920885498209573), (3700, 3700, 334443519234855191534), (3701, 3701, 336603219318561182080), (3702, 3702, 338801890273214433020), (3703, 3703, 341040425640401033076), (3704, 3704, 343319744175865858000), (3705, 3705, 345640790689388218400), (3706, 3706, 348004536916668060705), (3707, 3707, 350411982424589906919), (3708, 3708, 352864155551296194284), (3709, 3709, 355362114382569471256), (3710, 3710, 357906947766094206362), (3711, 3711, 360499776365243967487), (3712, 3712, 363141753754118638898), (3713, 3713, 365834067555639382207), (3714, 3714, 368577940624596449221), (3715, 3715, 371374632277636967165), (3716, 3716, 374225439572276703289), (3717, 3717, 377131698637121855426), (3718, 3718, 380094786055594404182), (3719, 3719, 383116120305567815713), (3720, 3720, 386197163257439235748), (3721, 3721, 389339421733290120590), (3722, 3722, 392544449129919886504), (3723, 3723, 395813847108677026042), (3724, 3724, 399149267355159664519), (3725, 3725, 402552413412013165154), (3726, 3726, 406025042588216619107), (3727, 3727, 409568967948423389312), (3728, 3728, 413186060386103859984), (3729, 3729, 416878250784431757323), (3730, 3730, 420647532269059469091), (3731, 3731, 424495962557143359249), (3732, 3732, 428425666407207849318), (3733, 3733, 432438838174677767019), (3734, 3734, 436537744478162940333), (3735, 3735, 440724726981848089130), (3736, 3736, 445002205299625640723), (3737, 3737, 449372680026910133748), (3738, 3738, 453838735906391404791), (3739, 3739, 458403045134320870755), (3740, 3740, 463068370814282097768), (3741, 3741, 467837570565774733825), (3742, 3742, 472713600295341111557), (3743, 3743, 477699518138388824435), (3744, 3744, 482798488580311866713), (3745, 3745, 488013786765989131224), (3746, 3746, 493348803007243918676), (3747, 3747, 498807047498383486547), (3748, 3748, 504392155250505543515), (3749, 3749, 510107891255861103653), (3750, 3750, 515958155894202529760), (3751, 3751, 521946990593724353562), (3752, 3752, 528078583759925170795), (3753, 3753, 534357276986484365284), (3754, 3754, 540787571563060611059), (3755, 3755, 547374135295783242590), (3756, 3756, 554121809657126108427), (3757, 3757, 561035617282830119015), (3758, 3758, 568120769834579318937), (3759, 3759, 575382676248240198776), (3760, 3760, 582826951388649664275), (3761, 3761, 590459425133188486792), (3762, 3762, 598286151907709416367), (3763, 3763, 606313420699808083059), (3764, 3764, 614547765575936399249), (3765, 3765, 622995976730468913959), (3766, 3766, 631665112096549457356), (3767, 3767, 640562509550375975035), (3768, 3768, 649695799742533783183), (3769, 3769, 659072919592070289423), (3770, 3770, 668702126481226898507), (3771, 3771, 678592013191116455562), (3772, 3772, 688751523621168050459), (3773, 3773, 699189969337867035879), (3774, 3774, 709917047001209332537), (3775, 3775, 720942856720379129456), (3776, 3776, 732277921393462627024), (3777, 3777, 743933207089543367450), (3778, 3778, 755920144535304059346), (3779, 3779, 768250651772304101703), (3780, 3780, 780937158055431196497), (3781, 3781, 793992629067661061342), (3782, 3782, 807430593531224607367), (3783, 3783, 821265171300602216118), (3784, 3784, 835511103028467168788), (3785, 3785, 850183781501814317970), (3786, 3786, 865299284752067637235), (3787, 3787, 880874411049995864314), (3788, 3788, 896926715903816464001), (3789, 3789, 913474551186975092050), (3790, 3790, 930537106530794552971), (3791, 3791, 948134453126541523182), (3792, 3792, 966287590091512696752), (3793, 3793, 985018493564550535424), (3794, 3794, 1004350168708023287369), (3795, 3795, 1024306704805810421142), (3796, 3796, 1044913333660294841329), (3797, 3797, 1066196491505855167545), (3798, 3798, 1088183884671959716662), (3799, 3799, 1110904559245780794900), (3800, 3800, 1134388975002373753708), (3801, 3801, 1158669083890009125208), (3802, 3802, 1183778413379326856329), (3803, 3803, 1209752155007728637807), (3804, 3804, 1236627258474978615761), (3805, 3805, 1264442531672498132648), (3806, 3806, 1293238747057484250628), (3807, 3807, 1323058754813937606394), (3808, 3808, 1353947603276152310605), (3809, 3809, 1385952667126417172587), (3810, 3810, 1419123783917841682900), (3811, 3811, 1453513399515612220352), (3812, 3812, 1489176723095888456165), (3813, 3813, 1526171892391278189354), (3814, 3814, 1564560149925721491751), (3815, 3815, 1604406031040044969675), (3816, 3816, 1645777564572822574534), (3817, 3817, 1688746487129948219963), (3818, 3818, 1733388471950978043779), (3819, 3819, 1779783373461374479458), (3820, 3820, 1828015488687870654442), (3821, 3821, 1878173836809919959491), (3822, 3822, 1930352458224313511723), (3823, 3823, 1984650734613319481094), (3824, 3824, 2041173731629982257277), (3825, 3825, 2100032565948461309131), (3826, 3826, 2161344798573529198717), (3827, 3827, 2225234856462730228504), (3828, 3828, 2291834484688486272676), (3829, 3829, 2361283231557013519475), (3830, 3830, 2433728969307814405728), (3831, 3831, 2509328453243421851369), (3832, 3832, 2588247922385861664265), (3833, 3833, 2670663745026021230302), (3834, 3834, 2756763112827041074677), (3835, 3835, 2846744787465492302448), (3836, 3836, 2940819904147244554198), (3837, 3837, 3039212836721638385066), (3838, 3838, 3142162129541253656432), (3839, 3839, 3249921501678977764334), (3840, 3840, 3362760929623397302506), (3841, 3841, 3480967815132390303481), (3842, 3842, 3604848245538314978114), (3843, 3843, 3734728354472069817790), (3844, 3844, 3870955791713862761833), (3845, 3845, 4013901311692799662838), (3846, 3846, 4163960491053194634253), (3847, 3847, 4321555586691503896528), (3848, 3848, 4487137546753657883556), (3849, 3849, 4661188188279078415014), (3850, 3850, 4844222556496812218511), (3851, 3851, 5036791482234359226050), (3852, 3852, 5239484355505837455469), (3853, 3853, 5452932135119750728917), (3854, 3854, 5677810616106398918979), (3855, 3855, 5914843978931663085776), (3856, 3856, 6164808646860732400827), (3857, 3857, 6428537480488296374781), (3858, 3858, 6706924341389887570610), (3859, 3859, 7000929060105002862996), (3860, 3860, 7311582847272866900129), (3861, 3873, 7529223614670646417664), (3874, 3874, 7504460002547589016099), (3875, 3875, 7430158418363949520890), (3876, 3876, 7356592493429652990980), (3877, 3877, 7283754943989755436614), (3878, 3878, 7211638558405698452093), (3879, 3879, 7140236196441285596132), (3880, 3880, 7069540788555728313002), (3881, 3881, 6999545335203691399012), (3882, 3882, 6930242906142268711893), (3883, 3883, 6861626639744820506825), (3884, 3884, 6793689742321604462203), (3885, 3885, 6726425487447133130894), (3886, 3886, 6659827215294191218707), (3887, 3887, 6593888331974446751195), (3888, 3888, 6528602308885590842767), (3889, 3889, 6463962682064941428482), (3890, 3890, 6399963051549446958893), (3891, 3891, 6336597080742026691974), (3892, 3892, 6273858495784184843538), (3893, 3893, 6211741084934836478751), (3894, 3894, 6150238697955283642328), (3895, 3895, 6089345245500280833988), (3896, 3896, 6029054698515129538602), (3897, 3897, 5969361087638742117427), (3898, 3898, 5910258502612615957849), (3899, 3899, 5851741091695659364207), (3900, 3900, 5793803061084811251690), (3901, 3901, 5736438674341397278901), (3902, 3902, 5679642251823165622674), (3903, 3903, 5623408170121946161064), (3904, 3904, 5567730861506877387192), (3905, 3905, 5512604813373145927913), (3906, 3906, 5458024567696184087042), (3907, 3907, 5403984720491271373309), (3908, 3908, 5350479921278486508227), (3909, 3909, 5297504872552956938838), (3910, 3910, 5245054329260353404790), (3911, 3911, 5193123098277577628505), (3912, 3912, 5141706037898591711392), (3913, 3913, 5090798057325338328110), (3914, 3914, 5040394116163701314961), (3915, 3915, 4990489223924456747486), (3916, 3916, 4941078439529165096521), (3917, 3917, 4892156870820955541110), (3918, 3918, 4843719674080154001099), (3919, 3919, 4795762053544706931781), (3920, 3920, 4748279260935353397803), (3921, 3921, 4701266594985498413666), (3922, 3922, 4654719400975741003630), (3923, 3923, 4608633070273010894683), (3924, 3924, 4563003039874268212558), (3925, 3925, 4517824791954721002532), (3926, 3926, 4473093853420515844091), (3927, 3927, 4428805795465857271378), (3928, 3928, 4384956233134512149879), (3929, 3929, 4341540824885655593939), (3930, 3930, 4298555272164015439544), (3931, 3931, 4255995318974272712420), (3932, 3932, 4213856751459675952891), (3933, 3933, 4172135397484827676130), (3934, 3934, 4130827126222601659534), (3935, 3935, 4089927847745150157955), (3936, 3936, 4049433512618960552430), (3937, 3937, 4009340111503921339040), (3938, 3938, 3969643674756357761426), (3939, 3939, 3930340272035997783590), (3940, 3940, 3891426011916829488703), (3941, 3941, 3852897041501811374953), (3942, 3942, 3814749546041397400944), (3943, 3943, 3776979748555839010835), (3944, 3944, 3739583909461226743401), (3945, 3945, 3702558326199234399407), (3946, 3946, 3665899332870529108324), (3947, 3947, 3629603299871810998341), (3948, 3948, 3593666633536446533011), (3949, 3949, 3558085775778659933674), (3950, 3950, 3522857203741247459083), (3951, 3951, 3487977429446779662459), (3952, 3952, 3453442999452257091543), (3953, 3953, 3419250494507185239152), (3954, 3954, 3385396529215034890249), (3955, 3955, 3351877751698054346781), (3956, 3956, 3318690843265400343348), (3957, 3957, 3285832518084554795394), (3958, 3958, 3253299522855994846925), (3959, 3959, 3221088636491084006856), (3960, 3960, 3189196669793152482036), (3961, 3961, 3157620465141735130728), (3962, 3962, 3126356896179935772998), (3963, 3963, 3095402867504886903959), (3964, 3964, 3064755314361274162336), (3965, 3965, 3034411202337895210233), (3966, 3966, 3004367527067222980429), (3967, 3967, 2974621313927943544979), (3968, 3968, 2945169617750439153445), (3969, 3969, 2916009522525187280638), (3970, 3970, 2887138141114046812513), (3971, 3971, 2858552614964402784667), (3972, 3972, 2830250113826141370957), (3973, 3973, 2802227835471427099957), (3974, 3974, 2774483005417254554413), (3975, 3975, 2747012876650747083578), (3976, 3976, 2719814729357175330275), (3977, 3977, 2692885870650668643836), (3978, 3978, 2666223634307592716670), (3979, 3979, 2639825380502567046208), (3980, 3980, 2613688495547096085354), (3981, 3981, 2587810391630788203321), (3982, 3982, 2562188506565136834971), (3983, 3983, 2536820303529838450467), (3984, 3984, 2511703270821622228185), (3985, 3985, 2486834921605566562559), (3986, 3986, 2462212793668877784712), (3987, 3987, 2437834449177106717537), (3988, 3988, 2413697474432778928254), (3989, 3989, 2389799479636414780450), (3990, 3990, 2366138098649915624208), (3991, 3991, 2342710988762292697235), (3992, 3992, 2319515830457715541817), (3993, 3993, 2296550327185856972096), (3994, 3994, 2273812205134511853560), (3995, 3995, 2251299213004467181743), (3996, 3996, 2229009121786601170043), (3997, 3997, 2206939724541189277270), (3998, 3998, 2185088836179395324030), (3999, 3999, 2163454293246926063396), (4000, 4000, 2142033953709827785540), (4001, 4001, 2120825696742403748060), (4002, 4002, 2099827422517231433722), (4003, 4003, 2079037051997258845270), (4004, 4004, 2058452526729959252742), (4005, 4005, 2038071808643524012616), (4006, 4006, 2017892879845073279818), (4007, 4007, 1997913742420864633483), (4008, 4008, 1978132418238479835132), (4009, 4009, 1958546948750970133794), (4010, 4010, 1939155394802940726529), (4011, 4011, 1919955836438555174781), (4012, 4012, 1900946372711440767110), (4013, 4013, 1882125121496476007039), (4014, 4014, 1863490219303441591128), (4015, 4015, 1845039821092516426860), (4016, 4016, 1826772100091600422633), (4017, 4017, 1808685247615445963003), (4018, 4018, 1790777472886580161389), (4019, 4019, 1773047002858000159791), (4020, 4020, 1755492082037623920586), (4021, 4021, 1738110972314479129293), (4022, 4022, 1720901952786612999300), (4023, 4023, 1703863319590705939901), (4024, 4024, 1686993385733372217723), (4025, 4025, 1670290480924130908637), (4026, 4026, 1653752951410030602611), (4027, 4027, 1637379159811911487734), (4028, 4028, 1621167484962288601716), (4029, 4029, 1605116321744840199719), (4030, 4030, 1589224080935485346257), (4031, 4031, 1573489189045034996294), (4032, 4032, 1557910088163400986429), (4033, 4033, 1542485235805347511316), (4034, 4034, 1527213104757769813184), (4035, 4035, 1512092182928484963549), (4036, 4036, 1497120973196519765890), (4037, 4037, 1482297993263880956327), (4038, 4038, 1467621775508793026066), (4039, 4039, 1453090866840389134719), (4040, 4040, 1438703828554840727445), (4041, 4041, 1424459236192911611331), (4042, 4042, 1410355679398922387457), (4043, 4043, 1396391761781111274710), (4044, 4044, 1382566100773377499712), (4045, 4045, 1368877327498393564072), (4046, 4046, 1355324086632072835715), (4047, 4047, 1341905036269379045262), (4048, 4048, 1328618847791464401249), (4049, 4049, 1315464205734123169554), (4050, 4050, 1302439807657547692628), (4051, 4051, 1289544364017373953097), (4052, 4052, 1276776598037003913957), (4053, 4053, 1264135245581191994017), (4054, 4054, 1251619055030883162393), (4055, 4055, 1239226787159290259795), (4056, 4056, 1226957215009198277025), (4057, 4057, 1214809123771483442599), (4058, 4058, 1202781310664835091682), (4059, 4059, 1190872584816668407606), (4060, 4060, 1179081767145216245154), (4061, 4061, 1167407690242788361539), (4062, 4062, 1155849198260186496573), (4063, 4063, 1144405146792263857993), (4064, 4064, 1133074402764617681182), (4065, 4065, 1121855844321403644734), (4066, 4066, 1110748360714261034390), (4067, 4067, 1099750852192337657812), (4068, 4068, 1088862229893403621596), (4069, 4069, 1078081415736043189699), (4070, 4070, 1067407342312914049207), (4071, 4071, 1056838952785063415057), (4072, 4072, 1046375200777290509957), (4073, 4073, 1036015050274545059363), (4074, 4074, 1025757475519351543924), (4075, 4075, 1015601460910249053390), (4076, 4076, 1005546000901236686525), (4077, 4077, 995590099902214541114), (4078, 4078, 985732772180410436747), (4079, 4079, 975973041762782610640), (4080, 4080, 966309942339388723406), (4081, 4081, 956742517167711607333), (4082, 4082, 947269818977932284488), (4083, 4083, 937890909879140875731), (4084, 4084, 928604861266476114585), (4085, 4085, 919410753729184271866), (4086, 4086, 910307676959588387986), (4087, 4087, 901294729662958799986), (4088, 4088, 892371019468276039590), (4089, 4089, 883535662839877266921), (4090, 4090, 874787784989977492001), (4091, 4091, 866126519792056922774), (4092, 4092, 857551009695105864132), (4093, 4093, 849060405638718677359), (4094, 4094, 840653866969028393424), (4095, 4095, 832330561355473656856), (4096, 4096, 824089664708389759263), (4097, 4097, 815930361097415603231), (4098, 4098, 807851842670708518050), (4099, 4099, 799853309574958928763), (4100, 4100, 791933969876196959171), (4101, 4101, 784093039481383127892), (4102, 4102, 776329742060775374151), (4103, 4103, 768643308971064726882), (4104, 4104, 761032979179272006814), (4105, 4105, 753497999187398026548), (4106, 4106, 746037622957819828266), (4107, 4107, 738651111839425572540), (4108, 4108, 731337734494480764891), (4109, 4109, 724096766826218579100), (4110, 4110, 716927491907147108020), (4111, 4111, 709829199908066443584), (4112, 4112, 702801188027788558004), (4113, 4113, 695842760423553027727), (4114, 4114, 688953228142131710621), (4115, 4115, 682131909051615555070), (4116, 4116, 675378127773876787198), (4117, 4117, 668691215617699789305), (4118, 4118, 662070510512574048817), (4119, 4119, 655515356943142622591), (4120, 4120, 649025105884299626328), (4121, 4121, 642599114736930323097), (4122, 4122, 636236747264287448611), (4123, 4123, 629937373528997473872), (4124, 4124, 623700369830690568190), (4125, 4125, 617525118644248087317), (4126, 4126, 611411008558661472591), (4127, 4127, 605357434216496507516), (4128, 4128, 599363796253956938134), (4129, 4129, 593429501241541522905), (4130, 4130, 587553961625288636540), (4131, 4131, 581736595668602610436), (4132, 4132, 575976827394656049936), (4133, 4133, 570274086529362425680), (4134, 4134, 564627808444913292752), (4135, 4135, 559037434103874547279), (4136, 4136, 553502410003836185425), (4137, 4137, 548022188122610084579), (4138, 4138, 542596225863970380771), (4139, 4139, 537223986003931070071), (4140, 4140, 531904936637555514922), (4141, 4141, 526638551126292589031), (4142, 4142, 521424308045834246566), (4143, 4143, 516261691134489353035), (4144, 4144, 511150189242068666372), (4145, 4145, 506089296279275907299), (4146, 4146, 501078511167599908216), (4147, 4147, 496117337789702879422), (4148, 4148, 491205284940299880616), (4149, 4149, 486341866277524634273), (4150, 4150, 481526600274776865617), (4151, 4151, 476759010173046401601), (4152, 4152, 472038623933709308516), (4153, 4153, 467364974191791394570), (4154, 4154, 462737598209694450070), (4155, 4155, 458156037831380643633), (4156, 4156, 453619839437010538251), (4157, 4157, 449128553898030235892), (4158, 4158, 444681736532703203853), (4159, 4159, 440278947062082380053), (4160, 4160, 435919749566418198072), (4161, 4161, 431603712441998215913), (4162, 4162, 427330408358414075161), (4163, 4163, 423099414216251559566), (4164, 4164, 418910311105199563926), (4165, 4165, 414762684262573825670), (4166, 4166, 410656123032251312544), (4167, 4167, 406590220824011200539), (4168, 4168, 402564575073278416375), (4169, 4169, 398578787201265758787), (4170, 4170, 394632462575510652265), (4171, 4171, 390725210470802626005), (4172, 4172, 386856644030497649510), (4173, 4173, 383026380228215494564), (4174, 4174, 379234039829916331251), (4175, 4175, 375479247356352803219), (4176, 4176, 371761631045893864573), (4177, 4177, 368080822817716697597), (4178, 4178, 364436458235363066928), (4179, 4179, 360828176470656501909), (4180, 4180, 357255620267976734563), (4181, 4181, 353718435908887856003), (4182, 4182, 350216273177116689112), (4183, 4183, 346748785323877910012), (4184, 4184, 343315629033542485161), (4185, 4185, 339916464389646024912), (4186, 4186, 336550954841233688031), (4187, 4187, 333218767169538304981), (4188, 4188, 329919571454988420774), (4189, 4189, 326653041044542990865), (4190, 4190, 323418852519349495906), (4191, 4191, 320216685662722273174), (4192, 4192, 317046223428437894232), (4193, 4193, 313907151909344449735), (4194, 4194, 310799160306281633401), (4195, 4195, 307721940897308547921), (4196, 4196, 304675189007236186061), (4197, 4197, 301658602977461570357), (4198, 4198, 298671884136100564710), (4199, 4199, 295714736768416400703), (4200, 4200, 292786868087540990795), (4201, 4201, 289887988205486129500), (4202, 4202, 287017810104441712376), (4203, 4203, 284176049608358131066), (4204, 4204, 281362425354810030758), (4205, 4205, 278576658767138644315), (4206, 4206, 275818474026869944866), (4207, 4207, 273087598046405886006), (4208, 4208, 270383760441986025749), (4209, 4209, 267706693506916857177), (4210, 4210, 265056132185066195225), (4211, 4211, 262431814044619995272), (4212, 4212, 259833479252099005220), (4213, 4213, 257260870546632678436), (4214, 4214, 254713733214487800431), (4215, 4215, 252191815063849307358), (4216, 4216, 249694866399850799364), (4217, 4217, 247222639999852276598), (4218, 4218, 244774891088962650097), (4219, 4219, 242351377315804604057), (4220, 4220, 239951858728519409957), (4221, 4221, 237576097751009316789), (4222, 4222, 235223859159415165138), (4223, 4223, 232894910058826896176), (4224, 4224, 230589019860224649679), (4225, 4225, 228305960257648167999), (4226, 4226, 226045505205592245544), (4227, 4227, 223807430896625985687), (4228, 4228, 221591515739233649195), (4229, 4229, 219397540335874900193), (4230, 4230, 217225287461262277419), (4231, 4231, 215074542040853740019), (4232, 4232, 212945091129558158434), (4233, 4233, 210836723890651642014), (4234, 4234, 208749231574902615856), (4235, 4235, 206682407499903580055), (4236, 4236, 204636047029607505005), (4237, 4237, 202609947554066836639), (4238, 4238, 200603908469373105583), (4239, 4239, 198617731157795154042), (4240, 4240, 196651218968114013903), (4241, 4241, 194704177196152489013), (4242, 4242, 192776413065497513875), (4243, 4243, 190867735708413380074), (4244, 4244, 188977956146943940667), (4245, 4245, 187106887274201921453), (4246, 4246, 185254343835843486587), (4247, 4247, 183420142411726224343), (4248, 4248, 181604101397748736974), (4249, 4249, 179806040987870036607), (4250, 4250, 178025783156306966938), (4251, 4251, 176263151639907888058), (4252, 4252, 174517971920700879265), (4253, 4253, 172790071208614731945), (4254, 4254, 171079278424371021728), (4255, 4255, 169385424182545566068), (4256, 4256, 167708340774797590166), (4257, 4257, 166047862153264940758), (4258, 4258, 164403823914123703721), (4259, 4259, 162776063281310597744), (4260, 4260, 161164419090406532419), (4261, 4261, 159568731772679735069), (4262, 4262, 157988843339286866405), (4263, 4263, 156424597365630560797), (4264, 4264, 154875838975871842373), (4265, 4265, 153342414827595883538), (4266, 4266, 151824173096629587661), (4267, 4267, 150320963462009492734), (4268, 4268, 148832637091098507657), (4269, 4269, 147359046624850007581), (4270, 4270, 145900046163217829288), (4271, 4271, 144455491250710722068), (4272, 4272, 143025238862089823830), (4273, 4273, 141609147388207746366), (4274, 4274, 140207076621987867689), (4275, 4275, 138818887744542443256), (4276, 4276, 137444443311428161640), (4277, 4277, 136083607239037783802), (4278, 4278, 134736244791126518616), (4279, 4279, 133402222565471800610), (4280, 4280, 132081408480665149119), (4281, 4281, 130773671763034801108), (4282, 4282, 129478882933697822879), (4283, 4283, 128196913795740418692), (4284, 4284, 126927637421525167022), (4285, 4285, 125670928140123927744), (4286, 4286, 124426661524875175984), (4287, 4287, 123194714381064530678), (4288, 4288, 121974964733727258097), (4289, 4289, 120767291815571542670), (4290, 4290, 119571576055021329376), (4291, 4291, 118387699064377553838), (4292, 4292, 117215543628096587958), (4293, 4293, 116054993691184740553), (4294, 4294, 114905934347707663914), (4295, 4295, 113768251829413528627), (4296, 4296, 112641833494468840225), (4297, 4297, 111526567816305782401), (4298, 4298, 110422344372579982575), (4299, 4299, 109329053834237606510), (4300, 4300, 108246587954690699515), (4301, 4301, 107174839559099702490), (4302, 4302, 106113702533762081673), (4303, 4303, 105063071815606021459), (4304, 4304, 104022843381788140058), (4305, 4305, 102992914239394198077), (4306, 4306, 101973182415241780275), (4307, 4307, 100963546945783940866), (4308, 4308, 99963907867112812739), (4309, 4309, 98974166205062190830), (4310, 4310, 97994223965408109733), (4311, 4311, 97023984124166445280), (4312, 4312, 96063350617986579485), (4313, 4313, 95112228334640177708), (4314, 4314, 94170523103604136345), (4315, 4315, 93238141686736768658), (4316, 4316, 92314991769046305602), (4317, 4317, 91400981949550797626), (4318, 4318, 90496021732228512501), (4319, 4319, 89600021517057933169), (4320, 4320, 88712892591146468485), (4321, 4321, 87834547119946998500), (4322, 4322, 86964898138561384653), (4323, 4323, 86103859543130083815), (4324, 4324, 85251346082307013678), (4325, 4325, 84407273348818825424), (4326, 4326, 83571557771107747944), (4327, 4327, 82744116605057176183), (4328, 4328, 81924867925799184339), (4329, 4329, 81113730619603152811), (4330, 4330, 80310624375844705754), (4331, 4331, 79515469679054164112), (4332, 4332, 78728187801043726844), (4333, 4333, 77948700793112600836), (4334, 4334, 77176931478329307758), (4335, 4335, 76412803443890403721), (4336, 4336, 75656241033554855169), (4337, 4337, 74907169340153321950), (4338, 4338, 74165514198171605891), (4339, 4339, 73431202176407530585), (4340, 4340, 72704160570700525332), (4341, 4341, 71984317396733193398), (4342, 4342, 71271601382904151879), (4343, 4343, 70565941963271437504), (4344, 4344, 69867269270565779707), (4345, 4345, 69175514129273049215), (4346, 4346, 68490608048785197242), (4347, 4347, 67812483216619007171), (4348, 7209, 67141072491701987298)]

def glob4 : ℕ := 7529223614670646417664

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3860, 0), (3861, 3861, 134488079724973769), (3862, 3862, 134588504470903865), (3863, 3863, 134718975179568287), (3864, 3864, 134880531977517966), (3865, 3865, 135074284838037316), (3866, 3866, 135301419064082506), (3867, 3867, 135563201299233332), (3868, 3868, 135860986126528511), (3869, 3869, 136196223322894167), (3870, 3870, 136570465845881832), (3871, 3871, 136985378639800189), (3872, 3872, 137442748360285013), (3873, 3873, 137944494130178467), (3874, 3874, 138492679455609003), (3875, 3875, 139089525449766785), (3876, 3876, 139737425533524113), (3877, 3877, 140438961807316910), (3878, 3878, 141196923318257411), (3879, 3879, 142014326481105523), (3880, 3880, 142894437952474520), (3881, 3881, 143840800305685412), (3882, 3882, 144857260910474753), (3883, 3883, 145948004489088549), (3884, 3884, 147117589900349182), (3885, 3885, 148370991798754927), (3886, 3886, 149713647929884174), (3887, 3887, 151151512960440728), (3888, 3888, 152691119906300321), (3889, 3889, 154339650421267850), (3890, 3890, 156105015450892475), (3891, 3891, 157995948049606818), (3892, 3892, 160022110518242678), (3893, 3893, 162194218458533324), (3894, 3894, 164524184881707092), (3895, 3895, 167025288175360251), (3896, 3896, 169712368559198349), (3897, 3897, 172602058687832928), (3898, 3898, 175713055341331278), (3899, 3899, 179066440750678882), (3900, 3900, 182686064124573043), (3901, 3901, 186598996490401618), (3902, 3902, 190836075182990191), (3903, 3903, 195432558398431803), (3904, 3904, 200428915417801681), (3905, 3905, 205871784701127856), (3906, 3906, 211815140434460308), (3907, 3907, 218321718742076002), (3908, 3908, 225464768186469230), (3909, 3909, 233330205945217771), (3910, 3910, 242019281694246138), (3911, 3911, 251651875986738599), (3912, 3912, 262370588321452123), (3913, 3913, 274345800075923040), (3914, 3914, 287781923743208980), (3915, 3915, 302925060989326780), (3916, 3916, 320072265262232435), (3917, 3917, 339582498066071421), (3918, 3918, 361889108838099057), (3919, 3919, 387513140587146259), (3920, 3920, 417075804497588868), (3921, 3921, 451306902563121484), (3922, 3922, 491043756362281758), (3923, 3923, 537212709734803357), (3924, 3924, 590783849499949212), (3925, 3925, 652691871583870273), (3926, 3926, 723725112159376435), (3927, 3927, 804400974631932592), (3928, 3928, 894862431825164005), (3929, 3929, 994833600579699355), (3930, 3930, 1103653848821816539), (3931, 3931, 1220378017556004327), (3932, 3932, 1343906421282717746), (3933, 3933, 1473106196509806400), (3934, 3934, 1606900620357495554), (3935, 3935, 1744321185103812009), (3936, 3936, 1884528875924302375), (3937, 3937, 2026814913508332507), (3938, 3938, 2170590187896166025), (3939, 3939, 2315369890147531687), (3940, 3940, 2460757238721634779), (3941, 3941, 2606428304834581150), (3942, 3942, 2752118767244911101), (3943, 3943, 2897612780567765837), (3944, 3944, 3042733826958352122), (3945, 3945, 3187337295394343942), (3946, 3946, 3331304505093563988), (3947, 3947, 3474537907502117770), (3948, 3948, 3616957236711825393), (3949, 3949, 3758496417132778624), (3950, 3950, 3899101073468684832), (3951, 3951, 4038726519204169167), (3952, 3952, 4177336125520168117), (3953, 3953, 4314899993249938994), (3954, 3954, 4451393866911395401), (3955, 3955, 4586798242774946103), (3956, 3956, 4721097633050368548), (3957, 3957, 4854279956193375878), (3958, 3958, 4986336029523627583), (3959, 3959, 5117259145193403229), (3960, 3960, 5247044714349777822), (3961, 3961, 5375689967325981578), (3962, 3962, 5503193700060090165), (3963, 3963, 5629556058810601281), (3964, 3964, 5754778356726376463), (3965, 3965, 5878862917015977606), (3966, 3966, 6001812938412934024), (3967, 3967, 6123632379398841566), (3968, 3968, 6244325858264240000), (3969, 3969, 6363898566588229510), (3970, 3970, 6482356194125485220), (3971, 3971, 6599704863422338904), (3972, 3972, 6715951072756605192), (3973, 3973, 6831101646220455053), (3974, 3974, 6945163689951108435), (3975, 3975, 7058144553667783277), (3976, 3976, 7170051796801080488), (3977, 3977, 7280893158607523745), (3978, 3978, 7390676531751111051), (3979, 3979, 7499409938908544592), (3980, 3980, 7607101512017778579), (3981, 3981, 7713759473842689208), (3982, 3982, 7819392121571681906), (3983, 3983, 7924007812206264305), (3984, 3984, 8027614949528142697), (3985, 3985, 8130221972461162562), (3986, 3986, 8231837344668168823), (3987, 3987, 8332469545243237261), (3988, 3988, 8432127060377247678), (3989, 3989, 8530818375889867480), (3990, 3990, 8628551970534055443), (3991, 3991, 8725336309990484526), (3992, 3992, 8821179841479076107), (3993, 3993, 8916090988923351703), (3994, 3994, 9010078148610724422), (3995, 3995, 9103149685298325298), (3996, 3996, 9195313928719620115), (3997, 3997, 9286579170452031607), (3998, 3998, 9376953661110134755), (3999, 3999, 9466445607832820321), (4000, 4000, 9555063172036192894), (4001, 4001, 9642814467406944142), (4002, 4002, 9729707558113570457), (4003, 4003, 9815750457215130963), (4004, 4004, 9900951125249304515), (4005, 4005, 9985317468983335866), (4006, 4006, 10068857340313089742), (4007, 4007, 10151578535296881882), (4008, 4008, 10233488793312049427), (4009, 4009, 10314595796323378017), (4010, 4010, 10394907168253535738), (4011, 4011, 10474430474446588840), (4012, 4012, 10553173221216503246), (4013, 4013, 10631142855473280148), (4014, 4014, 10708346764420042942), (4015, 4015, 10784792275314994739), (4016, 4016, 10860486655292707994), (4017, 4017, 10935437111239697018), (4018, 4018, 11009650789719665813), (4019, 4019, 11083134776944223007), (4020, 4020, 11155896098785216998), (4021, 4021, 11227941720825171774), (4022, 4022, 11299278548442600730), (4023, 4023, 11369913426929245283), (4024, 4024, 11439853141636529911), (4025, 4025, 11509104418148747982), (4026, 4026, 11577673922480695441), (4027, 4027, 11645568261297654192), (4028, 4028, 11712793982155795502), (4029, 4029, 11779357573761227543), (4030, 4030, 11845265466246051757), (4031, 4031, 11910524031459921174), (4032, 4032, 11975139583275711482), (4033, 4033, 12039118377908023287), (4034, 4034, 12102466614243332800), (4035, 4035, 12165190434180698733), (4036, 4036, 12227295922982016325), (4037, 4037, 12288789109630885862), (4038, 4038, 12349675967199233246), (4039, 4039, 12409962413220884833), (4040, 4040, 12469654310071358230), (4041, 4041, 12528757465353185582), (4042, 4042, 12587277632286136429), (4043, 4043, 12645220510101753813), (4044, 4044, 12702591744441660386), (4045, 4045, 12759396927759131023), (4046, 4046, 12815641599723465195), (4047, 4047, 12871331247626726339), (4048, 4048, 12926471306792446929), (4049, 4049, 12981067160985927055), (4050, 4050, 13035124142825781312), (4051, 4051, 13088647534196413798), (4052, 4052, 13141642566661124210), (4053, 4053, 13194114421875569554), (4054, 4054, 13246068232001325953), (4055, 4055, 13297509080119313591), (4056, 4056, 13348442000642865085), (4057, 4057, 13398871979730233583), (4058, 4058, 13448803955696351815), (4059, 4059, 13498242819423667181), (4060, 4060, 13547193414771890882), (4061, 4061, 13595660538986511111), (4062, 4062, 13643648943105931546), (4063, 4063, 13691163332367106795), (4064, 4064, 13738208366609556213), (4065, 4065, 13784788660677646559), (4066, 4066, 13830908784821042444), (4067, 4067, 13876573265093231433), (4068, 4068, 13921786583748038011), (4069, 4069, 13966553179634047565), (4070, 4070, 14010877448586867919), (4071, 4071, 14054763743819162001), (4072, 4072, 14098216376308390850), (4073, 4073, 14141239615182211384), (4074, 4074, 14183837688101478320), (4075, 4075, 14226014781640804182), (4076, 4076, 14267775041666635657), (4077, 4077, 14309122573712808569), (4078, 4078, 14350061443353547517), (4079, 4079, 14390595676573879716), (4080, 4080, 14430729260137435912), (4081, 4081, 14470466141951614293), (4082, 4082, 14509810231430086221), (4083, 4083, 14548765399852625317), (4084, 4084, 14587335480722243954), (4085, 4085, 14625524270119623573), (4086, 4086, 14663335527054827482), (4087, 4087, 14700772973816286847), (4088, 4088, 14737840296317052539), (4089, 4089, 14774541144438307330), (4090, 4090, 14810879132370134613), (4091, 4091, 14846857838949541434), (4092, 4092, 14882480807995735107), (4093, 4093, 14917751548642654077), (4094, 4094, 14952673535668755006), (4095, 4095, 14987250209824059274), (4096, 4096, 15021484978154463224), (4097, 4097, 15055381214323317560), (4098, 4098, 15088942258930282278), (4099, 4099, 15122171419827464466), (4100, 4100, 15155071972432847163), (4101, 4101, 15187647160041018269), (4102, 4102, 15219900194131209272), (4103, 4103, 15251834254672654239), (4104, 4104, 15283452490427280189), (4105, 4105, 15314758019249740566), (4106, 4106, 15345753928384804092), (4107, 4107, 15376443274762111817), (4108, 4108, 15406829085288315650), (4109, 4109, 15436914357136612129), (4110, 4110, 15466702058033685584), (4111, 4111, 15496195126544075238), (4112, 4112, 15525396472351981165), (4113, 4113, 15554308976540524306), (4114, 4114, 15582935491868476095), (4115, 4115, 15611278843044473482), (4116, 4116, 15639341826998735419), (4117, 4117, 15667127213152297078), (4118, 4118, 15694637743683778298), (4119, 4119, 15721876133793702936), (4120, 4120, 15748845071966385971), (4121, 4121, 15775547220229405355), (4122, 4122, 15801985214410675737), (4123, 4123, 15828161664393141329), (4124, 4124, 15854079154367105249), (4125, 4125, 15879740243080212796), (4126, 4126, 15905147464085106186), (4127, 4127, 15930303325984768323), (4128, 4128, 15955210312675573254), (4129, 4129, 15979870883588060994), (4130, 4130, 16004287473925454426), (4131, 4131, 16028462494899936026), (4132, 4132, 16052398333966702145), (4133, 4133, 16076097355055812627), (4134, 4134, 16099561898801853492), (4135, 4135, 16122794282771430427), (4136, 4136, 16145796801688510824), (4137, 4137, 16168571727657632027), (4138, 4138, 16191121310384993484), (4139, 4139, 16213447777397450412), (4140, 4140, 16235553334259426550), (4141, 4141, 16257440164787763561), (4142, 4142, 16279110431264524529), (4143, 4143, 16300566274647768994), (4144, 4144, 16321809814780316885), (4145, 4145, 16342843150596518621), (4146, 4146, 16363668360327048630), (4147, 4147, 16384287501701739414), (4148, 4148, 16404702612150473235), (4149, 4149, 16424915709002148411), (4150, 4150, 16444928789681737136), (4151, 4151, 16464743831905451622), (4152, 4152, 16484362793874035325), (4153, 4153, 16503787614464195862), (4154, 4154, 16523020213418196196), (4155, 4155, 16542062491531620514), (4156, 4156, 16560916330839331171), (4157, 4157, 16579583594799632946), (4158, 4158, 16598066128476660771), (4159, 4159, 16616365758721006979), (4160, 4160, 16634484294348604028), (4161, 4161, 16652423526317878542), (4162, 4162, 16670185227905192417), (4163, 4163, 16687771154878586607), (4164, 4164, 16705183045669843148), (4165, 4165, 16722422621544880799), (4166, 4166, 16739491586772499651), (4167, 4167, 16756391628791489863), (4168, 4168, 16773124418376119648), (4169, 4169, 16789691609800017471), (4170, 4170, 16806094840998463324), (4171, 4171, 16822335733729103855), (4172, 4172, 16838415893731105970), (4173, 4173, 16854336910882763459), (4174, 4174, 16870100359357571066), (4175, 4175, 16885707797778780303), (4176, 4176, 16901160769372451220), (4177, 4177, 16916460802119014197), (4178, 4178, 16931609408903355749), (4179, 4179, 16946608087663442200), (4180, 4180, 16961458321537494968), (4181, 4181, 16976161579009731104), (4182, 4182, 16990719314054682618), (4183, 4183, 17005132966280107991), (4184, 4184, 17019403961068509195), (4185, 4185, 17033533709717267395), (4186, 4186, 17047523609577410436), (4187, 4187, 17061375044191025070), (4188, 4188, 17075089383427326800), (4189, 4189, 17088667983617400086), (4190, 4190, 17102112187687621559), (4191, 4191, 17115423325291778789), (4192, 4192, 17128602712941897022), (4193, 4193, 17141651654137786219), (4194, 4194, 17154571439495320609), (4195, 4195, 17167363346873462861), (4196, 4196, 17180028641500044877), (4197, 4197, 17192568576096317114), (4198, 4198, 17204984391000278215), (4199, 4199, 17217277314288796643), (4200, 4200, 17229448561898535904), (4201, 4201, 17241499337745694841), (4202, 4202, 17253430833844574379), (4203, 4203, 17265244230424981993), (4204, 4204, 17276940696048485089), (4205, 4205, 17288521387723524364), (4206, 4206, 17299987451019398125), (4207, 4207, 17311340020179128447), (4208, 4208, 17322580218231219947), (4209, 4209, 17333709157100321861), (4210, 4210, 17344727937716803994), (4211, 4211, 17355637650125257057), (4212, 4212, 17366439373591927754), (4213, 4213, 17377134176711098936), (4214, 4214, 17387723117510425024), (4215, 4215, 17398207243555232791), (4216, 4216, 17408587592051797554), (4217, 4217, 17418865189949604658), (4218, 4218, 17429041054042606120), (4219, 4219, 17439116191069482153), (4220, 4220, 17449091597812917229), (4221, 4221, 17458968261197900241), (4222, 4222, 17468747158389058234), (4223, 4223, 17478429256887033090), (4224, 4224, 17488015514623910475), (4225, 4225, 17497506880057710230), (4226, 4226, 17506904292265947366), (4227, 4227, 17516208681038272668), (4228, 4228, 17525420966968201888), (4229, 4229, 17534542061543942377), (4230, 4230, 17543572867238325957), (4231, 4231, 17552514277597856722), (4232, 4232, 17561367177330882406), (4233, 4233, 17570132442394897845), (4234, 4234, 17578810940082988996), (4235, 4235, 17587403529109425902), (4236, 4236, 17595911059694412883), (4237, 4237, 17604334373648004197), (4238, 4238, 17612674304453193303), (4239, 4239, 17620931677348183796), (4240, 4240, 17629107309407849992), (4241, 4241, 17637202009624395105), (4242, 4242, 17645216578987214822), (4243, 4243, 17653151810561974066), (4244, 4244, 17661008489568904616), (4245, 4245, 17668787393460331220), (4246, 4246, 17676489291997433735), (4247, 4247, 17684114947326252757), (4248, 4248, 17691665114052946164), (4249, 4249, 17699140539318303883), (4250, 4250, 17706541962871528144), (4251, 4251, 17713870117143286420), (4252, 4252, 17721125727318044158), (4253, 4253, 17728309511405684374), (4254, 4254, 17735422180312421077), (4255, 4255, 17742464437911013452), (4256, 4256, 17749436981110287652), (4257, 4257, 17756340499923972978), (4258, 4258, 17763175677538859175), (4259, 4259, 17769943190382281496), (4260, 4260, 17776643708188940126), (4261, 4261, 17783277894067060489), (4262, 4262, 17789846404563900912), (4263, 4263, 17796349889730614042), (4264, 4264, 17802788993186468359), (4265, 4265, 17809164352182436058), (4266, 4266, 17815476597664153534), (4267, 4267, 17821726354334260609), (4268, 4268, 17827914240714124618), (4269, 4269, 17834040869204955378), (4270, 4270, 17840106846148317037), (4271, 4271, 17846112771886042713), (4272, 4272, 17852059240819557799), (4273, 4273, 17857946841468617735), (4274, 4274, 17863776156529466009), (4275, 4275, 17869547762932418077), (4276, 4276, 17875262231898876843), (4277, 4277, 17880920128997785302), (4278, 4278, 17886522014201521847), (4279, 4279, 17892068441941243755), (4280, 4280, 17897559961161684254), (4281, 4281, 17902997115375408550), (4282, 4282, 17908380442716534142), (4283, 4283, 17913710475993920680), (4284, 4284, 17918987742743834599), (4285, 4285, 17924212765282093688), (4286, 4286, 17929386060755696705), (4287, 4287, 17934508141193943119), (4288, 4288, 17939579513559047988), (4289, 4289, 17944600679796256939), (4290, 4290, 17949572136883466173), (4291, 4291, 17954494376880352373), (4292, 4292, 17959367886977017333), (4293, 4293, 17964193149542152080), (4294, 4294, 17968970642170725237), (4295, 4295, 17973700837731200297), (4296, 4296, 17978384204412286446), (4297, 4297, 17983021205769227547), (4298, 4298, 17987612300769633812), (4299, 4299, 17992157943838860674), (4300, 4300, 17996658584904939330), (4301, 4301, 18001114669443063354), (4302, 4302, 18005526638519635767), (4303, 4303, 18009894928835880888), (4304, 4304, 18014219972771025260), (4305, 4305, 18018502198425051887), (4306, 4306, 18022742029661032002), (4307, 4307, 18026939886147038518), (4308, 4308, 18031096183397645286), (4309, 4309, 18035211332815016251), (4310, 4310, 18039285741729588542), (4311, 4311, 18043319813440353495), (4312, 4312, 18047313947254739585), (4313, 4313, 18051268538528101182), (4314, 4314, 18055183978702817017), (4315, 4315, 18059060655347002221), (4316, 4316, 18062898952192837722), (4317, 4317, 18066699249174520803), (4318, 4318, 18070461922465840531), (4319, 4319, 18074187344517381777), (4320, 4320, 18077875884093361475), (4321, 4321, 18081527906308100762), (4322, 4322, 18085143772662136572), (4323, 4323, 18088723841077976269), (4324, 4324, 18092268465935498804), (4325, 4325, 18095777998107005919), (4326, 4326, 18099252784991926827), (4327, 4327, 18102693170551179794), (4328, 4328, 18106099495341194019), (4329, 4329, 18109472096547595140), (4330, 4330, 18112811308018557713), (4331, 4331, 18116117460297827932), (4332, 4332, 18119390880657419849), (4333, 4333, 18122631893129988322), (4334, 4334, 18125840818540881871), (4335, 4335, 18129017974539878616), (4336, 4336, 18132163675632608410), (4337, 4337, 18135278233211664277), (4338, 4338, 18138361955587406209), (4339, 4339, 18141415148018460379), (4340, 4340, 18144438112741916753), (4341, 4341, 18147431149003228098), (4342, 4342, 18150394553085813324), (4343, 4343, 18153328618340368086), (4344, 4344, 18156233635213885523), (4345, 4345, 18159109891278390017), (4346, 4346, 18161957671259386791), (4347, 4347, 18164777257064030150), (4348, 7209, 18446744073709430713)]

def glob5 : ℕ := 19972754393270891628

/-- Every run of kind `k` is ordered, sound and below the global fee. -/
def runsOk (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G : ℕ) : Bool :=
  runs.all fun e => decide (e.1 ≤ e.2.1) && okOf k rcPar (lowerQ rcPar.g e.1) (upperQ rcPar.g e.2.1) e.2.2 &&
    decide (e.2.2 ≤ G)

theorem runs0_ok : runsOk 0 runs0 glob0 = true := by decide +kernel
theorem runs1_ok : runsOk 1 runs1 glob1 = true := by decide +kernel
theorem runs2_ok : runsOk 2 runs2 glob2 = true := by decide +kernel
theorem runs3_ok : runsOk 3 runs3 glob3 = true := by decide +kernel
theorem runs4_ok : runsOk 4 runs4 glob4 = true := by decide +kernel

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

section Cap776Arithmetic
set_option debug.skipKernelTC false
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
namespace SigGolfResearch.AffineBound
open Finset Polynomial
open scoped BigOperators
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.N600

theorem interpolate {f : ℝ → ℝ} (a b L U x : ℝ)
    (hconv : ∀ t, 0 ≤ t → t ≤ 1 →
      f ((1-t)*L+t*U) ≤ (1-t)*f L+t*f U)
    (hL : f L ≤ a*L+b) (hU : f U ≤ a*U+b)
    (hxL : L ≤ x) (hxU : x ≤ U) : f x ≤ a*x+b := by
  rcases eq_or_lt_of_le (hxL.trans hxU) with heq | hlt
  · have hx : x = L := by linarith
    simpa only [hx] using hL
  · let t := (x-L)/(U-L)
    have hd : 0 < U-L := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hx : x=(1-t)*L+t*U := by dsimp only [t]; field_simp; ring
    have hc := hconv t ht0 ht1
    have h1 := mul_le_mul_of_nonneg_left hL (show 0 ≤ 1-t by linarith)
    have h2 := mul_le_mul_of_nonneg_left hU ht0
    rw [hx]
    nlinarith

theorem scarf_line (θ m vv a b L U x : ℝ) (hv : 0 ≤ vv)
    (hL : ClaudeWCT.Numerics.RouteC.scarf (θ-L) m vv ≤ a*L+b)
    (hU : ClaudeWCT.Numerics.RouteC.scarf (θ-U) m vv ≤ a*U+b)
    (hxL : L ≤ x) (hxU : x ≤ U) :
    ClaudeWCT.Numerics.RouteC.scarf (θ-x) m vv ≤ a*x+b := by
  exact interpolate (f := fun z => ClaudeWCT.Numerics.RouteC.scarf (θ-z) m vv) a b L U x
    (fun t h0 h1 => ClaudeWCT.Numerics.RouteCFees.scarf_affine θ m vv L U t hv h0 h1)
    hL hU hxL hxU

theorem histogram_rebate {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (P F : ℕ[X])
    (hP : CoeffLE P (weightedHistogram good bin (fun _ => 1)))
    (hF : CoeffLE F (weightedHistogram good bin weight))
    (N : Nat) (a b : Nat → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j ∈ range N, (a j*(P.coeff j : ℝ)+b j*(F.coeff j : ℝ))) ≤
      ∑ x : α, if good x ∧ bin x < N then a (bin x)+b (bin x)*(weight x : ℝ) else 0 := by
  classical
  have hp (j : Nat) : (P.coeff j : ℝ) ≤
      ∑ x : α, if good x ∧ bin x=j then (1 : ℝ) else 0 := by
    have h := hP j
    rw [weightedHistogram_coeff] at h
    exact_mod_cast h
  have hf (j : Nat) : (F.coeff j : ℝ) ≤
      ∑ x : α, if good x ∧ bin x=j then (weight x : ℝ) else 0 := by
    have h := hF j
    rw [weightedHistogram_coeff] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ j ∈ range N,
        (a j*(∑ x : α, if good x ∧ bin x=j then (1 : ℝ) else 0)+
        b j*(∑ x : α, if good x ∧ bin x=j then (weight x : ℝ) else 0)) := by
      exact sum_le_sum fun j _ => add_le_add (mul_le_mul_of_nonneg_left (hp j) (ha j))
        (mul_le_mul_of_nonneg_left (hf j) (hb j))
    _ = ∑ x : α, if good x ∧ bin x < N then a (bin x)+b (bin x)*(weight x : ℝ) else 0 := by
      simp_rw [mul_sum, ←sum_add_distrib]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      by_cases hg : good x
      · by_cases hbin : bin x < N
        · rw [if_pos ⟨hg,hbin⟩]
          rw [sum_eq_single (bin x)]
          · simp [hg]
          · intro j _ hj
            simp [hg, Ne.symm hj]
          · simp [mem_range, hbin]
        · rw [if_neg (by simp [hbin])]
          apply sum_eq_zero
          intro j hj
          have hn : bin x ≠ j := by intro he; rw [he] at hbin; exact hbin (mem_range.mp hj)
          simp [hg,hn]
      · simp [hg]

open ClaudeWCT.Numerics.RouteCFees

def affinePointOk (P : Par) (x y : ℚ) : Bool :=
  let w := P.m-P.θ+x
  let t := 2*y-w
  decide (0≤t) && decide (w*w+P.vv≤t*t)

theorem affinePoint_sound (P : Par) (x y : ℚ) (h : affinePointOk P x y=true) :
    ClaudeWCT.Numerics.RouteC.scarf (P.θ-x) P.m P.vv ≤ (y : ℝ) := by
  unfold affinePointOk at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  have h0 : (0 : ℝ)≤2*(y : ℝ)-(P.m-P.θ+x) := by exact_mod_cast h.1
  have h1 : ((P.m : ℝ)-P.θ+x)*((P.m : ℝ)-P.θ+x)+P.vv ≤
      (2*(y : ℝ)-((P.m : ℝ)-P.θ+x))*(2*(y : ℝ)-((P.m : ℝ)-P.θ+x)) := by exact_mod_cast h.2
  have hs : Real.sqrt (((P.m : ℝ)-P.θ+x)^2+P.vv)≤2*(y : ℝ)-(P.m-P.θ+x) := by
    rw [Real.sqrt_le_left h0]
    nlinarith
  unfold ClaudeWCT.Numerics.RouteC.scarf
  have he : (P.m : ℝ)-(P.θ-x)=P.m-P.θ+x := by ring
  rw [he]
  linarith

theorem affineInterval_sound (P : Par) (L U a b : ℚ) (hv : 0≤(P.vv : ℝ))
    (hL : affinePointOk P L (a*L+b)=true) (hU : affinePointOk P U (a*U+b)=true)
    (x : ℝ) (hxL : (L : ℝ)≤x) (hxU : x≤(U : ℝ)) :
    ClaudeWCT.Numerics.RouteC.scarf (P.θ-x) P.m P.vv ≤ (a : ℝ)*x+b := by
  have h1 := affinePoint_sound P L (a*L+b) hL
  have h2 := affinePoint_sound P U (a*U+b) hU
  push_cast at h1 h2
  exact scarf_line P.θ P.m P.vv a b L U x hv h1 h2 hxL hxU

theorem scarf_le_price (P : Par) (hc : 0≤(P.c0 : ℝ))
    (hd : 0≤(P.θ : ℝ)-P.m) (hv : (P.vv : ℝ)≤4*P.c0*(P.θ-P.m))
    (x : ℝ) (hx : 0≤x) : costScarf P x≤x := by
  unfold costScarf
  split_ifs with h
  · have hh : 0≤x+((P.θ : ℝ)-P.m) := by linarith
    have hs : Real.sqrt (((P.m : ℝ)-(P.θ-x))^2+P.vv)≤x+(P.θ-P.m) := by
      rw [Real.sqrt_le_left hh]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt h)) hd]
    unfold ClaudeWCT.Numerics.RouteC.scarf
    linarith
  · exact hx

theorem sum_cost_rebate {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (P F : ℕ[X])
    (hP : CoeffLE P (weightedHistogram good bin (fun _ => 1)))
    (hF : CoeffLE F (weightedHistogram good bin weight))
    (N : Nat) (a b : Nat → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (cost : α → ℝ) (G κ : ℝ)
    (hglobal : ∀ x, cost x ≤ G*κ*(weight x : ℝ))
    (hlocal : ∀ x, good x → bin x<N →
      cost x + a (bin x) + b (bin x)*(weight x : ℝ) ≤ G*κ*(weight x : ℝ)) :
    (∑ x, cost x) + (∑ j ∈ range N, (a j*(P.coeff j : ℝ)+b j*(F.coeff j : ℝ))) ≤
      G*κ*(∑ x, (weight x : ℝ)) := by
  classical
  have hr := histogram_rebate good bin weight P F hP hF N a b ha hb
  have hs : (∑ x, cost x) +
      (∑ x : α, if good x ∧ bin x<N then a (bin x)+b (bin x)*(weight x : ℝ) else 0) ≤
      ∑ x, G*κ*(weight x : ℝ) := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro x _
    by_cases h : good x ∧ bin x<N
    · rw [if_pos h]
      have := hlocal x h.1 h.2
      linarith
    · rw [if_neg h,add_zero]
      exact hglobal x
  rw [←mul_sum] at hs
  linarith

end SigGolfResearch.AffineBound
namespace SigGolfResearch.RebateData
open ClaudeWCT.Numerics.RouteCFees
open SigGolfResearch.AffineBound
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
def P : Par := ⟨826, (27/50 : ℚ), (10 : ℚ), (31929671/16000000 : ℚ), (19669/20000 : ℚ), (41661/5000000 : ℚ), (912809/10000000 : ℚ)⟩
def entries : List (Nat×Nat) := [(18297256800077370093, 0), (18295057564460428228, 101893667584318278949897626461135), (18291931232930721783, 244960345895485973428203365808898), (18288674817612886418, 395457614343833516073589663313820), (18285280774419717098, 553870495061478664856996417023146), (18281740995156899877, 720722908677420909823243687791038), (18278046755761970452, 896581412513691004411433210815612), (18274188658900552001, 1082059359977300174891995098333774), (18270156570205627349, 1277821535809000397051615079356392), (18265939547342431492, 1484589329902978182593238094290677), (18261525760961607341, 1703146521795626871574714670704725), (18256902406463514816, 1934345758880728970255843116665583), (18252055605333380205, 2179115824236324574748174807773192), (18246970294615940529, 2438469804999065168988032410279191), (18241630102874097353, 2713514289922490414080304402961875), (18236017210712463916, 3005459745624433114901196397318406), (18230112193635831544, 3315632245695036680101914331268773), (18223893844645090915, 3645486756067521477480493786752184), (18217338973537554901, 3996622214785934171239130342587652), (18210422179360923995, 4370798685686095327344447444276780), (18203115591853123509, 4769956914949525020980514199170297), (18195388576962783339, 5196240678735872903744682376358517), (18187207400661148490, 5652022381300068052012609278467886), (18178534844193435895, 6139932448826880794246741597712089), (18169329762636046052, 6662893167991926799228805482446197), (18159546577075747274, 7224157744134533334197551597176071), (18149134688845731871, 7827355507102396261430407954321738), (18138037801963344050, 8476544379831661334569035233301530), (18126193137117385410, 9176271953790459494706044426506302), (18113530517125883719, 9931646796945206858748364302648639), (18099971299572299978, 10748421967101105817714440346941129), (18085427127132138853, 11633093133096017047662961341806043), (18069798459672597921, 12593014239771494691613744977208748), (18052972844227202010, 13636534317219078890837892800778514), (18034822869010590454, 14773159865454961517757579720847153), (18015203735230469949, 16013748287188585254684205171783883), (17993950364918531592, 17370739151103415191431443842055259), (17970873943507161750, 18858431719538462755013111481001197), (17945757771370703751, 20493319261506886988062890617387776), (17918352267705358899, 22294493313952075547353399127692892), (17888368931295761923, 24284134401559383449847485862431828), (17855473013900143396, 26488109965782897345576218001370400), (17819274600794984154, 28936705615709652889430548527748038), (17779317716754812053, 31665522566673738347997828275723409), (17735066981607882528, 34716582576982599404073449403920364), (17685891225142240246, 38139692125400655976571800444953692), (17631043335732208778, 41994130208114405378437948479677518), (17569635463569819179, 46350738947605860943585007565808879), (17500608538696313434, 51294512613643398506714756776909938), (17422694922471127262, 56927796929026780583023299173979854), (17334372943681378494, 63374222737869077652905944894191090), (17233812183003279280, 70783498298507547740172628458890702), (17118808853797688262, 79337157684877743051982244741407918), (16986711811942520508, 89255282656544055425381269539372206), (16834342139442343648, 100804038325030713527727744762263837), (16657913652813474854, 114303523288128092529996899534602657), (16452969028024506131, 130134847324372568318405556263441503), (16214357246698855262, 148744435615553553230671174817259932), (15936292260966605548, 170642324990537091497606172705454010), (15612546424108018551, 196389921645859039968553639742350469), (15236835819159081340, 226572065888064867493314615492325426), (14803432277001338523, 261749608018005940330194638242689191), (14307973534922524615, 302393429281225020831751815414456967), (13748343292086775189, 348808903983224472800526440511370575), (13125401302229202772, 401067933942761818472152679507307282), (12443333492032673519, 458967908820363479800381520006945844), (11709505075675396757, 522029214758785811657931687585386141), (10933885488200901620, 589528394468504066598605308808839274), (10128256346262506479, 660551852717567978116478338249322922), (9305432082262570224, 734052209628056042419414442095414107), (8478633834640934326, 808895630511277980068205907370504606), (7661035443751819458, 883898162720267871104436536005643452), (6865408878726476419, 957857091309582503659126943164525169), (6103759485669630968, 1029587123945942261252807677661178610), (5386860389308110168, 1097970091942859500877964353320023413), (4723665124407953878, 1162020591250436868041466933803473120), (4120681546553587567, 1220959629952045994897078819023104439), (3581483687260787671, 1274278090827075507608435772518609809), (3106555719612965798, 1321768616819803100378315195009100223), (2693567413952238461, 1363512986065848192805599576343142487), (2338018246060937887, 1399828541444033018660400913688831846), (2034060244054804820, 1431191438878881236686365666500286340), (1775288375643753783, 1458158349891123214121051443460084564), (1555357177201490532, 1481302321146577134725051264415234665), (1368378280582340229, 1501169035693550000589742655574204683), (1209123258408126956, 1518252306689530282441073150464824680), (1073085777954992042, 1532984109499889453272972172824722222), (956457565166473215, 1545733964458161736182914203467601204), (856060224537513233, 1556813469962831001758698452403982584), (769260478529858547, 1566483119949549309102634999534941508), (693884681411272364, 1574959681896388166110148345299194576), (628140514025237950, 1582423217439645926994862269536102045), (570548965490291667, 1589023332270245560414161473378633034), (519887086719351995, 1594884529469012788066720111536842053), (475140728607813965, 1600110689078368321725933512232208388), (435465973785458373, 1604788763592795599554413970622492190), (400157870640716833, 1608991801120859881885557953617213757), (368625169830446832, 1612781407368691310416284644609245054), (340369930684278940, 1616209746829282102987228637532725260), (314971048420556543, 1619321169314467905659507107555520765), (292070925198403840, 1622153533566464833478888691758205605), (271364657886546193, 1624739286619531006134516949138485144), (252591240654487881, 1627106346368640061660566453113105523), (235526382605542341, 1629278825482859003322591300303422103), (219976622703393630, 1631277627206120176451938744580494633), (205774489548393104, 1633120937472230504415830317471104226), (192774505276354576, 1634824632871770547116035974313202517), (180849873700888593, 1636402620115854263190140530422943676), (169889725057850516, 1637867119548285548737346810660025239), (159796815164126147, 1639228902800224296123296886965297065), (150485596927987143, 1640497492727848266278264679970846855), (141880598092542149, 1641681332218005334414045194450913931), (133915051757553573, 1642787927205755208030737060008310616), (126529736311648941, 1643823968254969643951889520144808884), (119671989465839124, 1644795434256869582032934867395287801), (113294867538768172, 1645707681160737648680334270097111963), (107356426338925484, 1646565518134012768236466168942151300), (101819104180920425, 1647373273130355664993918786275888387), (96649190967020349, 1648134849504229254685726977090376626), (91816370022675772, 1648853775033410628335518770657582545), (87293321622678934, 1649533244484259115955890516828103757), (83055378983237324, 1650176156668688925916539331942228935), (79080229004077457, 1650785146788827507771444403259689260), (75347651286903241, 1651362614739055849916129175905970360), (71839289982489681, 1651910749930544469311272171659820111), (68538453868686557, 1652431553116523740184629627994748534), (65429940767966131, 1652926855624144581423463567986627346), (62499883001895744, 1653398336338300502662079452720069899), (59735611072061715, 1653847536732093767437437232421075111), (57125533169533705, 1654275874196030982054807629808010325), (54659028461765436, 1654684653882137264915578248173637261), (52326352398145505, 1655075079248848230555880341987819742), (50118552522450389, 1655448261466845418922674033546030140), (48027393489759004, 1655805227824179485142045065234310278), (46045290163170117, 1656146929250446940360259114156711400), (44165247817035758, 1656474247063930413679391192277471781), (42380808602614199, 1656787999032048434912574533717982317), (40686003542559802, 1657088944823830740914578500437706373), (39075309415416482, 1657377790923141052680143210263725425), (37543609972693409, 1657655195062762331697284082390221961), (36086161001202351, 1657921770232031444449968124242416676), (34698558803822950, 1658178088304286215308560152095356235), (33376711724159243, 1658424683324821085198161069977583129), (32116814385856169, 1658662054495214149597873467642438110), (30915324356668889, 1658890668885683574542678674155644303), (29768940981574105, 1659110963903466672567449664854440304), (28674586159004457, 1659323349542015069388948508185227372), (27629386860287911, 1659528210433000465070576910919825289), (26630659215105954, 1659725907720673003855920666531411821), (25675894005692017, 1659916780775961690966784972774169888), (24762743429954751, 1660101148765813829040969476793678739), (23889009009054488, 1660279312091603971869930255341541466), (23052630528464010, 1660451553708973105794084584969948570), (22251675913445854, 1660618140340160456834424992018410295), (21484331950383566, 1660779323588741751713496157743750453), (20748895774691055, 1660935340965670167204869635455083891), (20043767054245539, 1661086416834613352145364914098773234), (19367440804578121, 1661232763283777735059900566693733662), (18718500778526345, 1661374580930697630836013563212564878), (18095613378804923, 1661512059665830820796748181416672681), (17497522047070568, 1661645379340235062654959294867319067), (16923042087619923, 1661774710402093333277924030036001544), (16371055887931573, 1661900214486402481348702332159605453), (15840508501901388, 1662022044961734214227112564173280753), (15330403564875114, 1662140347437613572488846361182779066), (14839799512497060, 1662255260235733527734660104529868312), (14367806078007441, 1662366914827930920252995401857849731), (13913581044967181, 1662475436243584978981022729880095347), (13476327234497495, 1662580943448861918470270051240092975), (13055289708018462, 1662683549700014747641739271266862821), (12649753168179201, 1662783362872753946245483522529250928), (12259039542212415, 1662880485769529850579808211092328016), (11882505733336047, 1662975016406409477824525721244918765), (11519541527080463, 1663067048281087368874282235025966947), (11169567640555012, 1663156670623440299153309250692797120), (10832033903695593, 1663243968629918024005201743631825729), (10506417562465969, 1663329023682955369862235968199235377), (10192221694829982, 1663411913556493868053092787407865291), (9888973731078251, 1663492712608612786219846968940473720), (9596224070789206, 1663571491962188978441807605040374870), (9313544789337475, 1663648319674431676984136383193094776), (9040528427438760, 1663723260896071495363283598363291554), (8776786857745220, 1663796378020921885737067119566786754), (8521950222983722, 1663867730826475539266991823449941918), (8275665940565840, 1663937376606147238883786142817721611), (8037597768997003, 1664005370293728023365742928847541919), (7807424931776358, 1664071764580572798535777211696671237), (7584841294811980, 1664136610026004374680232370737576327), (7369554593680825, 1664199955161380993893758683152337442), (7161285707342018, 1664261846588241443943133098687631462), (6959767975167921, 1664322329070911572079438299323063676), (6764746554392092, 1664381445623928174334337710520597715), (6575977815288701, 1664439237594610627517372759685560008), (6393228771595806, 1664495744741087057296536284100830222), (6216276543876755, 1664551005306060119791243004136409194), (6044907853681263, 1664605056086577456036937255879186351), (5878918546521687, 1664657932500053413421273310411893067), (5718113141821775, 1664709668646771584098687982191362598), (5562304408125895, 1664760297369081967910386347617915828), (5411312961977199, 1664809850307492017814388587370199224), (5264966888984435, 1664858357953837370438047797026733521), (5123101385699727, 1664905849701705613148253566886693800), (4985558421024555, 1664952353894274910052594168993330398), (4852186415948808, 1664997897869718627905165640708869943), (4722839940508929, 1665042508004317200857852082919692837), (4597379426926202, 1665086209753409288173926626217001638), (4475670897955772, 1665129027690305754588841560284209038), (4357585709541387, 1665170985543282087026118675405917675), (4243000306930555, 1665212106230757506346156434250772125), (4131795993460213, 1665252411894762195236682905005587788), (4023858711274399, 1665291923932787703415360044056047285), (3919078833283137, 1665330663028109672502411607989607266), (3817350965716119, 1665368649178666511754887157156649848), (3718573760665962, 1665405901724572521611053265416935961), (3622649738054159, 1665442439374339176461883572079994698), (3529485116488525, 1665478280229873815325751535676904840), (3438989652514128, 1665513441810320825321569470159725127), (3351076487790630, 1665547941074806516092888174749495803), (3265662003757775, 1665581794444145253453101188363186775), (3182665683377643, 1665615017821561028916760509076364367), (3102009979567327, 1665647626612475471329878382358402694), (3023620189959084, 1665679635743410341724254597163529449), (2947424337646843, 1665711059680049778231935853317142836), (2873353057598337, 1665741912444504960961687682631654138), (2801339488431165, 1665772207631821434743856520653193084), (2731319169268926, 1665801958425767049120718424761011387), (2663229941410187, 1665831177613936339290079312553376970), (2597011854558661, 1665859877602205169089987062584641872), (2532607077377527, 1665888070428567578462827902505472824), (2469959812144503, 1665915767776385014751342795798365452), (2409016213297056, 1665942980987076471869684046649281729), (2349724309669140, 1665969721072276506641827452448452555), (2292033930232081, 1665995998725486640714628700929177641), (2235896633162761, 1666021824333244283224466044943806957), (2181265638072174, 1666047207985832018061691196042586365), (2128095761236671, 1666072159487548884784465085634405455), (2076343353682954, 1666096688366564139011257301864787432), (2025966241986058, 1666120803884372901848370150494495342), (1976923671647258, 1666144515044872094288421266440467385), (1929176252926050, 1666167830603074097550464920686064245), (1882685909007193, 1666190759073474680302084618625227802), (1837415826390157, 1666213308738090885144425219449602567), (1793330407394364, 1666235487654183766426124403672860786), (1750395224679275, 1666257303661680116374588279616851952), (1708576977683697, 1666278764390306603889793194323574486), (1667843450893732, 1666299877266449077522293767461514741), (1628163473853502, 1666320649519749148713925748707597510), (1589506882837281, 1666341088189449571039762305191876218), (1551844484105825, 1666361200130499363826903211682940465), (1515148018673731, 1666380992019429092153311779530596985), (1479390128518325, 1666400470360006207991861694460689991), (1444544324164181, 1666419641488679877425562984513312535), (1410584953580675, 1666438511579824264796512922678853671), (1377487172333138, 1666457086650788814844886674472666079), (1345226914931152, 1666475372566763666923918777270867639), (1313780867320364, 1666493375045467949911536692076218580), (1283126440466815, 1666511099661668341232607803825012711), (1253241744985342, 1666528551851534927289713294226398674), (1224105566765955, 1666545736916841074480232895737638215), (1195697343554371, 1666562660029013708826833338377097859), (1167997142444985, 1666579326233040107104380624895159191), (1140985638246621, 1666595740451237022305422003437707421), (1114644092683256, 1666611907486887700500731984052850008), (1088954334393786, 1666627832027752093824784067728996261), (1063898739696559, 1666643518649455334700552160118061028), (1039460214086060, 1666658971818759308811108527695210169), (1015622174430665, 1666674195896721948066656094296520516), (992368531841825, 1666689195141748659283999865986630956), (969683675186456, 1666703973712540108907063328396905391), (947552455215601, 1666718535670940398302504989039851704), (925960169283674, 1666732884984689487446768013568635502), (904892546633815, 1666747025530083556693289634175963280), (884335734225955, 1666760961094546836312783367885199868), (864276283085304, 1666774695379118281203764021502463659), (844701135149969, 1666788232000856323168025112848056924), (825597610597367, 1666801574495164795053192040173557495), (806953395630019, 1666814726318042989520281693183295268), (788756530702197, 1666827690848262689857493801790185445), (770995399169687, 1666840471389474890810644171843716115), (753658716345762, 1666853071172248813532256359659184486), (736735518947160, 1666865493356045710178912276317873510), (720215154914633, 1666877741031129850139572863991757854), (704087273593238, 1666889817220418981100795288616664256), (688341816258261, 1666901724881276463906797740403984237), (672969006973220, 1666913466907247190225144474150809449), (657959343767018, 1666925046129739306166922765146234995), (643303590117849, 1666936465319653683029894289391022013), (628992766732002, 1666947727188962998041521605360027577), (615018143606223, 1666958834392242213193704096654166484), (601371232362754, 1666969789528152168810019940200304322), (588043778846649, 1666980595140877940206009519697803861), (575027755975399, 1666991253721523540539000274837546455), (562315356831312, 1667001767709464490549812261899457236), (549898987987499, 1667012139493659716235776595372986587), (537771263058695, 1667022371413924178431513124592107291), (525924996468507, 1667032465762163583686391558069612739), (514353197425036, 1667042424783572473597570041492093624), (503049064097126, 1667052250677796939773115845414098449), (492005977983854, 1667061945600063163754890776516281362), (481217498470130, 1667071511662272935425010693534299848), (470677357561592, 1667080950934067259557297487347728103), (460379454792254, 1667090265443859118165633315584044156), (450317852298619, 1667099457179836416058499723225738928), (440486770054233, 1667108528090936098451583945581710189), (430880581258886, 1667117480087790392540615647104785843), (421493807876900, 1667126315043646089520899646896635927), (412321116319174, 1667135034795257749588349023917219320), (403357313263848, 1667143641143755679902690558493101908), (394597341610669, 1667152135855489504273693193706997171), (386036276564315, 1667160520662848113385656859399593705), (377669321842143, 1667168797265056755646838854138103447), (369491806001972, 1667176967328952001184625430879351767), (361499178885720, 1667185032489735285052359382893119133), (353687008174830, 1667192994351705710320597997679883789), (346050976053621, 1667200854488972767347361850292718596), (338586875976816, 1667208614446149602114056205615846474), (331290609537658, 1667216275739027444033749599586553565), (324158183433153, 1667223839855231782045948045103945069), (317185706523118, 1667231308254860857068396851382540811), (310369386979825, 1667238682371107018945084390421831173), (303705529525177, 1667245963610861476875549921079063702), (297190532752424, 1667253153355302953900486977047838507), (290820886529595, 1667260252960470738320717455093618345), (284593169481865, 1667267263757822607910599846866822560), (278504046550243, 1667274187054778086423941975651151404), (272550266624002, 1667281024135247476152961235545137132), (266728660244414, 1667287776260147095162487431586411291), (261036137377417, 1667294444667901133257352306200655569), (255469685252938, 1667301030574930526726817203002146715), (250026366268669, 1667307535176129238423105197154321211), (244703315956187, 1667313959645328316749809746674404508), (239497741007372, 1667320305135748094639315407722372198), (234406917359159, 1667326572780438877566489951189750248), (229428188334719, 1667332763692710458059784041847512451), (224558962839259, 1667338878966550783012344329077870914), (219796713608656, 1667344919677034089347454461864308085), (215138975509233, 1667350886880718813237979853168183824), (210583343887042, 1667356781616035568102650494841096239), (206127472965055, 1667362604903665476987812289221220939), (201769074286757, 1667368357746909135677214706485325225), (197505915204644, 1667374041132046473940616189443574615), (193335817412220, 1667379656028687773721215538058322292), (189256655518110, 1667385203390116094759468020805568465), (185266355660972, 1667390684153621350144576430901198975), (181362894163914, 1667396099240826266563238246527183072), (177544296227204, 1667401449558004456566956035407102446), (173808634658045, 1667406735996390822993728892751282803), (170154028636302, 1667411959432484508747039848068301768), (166578642515029, 1667417120728344598444971082489946535), (163080684654754, 1667422220731878771995660411615688099), (159658406290458, 1667427260277125103923196668279879752), (156310100430257, 1667432240184527196251851281212699715), (153034100784816, 1667437161261202826948029480889470574), (149828780726545, 1667442024301206290310610084721551431), (146692552277691, 1667446830085784600283867180424307969), (143623865126433, 1667451579383627722435681618956696727), (140621205670137, 1667456272951112995290304422480592722), (137683096084959, 1667460911532543896822862123584300798), (134808093420990, 1667465495860383307205701912469355054), (131994788722195, 1667470026655481414338428609084476902), (129241806170387, 1667474504627298404288200875217609650), (126547802252530, 1667478930474122074508883455365725564), (123911464950680, 1667483304883280503591575649822622835), (121331512953882, 1667487628531349907319651186268740894), (118806694891384, 1667491902084357806953756676370030152), (116335788586535, 1667496126197981631951429432487950835), (113917600330763, 1667500301517742875727505508218894494), (111550964177037, 1667504428679196919580872584136647342), (109234741252257, 1667508508308118636546131348067758040), (106967819087999, 1667512541020683883671281905341231619), (104749110969114, 1667516527423646988070726969284194630), (102577555299623, 1667520468114514329052912700162753765), (100452114985446, 1667524363681714115670189290181712029), (98371776833452, 1667528214704762456181485399670226819), (96335550966381, 1667532021754425813152806563965313908), (94342470253169, 1667535785392879935243169872806666239), (92391589754238, 1667539506173865354131281291028163254), (90481986181331, 1667543184642839532528072078001980450), (88612757371478, 1667546821337125746789274525093902797), (86783021774676, 1667550416786058785287781143880453541), (84991917954919, 1667553971511127541424946329629130401), (83238604104184, 1667557486026114577950706288303701105), (81522257569014, 1667560960837232737121958520122377981), (79842074389346, 1667564396443258869154695330745497393), (78197268849238, 1667567793335664749415653947608879381), (76587073039163, 1667571151998745252851540854700306175), (75010736429554, 1667574472909743852266103249830418032), (73467525455270, 1667577756538975505225427451885475301), (71956723110707, 1667581003349946992597888940516205295), (70477628555237, 1667584213799474770015279721362153822), (69029556728694, 1667587388337800391873983158707294479), (67611837976644, 1667590527408703565877907901167709072), (66223817685157, 1667593631449612894556548328923632180), (64864855924819, 1667596700891714358670387530150281901), (63534327103746, 1667599736160057595940337391440350170), (62231619629344, 1667602737673660027106512642641210184), (60956135578572, 1667605705845608879932909561218518941), (59707290376499, 1667608641083161160427105579940529283), (58484512482898, 1667611543787841619236563426726393923), (57287243086696, 1667614414355538759914210994579191606), (56114935808039, 1667617253176598934514420534426093900), (54967056407783, 1667620060635918570785117146564154312), (53843082504209, 1667622837113034574061338889920878280), (52742503296767, 1667625582982212945839022276466109775), (51664819296662, 1667628298612535659914010214503438050), (50609542064100, 1667630984367985835909225445436948701), (49576193952021, 1667633640607531248981608667344688069), (48564307856134, 1667636267685206213498809599495422346), (47573426971109, 1667638865950191877502797889896113447), (46603104552742, 1667641435746894963832618333045334159), (45652903685951, 1667643977415024992860572107872922892), (44722397058437, 1667646491289670020904313682608110194), (43811166739877, 1667648977701370927510891808270195543), (42918803966487, 1667651436976194283966840825407704490), (42044908930832, 1667653869435803834570280535822450011), (41189090576729, 1667656275397530621405870347198124402), (40350966399128, 1667658655174441782590672539352549461), (39530162248829, 1667661009075408053207820712375134183), (38726312141913, 1667663337405169997414696392207696519), (37939058073768, 1667665640464402999502445419304732698), (37168049837595, 1667667918549781040993493744403122555), (36412944847265, 1667670171954039290192648014632250160), (35673407964431, 1667672400966035529954808311717039713), (34949111329775, 1667674605870810448797716382806658177), (34239734198295, 1667676786949646819870969091379139263), (33544962778514, 1667678944480127591692217977005435950), (32864490075525, 1667681078736192913977543430470370310), (32198015737771, 1667683189988196121324944444539437258), (31545245907458, 1667685278502958696957246673741534044), (30905893074515, 1667687344543824238193042644181231701), (30279675934022, 1667689388370711444791093394307795979), (29666319246990, 1667691410240166150804510051204524877), (29065553704440, 1667693410405412420085580250911729983), (28477115794679, 1667695389116402725099904747947146251), (27900747673699, 1667697346619867228239173865866167554), (27336197038620, 1667699283159362184365063986559474013), (26783217004101, 1667701198975317482872005525889490515), (26241565981648, 1667703094305083347123611938055888886), (25711007561740, 1667704969382976208696021643476842161), (25191310398707, 1667706824440323773450959680564065787), (24682248098299, 1667708659705509296061652144439468676), (24183599107864, 1667710475404015079225513046881496124), (23695146609081, 1667712271758465213418468863341226218), (23216678413190, 1667714048988667572676598942165008753), (22747986858638, 1667715807311655081531167499065821535), (22288868711106, 1667717546941726267872831300246157872), (21839125065842, 1667719268090485116179561078121338344), (21398561252243, 1667720970966880235210357197743252776), (20966986740651, 1667722655777243353942922041174723757), (20544215051276, 1667724322725327159217831642938716289), (20130063665228, 1667725972012342488244193376356501619), (19724353937584, 1667727603836994888822058235895663742), (19326911012447, 1667729218395520559844755716370344563), (18937563739957, 1667730815881721684359623410656018074), (18556144595190, 1667732396487001167188105688228739527), (18182489598916, 1667733960400396788835695917203104788), (17816438240162, 1667735507808614787158500470436130577), (17457833400538, 1667737038896062877996121907543126046), (17106521280284, 1667738553844882725729910630439185887), (16762351326001, 1667740052834981874481241850635173552), (16425176160017, 1667741536044065150426166082158147728), (16094851511355, 1667743003647665545470389931498772997), (15771236148264, 1667744455819174592301908021901799524), (15454191812277, 1667745892729872240617569608500003077), (15143583153755, 1667747314548956244104272620935370153), (14839277668885, 1667748721443571067545185831510485790), (14541145638096, 1667750113578836323216263277493061326), (14249060065868, 1667751491117874745538194881547205986), (13962896621879, 1667752854221839712753698422508297653), (13682533583490, 1667754203049942324209569580027311212), (13407851779504, 1667755537759478041637041517209463535), (13138734535195, 1667756858505852902642639895851940899), (12875067618563, 1667758165442609314444733456676885616), (12616739187786, 1667759458721451435718257942807357049), (12363639739851, 1667760738492270154241519173049734460), (12115662060329, 1667762004903167667874449724441571025), (11872701174260, 1667763258100481676237096368465856073), (11634654298145, 1667764498228809190300348596231893738), (11401420792991, 1667765725431029966947881709556851548), (11172902118406, 1667766939848329575418883370525124476), (10949001787707, 1667768141620222102395265304251438603), (10729625324032, 1667769330884572502354639853653216781), (10514680217404, 1667770507777618599671274725984623799), (10304075882768, 1667771672433992748811441522502458040), (10097723618932, 1667772824986743158836959939623361664), (9895536568430, 1667773965567354888301227692499913176), (9697429678259, 1667775094305770516495536372901103532)]
def rebateB (j : Nat) : Nat := if j≤3860 then feeScale else if j<4348 then (entries[j-3861]?.getD (0,0)).1 else 0
def rebateD (j : Nat) : Nat := if j≤3860 then 0 else if j<4348 then (entries[j-3861]?.getD (0,0)).2 else 0
def kappa : ℚ := 826/2^66

def midOk (j : Nat) : Bool :=
  let a := ((feeScale : ℚ)-rebateB j)/feeScale
  let b := -kappa*(rebateD j : ℚ)/feeScale
  decide (rebateB j≤feeScale) &&
    affinePointOk P (lowerQ 826 j) (a*lowerQ 826 j+b) &&
    affinePointOk P (upperQ 826 j) (a*upperQ 826 j+b)

theorem cost_le_scarf (x : ℝ) : costScarf P x≤ClaudeWCT.Numerics.RouteC.scarf (P.θ-x) P.m P.vv := by
  have hv : 0≤(P.vv : ℝ) := by norm_num [P]
  unfold costScarf
  split_ifs
  · exact le_rfl
  · unfold ClaudeWCT.Numerics.RouteC.scarf
    have ha := neg_le_abs ((P.m : ℝ)-(P.θ-x))
    have hb := Real.abs_le_sqrt (show ((P.m : ℝ)-(P.θ-x))^2≤((P.m : ℝ)-(P.θ-x))^2+P.vv by linarith)
    linarith

theorem global_bound (x : ℝ) (hx : 0≤x) : costScarf P x≤x :=
  scarf_le_price P (by norm_num [P]) (by norm_num [P]) (by norm_num [P]) x hx

theorem local_rebate (hmid : ∀ i : Fin 487, midOk (3861+i.val)=true)
    (j : Nat) (x : ℝ) (hx : 0≤x) (hL : (lowerQ 826 j : ℝ)≤x) (hU : x≤(upperQ 826 j : ℝ)) :
    costScarf P x+(kappa : ℝ)*(rebateD j : ℝ)/feeScale+(rebateB j : ℝ)*x/feeScale≤x := by
  have hS : (0 : ℝ)<feeScale := feeScale_pos
  by_cases hc : j≤3860
  · have hclip : x≤(P.c0 : ℝ) := by
      calc x≤(upperQ 826 j : ℝ) := hU
           _≤(upperQ 826 3860 : ℝ) := upperQ_mono 826 hc
           _≤(P.c0 : ℝ) := by exact_mod_cast (by decide +kernel : upperQ 826 3860≤P.c0)
    have hz : costScarf P x=0 := by simp only [costScarf,not_lt.mpr hclip,ite_false]
    simp only [rebateB,rebateD,if_pos hc,hz,Nat.cast_zero, Nat.cast_ofNat,mul_zero,zero_div,add_zero,zero_add]
    rw [mul_comm (feeScale : ℝ),mul_div_cancel_right₀ _ hS.ne']
  · by_cases hm : j<4348
    · have hi : j=3861+(j-3861) := by omega
      have hh := hmid ⟨j-3861,by omega⟩
      rw [←hi] at hh
      simp only [midOk,Bool.and_eq_true,decide_eq_true_eq] at hh
      have hv : 0≤(P.vv : ℝ) := by norm_num [P]
      have hb := affineInterval_sound P (lowerQ 826 j) (upperQ 826 j)
        (((feeScale : ℚ)-rebateB j)/feeScale) (-kappa*(rebateD j : ℚ)/feeScale) hv hh.1.2 hh.2 x hL hU
      have hs := (cost_le_scarf x).trans hb
      push_cast at hs
      field_simp at hs ⊢
      nlinarith
    · simp only [rebateB,rebateD,if_neg hc,if_neg hm,Nat.cast_zero,mul_zero,zero_mul,zero_div,add_zero]
      exact global_bound x hx

end SigGolfResearch.RebateData
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000


namespace SigGolfResearch.RealRow
open Finset Polynomial
open scoped BigOperators
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.SharedMoments
open SigGolfResearch.RebateData SigGolfResearch.AffineBound

theorem real_row {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (Prob First : Nat[X])
    (hProb : CoeffLE Prob (weightedHistogram good bin (fun _ => 1)))
    (hFirst : CoeffLE First (weightedHistogram good bin weight))
    (hmid : ∀ i : Fin 487, midOk (3861+i.val)=true)
    (hinterval : ∀ x, good x → (lowerQ 826 (bin x) : ℝ)≤(kappa : ℝ)*(weight x : ℝ) ∧
      (kappa : ℝ)*(weight x : ℝ)≤(upperQ 826 (bin x) : ℝ)) :
    (∑ x, costScarf P ((kappa : ℝ)*(weight x : ℝ))) +
      (kappa : ℝ)/feeScale*(
        (∑ j ∈ range 7210, (rebateD j : ℝ)*(Prob.coeff j : ℝ))+
        (∑ j ∈ range 7210, (rebateB j : ℝ)*(First.coeff j : ℝ))) ≤
      (kappa : ℝ)*(∑ x, (weight x : ℝ)) := by
  have hs := sum_cost_rebate good bin weight Prob First hProb hFirst 7210
    (fun j => (kappa : ℝ)*(rebateD j : ℝ)/feeScale)
    (fun j => (kappa : ℝ)*(rebateB j : ℝ)/feeScale)
    (fun j => by unfold kappa feeScale; positivity)
    (fun j => by unfold kappa feeScale; positivity)
    (fun x => costScarf P ((kappa : ℝ)*(weight x : ℝ))) 1 (kappa : ℝ)
    (fun x => by simpa using global_bound ((kappa : ℝ)*(weight x : ℝ)) (by unfold kappa; positivity))
    (fun x hg _ => by
      have h := local_rebate hmid (bin x) ((kappa : ℝ)*(weight x : ℝ)) (by unfold kappa; positivity)
        (hinterval x hg).1 (hinterval x hg).2
      convert h using 1 <;> ring)
  have he : (∑ j ∈ range 7210,
      ((kappa : ℝ)*(rebateD j : ℝ)/feeScale*(Prob.coeff j : ℝ)+
      (kappa : ℝ)*(rebateB j : ℝ)/feeScale*(First.coeff j : ℝ))) =
      (kappa : ℝ)/feeScale*((∑ j ∈ range 7210,(rebateD j : ℝ)*(Prob.coeff j : ℝ))+
        (∑ j ∈ range 7210,(rebateB j : ℝ)*(First.coeff j : ℝ))) := by
    rw [mul_add,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,one_mul] at hs
  exact hs

theorem nat_row_finish (s kr : ℝ) (den M dn bn : Nat) (hden : 0 < den) (hkr : 0 < kr)
    (hs0 : 0 ≤ s) (hs : s+kr/(den : ℝ)*((dn : ℝ)+(bn : ℝ)) ≤ kr*(M : ℝ)) :
    s ≤ kr/(den : ℝ)*((den*M-dn-bn : Nat) : ℝ) := by
  have hd : (0 : ℝ)<den := by exact_mod_cast hden
  have hh : ((dn+bn : Nat) : ℝ)≤((den*M : Nat) : ℝ) := by
    have hm : kr/(den : ℝ)*((dn+bn : Nat) : ℝ) ≤ kr/(den : ℝ)*((den*M : Nat) : ℝ) := by
      push_cast
      have he : kr/(den : ℝ)*((den : ℝ)*(M : ℝ))=kr*(M : ℝ) := by field_simp
      rw [he]
      linarith
    exact le_of_mul_le_mul_left hm (div_pos hkr hd)
  have hn : dn+bn≤den*M := by exact_mod_cast hh
  rw [Nat.sub_sub,Nat.cast_sub hn]
  push_cast
  have he : kr/(den : ℝ)*((den : ℝ)*(M : ℝ)-((dn : ℝ)+(bn : ℝ))) =
      kr*(M : ℝ)-kr/(den : ℝ)*((dn : ℝ)+(bn : ℝ)) := by field_simp
  rw [he]
  linarith

end SigGolfResearch.RealRow
namespace SigGolfResearch.RebateData
open ClaudeWCT.Numerics.RouteCFees SigGolfResearch.AffineBound
open ClaudeWCT.Numerics.SharedFees ClaudeWCT.Numerics.SharedGeneratedCoordinate
open Finset Polynomial

theorem entries_bound : entries.all (fun p => decide (p.1≤2^128) && decide (p.2≤2^128))=true := by decide +kernel

theorem entry_bound (j : Nat) : (entries[j]?.getD (0,0)).1≤2^128 ∧ (entries[j]?.getD (0,0)).2≤2^128 := by
  by_cases hj : j<entries.length
  · rw [List.getElem?_eq_getElem hj]
    have h := List.all_eq_true.mp entries_bound entries[j] (List.getElem_mem hj)
    simpa only [Bool.and_eq_true,decide_eq_true_eq,Option.getD_some] using h
  · rw [List.getElem?_eq_none (by omega)]
    norm_num

theorem fee_bound (j : Nat) : rebateB j≤2^128 ∧ rebateD j≤2^128 := by
  unfold rebateB rebateD
  split_ifs <;> first | exact entry_bound _ | norm_num [feeScale]

def treeB : Nat := packTree 4096 13 0 (fun i => if i<7210 then rebateB (7209-i) else 0)
def treeD : Nat := packTree 4096 13 0 (fun i => if i<7210 then rebateD (7209-i) else 0)

open Lean Elab in
elab "tree_pack% " k:num : term => do
  return limbExpr (if k.getNat=0 then treeB else treeD)

noncomputable def PackB : Nat := tree_pack% 0
noncomputable def PackD : Nat := tree_pack% 1

theorem packB_eq : treeB=PackB := by decide +kernel
theorem packD_eq : treeD=PackD := by decide +kernel

theorem dot_model (Poly : Nat[X]) (fee : Nat → Nat)
    (hfee : ∀ j, fee j≤2^128) (hmass : Poly.eval 1≤2^3072) :
    packedDot (Poly.eval (2^4096)) (packTree 4096 13 0 (fun i => if i<7210 then fee (7209-i) else 0)) =
      ∑ j ∈ range 7210, Poly.coeff j*fee j := by
  unfold packedDot
  rw [packTree_reversed 4096 13 7210 fee (by decide)]
  apply convolution_shift
  have hs : (∑ j ∈ range 7210,fee j)≤7210*2^128 := by
    calc _≤∑ _j ∈ range 7210,2^128 := sum_le_sum fun j _ => hfee j
         _=_ := by simp
  exact (Nat.mul_le_mul hmass hs).trans_lt (by decide +kernel)

end SigGolfResearch.RebateData
namespace SigGolfResearch.RowBudget
open Finset Polynomial
open scoped BigOperators
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.SharedFees
open SigGolfResearch.RebateData SigGolfResearch.RealRow

theorem row_budget {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (Prob First : Nat[X])
    (hProb : CoeffLE Prob (weightedHistogram good bin (fun _ => 1)))
    (hFirst : CoeffLE First (weightedHistogram good bin weight))
    (hPm : Prob.eval 1≤2^3072) (hFm : First.eval 1≤2^3072)
    (hmid : ∀ i : Fin 487, midOk (3861+i.val)=true)
    (hinterval : ∀ x, good x → (lowerQ 826 (bin x) : ℝ)≤(kappa : ℝ)*(weight x : ℝ) ∧
      (kappa : ℝ)*(weight x : ℝ)≤(upperQ 826 (bin x) : ℝ))
    (M : Nat) (hM : ∑ x,weight x=M) :
    (∑ x, costScarf P ((kappa : ℝ)*(weight x : ℝ))) ≤ (kappa : ℝ)/feeScale*
      ((feeScale*M-packedDot (Prob.eval (2^4096)) PackD-packedDot (First.eval (2^4096)) PackB : Nat) : ℝ) := by
  have hd : ((packedDot (Prob.eval (2^4096)) PackD : Nat) : ℝ)=
      ∑ j ∈ range 7210,(rebateD j : ℝ)*(Prob.coeff j : ℝ) := by
    rw [←packD_eq]
    unfold treeD
    rw [dot_model Prob rebateD (fun j => (fee_bound j).2) hPm]
    push_cast
    apply sum_congr rfl
    intro j _
    ring
  have hb : ((packedDot (First.eval (2^4096)) PackB : Nat) : ℝ)=
      ∑ j ∈ range 7210,(rebateB j : ℝ)*(First.coeff j : ℝ) := by
    rw [←packB_eq]
    unfold treeB
    rw [dot_model First rebateB (fun j => (fee_bound j).1) hFm]
    push_cast
    apply sum_congr rfl
    intro j _
    ring
  have hw : (∑ x,(weight x : ℝ))=(M : ℝ) := by exact_mod_cast hM
  have hr := real_row good bin weight Prob First hProb hFirst hmid hinterval
  rw [hw,←hd,←hb] at hr
  have hP : ParFacts P := parFacts_of_ok P (by decide +kernel)
  have hz : (0 : ℝ)≤∑ x,costScarf P ((kappa : ℝ)*(weight x : ℝ)) := by
    apply sum_nonneg
    intro x _
    exact costOf_nonneg 5 P hP _ (by unfold kappa; positivity)
  exact nat_row_finish _ (kappa : ℝ) feeScale M _ _ (by norm_num [feeScale])
    (by norm_num [kappa]) hz hr

end SigGolfResearch.RowBudget

namespace SigGolfResearch.RebateData
theorem mid_checked : ∀ i : Fin 487, midOk (3861+i.val)=true := by decide +kernel


theorem P_eq_rcPar : P=ClaudeWCT.Numerics.RouteCData.rcPar := by rfl
end SigGolfResearch.RebateData

end Cap776Arithmetic

-- ==== merged from ClaudeWCT_Numerics_RouteCRows ====
section

/-! Route C row dot products and Poisson-envelope certificates at the installed gate (RC938: #938's
cap-776 law through the binomial thinning, so the envelope is `u = 13167581e-8`, `λ = 2027792e-6` on uniform
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

noncomputable def affineFirstN (r : ℕ) : ℕ :=
  if r=19 then SigGolfResearch.ProbabilityCache.FirstForest19 else
  if r=20 then SigGolfResearch.Twenty.FirstForest20 else forestN r

noncomputable def affineCountN (r : Nat) : Nat :=
  match r with
  | 7 => SigGolfResearch.ProbabilityCache.CountForest_7
  | 8 => SigGolfResearch.ProbabilityCache.CountForest_8
  | 9 => SigGolfResearch.ProbabilityCache.CountForest_9
  | 10 => SigGolfResearch.ProbabilityCache.CountForest_10
  | 11 => SigGolfResearch.ProbabilityCache.CountForest_11
  | 12 => SigGolfResearch.ProbabilityCache.CountForest_12
  | 13 => SigGolfResearch.ProbabilityCache.CountForest_13
  | 14 => SigGolfResearch.ProbabilityCache.CountForest_14
  | 15 => SigGolfResearch.ProbabilityCache.CountForest_15
  | 16 => SigGolfResearch.ProbabilityCache.CountForest_16
  | 17 => SigGolfResearch.ProbabilityCache.CountForest_17
  | 18 => SigGolfResearch.ProbabilityCache.CountForest_18
  | 19 => SigGolfResearch.ProbabilityCache.CountForest_19
  | _ => 0

noncomputable def affineRaw (r : ℕ) : ℕ := feeScale*forestMoment r-
  ClaudeWCT.Numerics.SharedFees.packedDot (affineCountN r) SigGolfResearch.RebateData.PackD-
  ClaudeWCT.Numerics.SharedFees.packedDot (affineFirstN r) SigGolfResearch.RebateData.PackB

noncomputable def affineRowData (r : ℕ) : ℕ :=
  match r with
  | 1 => 0
  | 2 => 12924522831368495564705478904853378719264830210294868072524294513282367580929955699981657277726720
  | 3 => 474385233980054732532409148077579686955137010701776221681401572708940159892426158602911328879579636059300399244766197973919300330598642365759488
  | 4 => 800830441840119800733271649072025482357335213614114967009818654200060932220113296940492498337634697304998137893801896641856714399159704529651322636384311135821330015257139016142389216542720
  | 5 => 320946013580386177850276848450347085753271707536487733299793081290968353880226295225418461734736263078069599577394172792713997677573170498730483404090225593479947404517019382302925177845088298544158394467250111749210119656114749440000
  | 6 => 54907912769911971589020892459159366653650595540662865650448951892216930789771215986675239292139968523881102969725971322371109080859374249559074003839060048835300112052199190948059486638933441128131232811965633853090951798894865123999597345318397032098844121056363955131588280320
  | 7 => 1954239140781653456575771240052229671996502156362125648488252631702116622708241206829050826827141672425077952831081789849064227869018031911114309552800067380289135114895046078286474909326244017569195814290761881507857024987523854178571748941818649289868105627990330381775654272562345658624249341574319850317298326227124224
  | 8 => 130072928466539580459308833633428953484121596028575663116261277876758474044046038917644620151403272055660160547206014279998274202556520351620917850537183252593336885578399719314626903805013819612135311879185149486922197100007918224857322557685765521509504558288169184071811057881034031351883423896524303133740130721109838455328129002141512712901670781962251545870336
  | 9 => 6312117466141852370090586814391629380521371740786918486467237214000928008620014655148991592794974622189398991098749137660174861330687224308936888521956786331331064359545955127756930672742113580821955013851059597846447039883421407858962169111545789226778671895223231952306358913824876076348852395338714049987722758563784707215512107164790392371680634547859342322668511570631480648557365578574865988520828207104
  | 10 => 237983724557089245530117523969014957445561882470759686186157141725815239995164552437158460718268941321713696629110613958481535935915893267785133809493756602139393915756451442450885869444042495245212866326823944686213972353184375190117253515780429934126135752968143729937687546905689845610053779285218441873421077449706548068361228821981201511113076421093674773099597009241146713553541466412424922721983661715914026770671682827274856165380278295977787392
  | 11 => 7284073658132200464102608935764839136999379382242553322499986328225563462740443639360864987555297563168225903071275112691022577099978711779581017599452449307771200082676206282806627535647976205053629409911035180509612856691531673451405773161493513593187332218120704565319724558556423909750451444881195551425761330617258813580449701907225199723701353541337365776751265446316273495076372993412849177335487193306251893539425754641138376208584149914821417009694331018701724739999043233136726058729472
  | 12 => 186776199792227850169016801751634717038978982064094806128302435325499530239772392088755509869934283838472128173011384230660461984301617983526517679448053068852796376656524171427647422709927068574456583512590864339244471411384467994290353018709114693521363707098100642313293446858410951451440225003059210118505487700034081529319733304001015517808768797374097488594304513918158320851375421458751179071171519454214545687092660577197256294244146290005523872056504376667088786449613401923803453415015213021308800929733519597145094918184909144064
  | 13 => 4105577914927100966127427539641496652043424559918024640537622125633020087030620510948883161477044700695643405749950648565737095445730993310845815472806647144914568817841548995575233507855421603803589671768503672457447374442093848811457616671391502915801717785405469419931414506861620053547548621794686486547556821383069577549336914128741059567417643225985579861506722111190731601529144665178709743135106619268511749076963835194626373557497323568583994206846787829740823978144314024494437479953015391221382253536311469771872051253876610328152310630805566589887271295159754973547331584
  | 14 => 78705916085659436929918291760554897054911457476615356710760596056793786176389739301224861180552743027901487996808848028896489224848855192916409959321510823198765077959373136465990496454610134210346137722565064889317898199010866839557660799213280380688208507000354795514630335224715621275097678443933896985704567796549623777422950655772000430759988249260063940475645692527332280876759305038503352144760554497060391131027610044939310892998834373886202326764007111170018448398721309975510634592485500238061874722441337613931844050861651362323337462420194012245918089699355601562799437062473735285131236089023475869470352509763584
  | 15 => 1333129530212889787409974768602114156079979300376452313436613691339764214144842849516431722280352603215685144465959645081038046154115128636910868105641734368238223058681532444968623972347981251220639724398993448796591426721199049311556108673140162639420543167965619947610930532632668489243053092110174164789525259743954277858402499947040982016092458336260467197790946702120272097422788625022454499411806632587389357999769474246230567809564234965702110169594533847671045192262591070252286751899874260627692133117982425186496249164850308742871335384505642730372626958311990089353570579470838737325635861263659261643185344512806958809506999794879002352215729529675696832512
  | 16 => 20153027653604022071813963392192555941413487688228211475347239710586298382866901983919278950389788157994066565128971974646049055413347108895134326423646920597428438499693849430934248045212546586813991359818928186779760525904180340869621165403089971044448013296344935133352681609794058620088848876021031724357046851621530496871174357982168677052644975343109301313751550591470907873263982928559134284604461794067344128819662509562182465636872908467078125600095785699474517584213417176585391741602727814149848263286640115977006847637488344784747532490122768580990107791361522991787587040162108830072116246354612544009653842318905062692985016074660933391072708609320919862064002811667219737611697571218428896613498880
  | 17 => 274065557399414351877209466865671433443180040997334905341432275642288272854637912145558556462510526173175589409584165159300069907095566546038245626877674345739019667163691285579230366183756622183725874054808139364142710772586118606249045448414103461041839322170654250884590637274169627152600808114716299080644788509372481523622762597585433762872322517313576644184449972889330517839824958061387203468526799486801079269829879777433284553309264691678978683587716682845521413004233672357941194613584273509958776160597370192932750473893482731453219493393531867718164640085712165260012012355197901550097068327715354487594579688386760881257737431651300208383871574799070535816046490139659041581798249728635960944813402369260803893527134759814036949427040987119616
  | 18 => 3374483311969609383964808157382237740561559479084491322911216806181226276580990347304940574252978459353143408585245852530117452688340723827938047273566405829546627688540840275030221496590517590908670558863753187444728628239360663488216579356164338910512100498229910129712135699465307277158773647041517839868075848774013673232631071794173551483446080159957021620889152792515751242429063551367414403118285567347919215873089683406069287195373224684986131532280408266347121016574270934745971616223833805651772247869913738518779669780022796651504326915458500578646130284113967096498626606563690354589169255449923506367025845856801785807430250140181095025566993485234177902178147432352679821530901063534014172154938571058600244747031662001992610555441649675859618902186081068404556393042224947473212768256
  | 19 => 37823718561538788421446015616462658295835470228779405950836348022680400863998063086653391396894131429457947678650903652046602431038835810458081535347179179594196229731683189366681674740329487090569432251231605671557428222972297217560486592495248712939632879666981702452282940362044665396114703870505082118786110155281927145572428703034096517261069696292734597872671283162902203007028480607111989996945449060433425937332564638880331161387871521708136457582215802846976035040316770584617020788969154650704607367195154181416787661834347351606743276438343599370561393366882139596644573627833959896438322811447151590572651287467313541580992469941773896599341072917162359958583023398748895754521872655356179868174343608414341041835727071795882213878851028175585504784004397171061908170427126468970297938939524464038982380790302565733800102699466752
  | 20 => 608731738200940135661054863213472673091870285856900610823229187180808435784621081435661917694085318173513856825978979010688778024277946501933995313795638722394893205298072662629233501149144219314293869089383341010993494678497617046660118811071928043463108982651416923973631671488552054664167508731460197193125289371310655730545574172290851394337736049131859239668332648091698791072357659555152962109247643940788374416025762656466064876054535249414740886432830511881946341332828137692717598335374947445679345523402141906956941481181342987641113968974923251776451046823663902081379318551155040113648080556667201998758427506769195104707706025843787664131828033384285923105379508024532163827731207441482489797301350909689915094532931741456869803356448711591055146380321505124471670355773264683386146060267074095893284272662957919767316149320887228430456837107965936071218818642055805272064
  | r => feeScale*forestMoment r

noncomputable def affineRow (r : ℕ) : ℕ :=
  if 1≤r ∧ r≤20 then affineRowData r else feeScale*forestMoment r

set_option debug.skipKernelTC false in
theorem affineRows_checked : ∀ r : Fin 21, 1≤r.val → affineRaw r.val=affineRow r.val := by decide +kernel

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

def meanN : ℕ := 19669
def meanD : ℕ := 20000
def secN : ℕ := 41661
def secD : ℕ := 5000000
def countN : ℕ := 287
def countD : ℕ := 50000
def overN : ℕ := 25689
def overD : ℕ := 10000000
def mgfN : ℕ := 300939
def mgfD : ℕ := 25000
def scarfN : ℕ := 120151
def scarfD : ℕ := 100000000
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
set_option debug.skipKernelTC false in
theorem env_scarf : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16^r*affineRow r) (feeScale*alphabetSize) (feeScale*pst) feeScale scarfN scarfD 80=true := by
  decide +kernel

theorem env_long : poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
    (fun r => 16 ^ r * rowLong r) (feeScale * alphabetSize) (feeScale * pst) feeScale longN longD 80 = true := by
  decide +kernel

/-! ### Parameter values and the route-C totals (generated) -/

theorem rc_c0 : (rcPar.c0 : ℝ) = (27 / 50 : ℝ) := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = (10 / 1 : ℝ) := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 1996581 / 1000000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (365 / 1000000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (365 / 1000000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(7918 / 1000 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (7918 / 1000 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (1000000 / 365 : ℝ) ≤ ∑ i ∈ Finset.range 30, (7918 / 1000 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (365 / 1000000 : ℝ) = ((1000000 / 365 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (1230/1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1230/1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (365 / 1000000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1230/1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 1/1024)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hx : (mgfN : ℝ)/mgfD-rcPar.a*(1-1/1024)≤5/2 := by norm_num [rcPar,mgfN,mgfD]
  have he : Real.exp ((mgfN : ℝ)/mgfD-rcPar.a*(1-1/1024))≤(49/4 : ℝ) := by
    refine (Real.exp_le_exp.mpr hx).trans ?_
    have hpow : Real.exp (5/2 : ℝ)^2=Real.exp (1 : ℝ)^5 := by
      rw [←Real.exp_nat_mul,←Real.exp_nat_mul]
      norm_num
    have h1 : Real.exp (1 : ℝ)^5≤(2.7182818286 : ℝ)^5 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have h2 : (2.7182818286 : ℝ)^5<(49/4 : ℝ)^2 := by norm_num
    have h0 := Real.exp_pos (5/2 : ℝ)
    nlinarith
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (49/4 : ℝ) + (overN : ℝ) / overD ≤ 49 / 100 := by
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
    (2:ENNReal)^128 * ((826*2^62:Nat):ENNReal) *
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

noncomputable def feeCoefficient : ENNReal := 826/2^66

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

 theorem feeCoefficient_real : feeCoefficient.toReal = (826:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((826:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((826:ℝ)/2^66*(n:ℝ)-6/5)) := by
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
    ((826:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((826:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
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
`(1 - kappa 2^-31)^(T-80) ≤ 13167581e-8` for the cap-776 `kappa`. -/
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

/-- Thinned Poisson parameter: `2^32 · kappa · 2^-31 = 2 kappa ≤ 2.027792` (cap 776). -/
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

/-! Scalar endpoint support for the cap-776 thinned certificate. -/
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

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (986:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (986/1000) (fun _ _ h => h)
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

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ (40711/100) := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment (40711/100) (fun L b R => nearBucket_insert L R b)
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
    nearPrice average_nearScore (40711/100)
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

/-! Route C for the FTS bank on #938's cap-776 law (RC938; R6 campaign stream RC, sec-rc/RC_SPEC.txt): binned
row bounds, thinned envelope moments, and the route-C excess theorems that replace the winsorized-Chernoff
certificate (removed). Every route-C moment is an insertion-monotone payoff, so #938's binomial thinning
(`Law.coordAverage_thin`: honest at rate `p` ≤ uniform at rate `kappa * p`) applies to all of them; the Scarf
payment of the one-large-bucket term is bounded by its monotone majorant `costOf 5`. The route-C split is
at rows `≤ 80`, so the long-row term is the `poissonCheckQ` tail only. The theorems
`excess_{middle,high,low,large,tiny}_certified` keep their installed names; their fee premise is gone. -/

section Cap776Forest
set_option debug.skipKernelTC false
namespace SigGolfResearch.ForestRow
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
open Finset Polynomial
open scoped BigOperators
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedMoments ClaudeWCT.Numerics.SharedPathForest
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.SharedFees
open SigGolfResearch.RebateData SigGolfResearch.RowBudget

noncomputable def row (r : Nat) : Nat := feeScale*forestMoment r-
  packedDot (if r≤6 ∨ r=20 then 0 else ProbabilityRows.forestPacked r) PackD-packedDot (SharedPathPacked.forest r) PackB

theorem forest_row (hmid : ∀ i : Fin 487, midOk (3861+i.val)=true)
    (r : Nat) (h1 : 1≤r) (h20 : r≤20) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costScarf P ((kappa : ℝ)*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal (kappa : ℝ)/(feeScale : ENNReal)*(row r : ENNReal) := by
  classical
  have hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×Fin 563 => coordinateCoverage ClaudeWCT.WCT9.wordDigit E=j).card :=
    fun K hK u hu j => wordDigit_coordinate_coeff K hK u (by omega) j
  have hκ : (0 : ℝ)<(kappa : ℝ) := by norm_num [kappa]
  have hS : 0<feeScale := by norm_num [feeScale]
  have hP : ParFacts P := parFacts_of_ok P (by decide +kernel)
  apply ofReal_sum_nat_bound _ _ _ feeScale hκ.le hS
    (fun h => costOf_nonneg 5 P hP _ (by positivity))
  have hfm : (actualPoly r).eval 1≤2^3072 :=
    (actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp).trans (forest_mass_3072 r h20)
  have hpm : (ProbabilityRows.forestPoly r).eval 1≤2^3072 := by
    have h := ProbabilityRows.forest_mass ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp
    have ha : alphabetSize^r≤alphabetSize^r*alphabetSize :=
      Nat.le_mul_of_pos_right _ (by decide)
    exact h.trans (ha.trans (forest_mass_3072 r h20))
  have hfenc := actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp
  have hpenc := ProbabilityRows.forest_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp
  let prob : ℕ[X] := if r≤6 ∨ r=20 then 0 else ProbabilityRows.forestPoly r
  have hpenc' : (if r≤6 ∨ r=20 then 0 else ProbabilityRows.forestPacked r)=prob.eval (2^4096) := by
    by_cases hr : r≤6 ∨ r=20
    · simp only [prob,if_pos hr,Polynomial.eval_zero]
    · simpa only [prob,if_neg hr] using hpenc
  have hpm' : prob.eval 1≤2^3072 := by
    by_cases hr : r≤6 ∨ r=20
    · simp only [prob,if_pos hr,Polynomial.eval_zero]
      exact Nat.zero_le _
    · simpa only [prob,if_neg hr] using hpm
  have hprob : CoeffLE prob (weightedHistogram (actualGood (r := r) ClaudeWCT.WCT9.wordDigit)
      (actualBin (r := r) ClaudeWCT.WCT9.wordDigit) (fun (_ : ForestHistory (Fin 563) r) => 1)) := by
    by_cases hr : r≤6 ∨ r=20
    · simp only [prob,if_pos hr]
      intro j
      simp only [Polynomial.coeff_zero]
      exact Nat.zero_le _
    · simpa only [prob,if_neg hr] using
        ProbabilityRows.forest_histogram ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp
  unfold row
  rw [hfenc,hpenc']
  apply row_budget (actualGood ClaudeWCT.WCT9.wordDigit) (actualBin ClaudeWCT.WCT9.wordDigit)
    (forestCoverage ClaudeWCT.WCT9.wordDigit) prob (actualPoly r) hprob
    (actual_histogram ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r h20 hp) hpm' hfm hmid
  · intro h hg
    have hb := bin_bounds 826 (actual_interval ClaudeWCT.WCT9.wordDigit h1 h hg)
    have hk : (kappa : ℝ)=(826 : ℝ)/2^66 := by norm_num [kappa]
    rw [hk]
    exact hb
  · exact forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
      WCTEnvelope.w1Table_wordDigit rows_checked r (by omega)

end SigGolfResearch.ForestRow

end Cap776Forest
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
rate `kappa * p` (cap-776 thinning), whose rows are checked by `poissonCheckQ` with `u = 13167581e-8` and
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

section Cap776AffineBank
set_option debug.skipKernelTC false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem affineFirstN_eq (r : ℕ) (h1 : 1≤r) (h20 : r≤20) :
    affineFirstN r=SharedPathPacked.forest r := by
  by_cases h19 : r=19
  · subst r
    simp only [affineFirstN,if_pos rfl]
    exact SigGolfResearch.ProbabilityCache.first_forest19.symm
  · by_cases h20' : r=20
    · subst r
      simp only [affineFirstN,if_neg h19,if_pos rfl]
      exact SigGolfResearch.Twenty.firstForest20.symm
    · simp only [affineFirstN,if_neg h19,if_neg h20']
      exact forestN_eq r h1 (by omega)

theorem affineCountN_eq (r : ℕ) (h7 : 7≤r) (h19 : r≤19) :
    SigGolfResearch.ProbabilityRows.forestPacked r=affineCountN r := by
  interval_cases r
  · exact SigGolfResearch.ProbabilityCache.countForest_7
  · exact SigGolfResearch.ProbabilityCache.countForest_8
  · exact SigGolfResearch.ProbabilityCache.countForest_9
  · exact SigGolfResearch.ProbabilityCache.countForest_10
  · exact SigGolfResearch.ProbabilityCache.countForest_11
  · exact SigGolfResearch.ProbabilityCache.countForest_12
  · exact SigGolfResearch.ProbabilityCache.countForest_13
  · exact SigGolfResearch.ProbabilityCache.countForest_14
  · exact SigGolfResearch.ProbabilityCache.countForest_15
  · exact SigGolfResearch.ProbabilityCache.countForest_16
  · exact SigGolfResearch.ProbabilityCache.countForest_17
  · exact SigGolfResearch.ProbabilityCache.countForest_18
  · exact SigGolfResearch.ProbabilityCache.countForest_19

theorem rc_affine_row (r : ℕ) (h1 : 1≤r) (h20 : r≤20) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf 5 rcPar ((rcPar.g : ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ)/2^66)/(feeScale : ENNReal)*(affineRow r : ENNReal) := by
  have h := SigGolfResearch.ForestRow.forest_row SigGolfResearch.RebateData.mid_checked r h1 h20
  rw [SigGolfResearch.RebateData.P_eq_rcPar] at h
  have hk : (SigGolfResearch.RebateData.kappa : ℝ)=(rcPar.g : ℝ)/2^66 := by
    norm_num [SigGolfResearch.RebateData.kappa,rcPar]
  rw [hk] at h
  unfold SigGolfResearch.ForestRow.row at h
  have hcount : (if r≤6 ∨ r=20 then 0 else SigGolfResearch.ProbabilityRows.forestPacked r)=affineCountN r := by
    by_cases he : r≤6 ∨ r=20
    · rw [if_pos he]
      rcases he with hr | hr
      · interval_cases r <;> rfl
      · subst r; rfl
    · rw [if_neg he]
      exact affineCountN_eq r (by omega) (by omega)
  rw [hcount,←affineFirstN_eq r h1 h20] at h
  change _≤ENNReal.ofReal ((rcPar.g : ℝ)/2^66)/(feeScale : ENNReal)*(affineRaw r : ENNReal) at h
  rw [affineRows_checked ⟨r,by omega⟩ h1] at h
  exact h

theorem rc_affine_global (r : ℕ) (hr : r≤80) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf 5 rcPar ((rcPar.g : ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ)/2^66)/(feeScale : ENNReal)*((feeScale*forestMoment r : ℕ) : ENNReal) := by
  have hκ : (0 : ℝ)≤(rcPar.g : ℝ)/2^66 := by positivity
  have hP := parFacts_of_ok rcPar par_ok
  have hS : (feeScale : ℝ)≠0 := feeScale_pos.ne'
  apply SharedFees.ofReal_sum_nat_bound _ _ _ feeScale hκ (by norm_num [feeScale])
    (fun h => costOf_nonneg 5 rcPar hP _ (by positivity))
  have htot := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega)
  have htotR : (∑ h : ForestHistory (Fin 563) r,(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ))=(forestMoment r : ℝ) := by
    exact_mod_cast htot
  calc _≤∑ h : ForestHistory (Fin 563) r,(rcPar.g : ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ) := by
         apply Finset.sum_le_sum
         intro h _
         have hg := SigGolfResearch.RebateData.global_bound
           ((rcPar.g : ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)) (by positivity)
         rw [SigGolfResearch.RebateData.P_eq_rcPar] at hg
         exact hg
       _=(rcPar.g : ℝ)/2^66*(forestMoment r : ℝ) := by rw [←Finset.mul_sum,htotR]
       _=_ := by push_cast; field_simp

theorem rc_affine_point (W : List Alphabet) :
    ENNReal.ofReal (costOf 5 rcPar (priceBucket W).toReal)≤
      (feeScale : ENNReal)*feeCoefficient*alphabetSize/(feeScale : ENNReal) := by
  have h := SigGolfResearch.RebateData.global_bound (priceBucket W).toReal ENNReal.toReal_nonneg
  rw [SigGolfResearch.RebateData.P_eq_rcPar] at h
  calc _≤ENNReal.ofReal (priceBucket W).toReal := ENNReal.ofReal_le_ofReal h
       _=priceBucket W := ENNReal.ofReal_toReal (priceBucket_ne_top W)
       _≤feeCoefficient*alphabetSize := priceBucket_le W
       _=_ := by
         rw [show (feeScale : ENNReal)*feeCoefficient*alphabetSize=
           (feeCoefficient*alphabetSize)*(feeScale : ENNReal) by ac_rfl,
           ENNReal.mul_div_cancel_right (by norm_num [feeScale]) (by finiteness)]

theorem rc_kind_scarf (hP : ParFacts rcPar)
    (rate : ENNReal) (hrate : kappa*rate≤1) (T : ℕ)
    (hlam : (T : ENNReal)*(kappa*rate)*1≤((2027792 : ℕ) : ENNReal)/((1000000 : ℕ) : ENNReal))
    (hu : (1-kappa*rate)^(T-80)≤((13167581 : ℕ) : ENNReal)/((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0<Md)
    (hcheck : N600.poissonCheckQ fieldSize 13167581 100000000 2027792 1000000
      (fun r => 16^r*affineRow r) (feeScale*alphabetSize) (feeScale*pst) feeScale Mn Md 80=true) :
    (2^31 : ENNReal)*Law.coordAverage rate honestCoordLaw T
      (fun L => ENNReal.ofReal (costOf 5 rcPar (priceBucket L).toReal))≤(Mn : ENNReal)/Md := by
  apply rc_envelope_thin rate hrate T hlam hu feeScale (by norm_num [feeScale]) affineRow _
    (fun L b R => rc_cost_insert 5 hP L R b)
    (fun r h => ENNReal.ofReal (costOf 5 rcPar ((rcPar.g : ℝ)/2^66*
      (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) _ _ rc_affine_point Mn Md hMd
    (by rw [rc_pst];exact hcheck)
  · intro r _ h
    rw [rc_price_real]
  · intro r hr
    by_cases hrow : 1≤r ∧ r≤20
    · have h := rc_affine_row r hrow.1 hrow.2
      rwa [rc_coef] at h
    · have h := rc_affine_global r hr
      rw [rc_coef] at h
      unfold affineRow
      rwa [if_neg hrow]
end Cap776AffineBank

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

/-- Route C bank excess at the middle threshold (thinned cap-776 envelope, `rcPar`). -/
theorem rc_excess_middle :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1996581 : ℝ) / 1000000 - 1 / 1024)) ≤
      ENNReal.ofReal ((1230 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((1996581 : ℝ) / 1000000 - 1 / 1024)) =
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
    exact rc_kind_scarf hP (2^31 : ENNReal)⁻¹ rc_rate_uncond (2^32) rc_lam_uncond rc_u_uncond _ _
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
      (fun W => price W-ENNReal.ofReal ((1996581:ℝ)/1000000-1/1024)) ≤
        ENNReal.ofReal ((1230 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-1251/500000-1/1024)) ≤
        ENNReal.ofReal ((124500771:ℝ)/100000000000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (1996581 : ℝ) / 1000000 - 1 / 1024 ≤ 2 - 1251 / 500000 - 1 / 1024)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-776 envelope `(993/1000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 1251/1000000 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((99521/100000)*y) := by
  let t : ℝ := (y-1251/1000000)/(1/2-1251/1000000)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-1251/1000000)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-1251/500000-1/1024) (1-1/1024)
    (124500771/100000000000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-1251/500000-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (99521/100000)*y-((1-t)*(124500771/100000000000)+t*(49/100)) = t*(1521/200000) := by
    dsimp [t]; ring
  have hval : (1-t)*(124500771/100000000000)+t*(49/100) ≤ (99521/100000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) := by
  have h := price_excess_affine (2^32) ((1996581:ℝ)/1000000-1/1024) (1-1/1024)
    (1230/1000000) (49/100) (4581/996581) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) excess_middle_certified excess_low_certified
  have harg : (1-(4581:ℝ)/996581)*((1996581:ℝ)/1000000-1/1024)+4581/996581*(1-1/1024) = 249/125-1/1024 := by
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
