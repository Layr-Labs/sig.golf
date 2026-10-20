import SigGolfCandidate.ClaudeWCT_Numerics_N600Price
import SigGolfCandidate.ClaudeWCT_Numerics_TopZeroChecks

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

local notation "topFiberZ" z:arg score:arg =>
  (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
    SigGolfResearch.NonbinaryTop.EffectiveCounting.zeros w = z ∧
    SigGolfResearch.NonbinaryTop.Counting.weight w = 146 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = score).card

/-- Top zero cap: the zero-fibered top polynomial has the fiber counts as its digits. -/
theorem top_zero_digit (z j : Nat) (hj : j < 205) :
    SharedDigitBlock.digit (2^136) SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked
      (65536*z+256*146+27+j) = topFiberZ z (j+27) := by
  rw [← bits_digit_eq]
  apply CanonicalCounting.digit_histogram_of_weighted SigGolfResearch.NonbinaryTop.ZeroCounting.zstat _ 136 _ _
    CanonicalCounting.top_card SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked_weighted
  intro w
  have he := SigGolfResearch.NonbinaryTop.ZeroCounting.zstat_eq w
  have hs := SigGolfResearch.NonbinaryTop.EffectiveCounting.score_le w
  have hw := SigGolfResearch.NonbinaryTop.EffectiveCounting.weight_le_225 w
  omega

theorem top_zero_fibers (j : Nat) : (∑ z : Fin 10, topFiberZ z.val (j+27)) = topWordCount (j+15) := by
  rw [CanonicalCounting.count_fibers_fin]
  unfold topWordCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  omega

theorem topWordCount_lt (r : Nat) : topWordCount r < 2^136 :=
  (Finset.card_filter_le _ _).trans_lt CanonicalCounting.top_card

theorem top_zero_windows_fold (p : Nat) :
    (List.range 10).foldl (fun s zeros =>
      s + ((p >>> (136 * (65536 * zeros + 256 * 146 + 27))) % 2 ^ (136 * 205))) 0 =
    ∑ z : Fin 10, p / (2^136)^(65536*z.val+256*146+27) % (2^136)^205 := by
  have hfold (f : Nat → Nat) : (List.range 10).foldl (fun s z => s+f z) 0 =
      ∑ z : Fin 10, f z.val := by
    simp [List.range_succ, Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hfold]
  apply Finset.sum_congr rfl
  intro z _
  exact shift_window_eq 136 p (65536*z.val+256*146+27) 205

theorem top_counts_of_check (hcheck : TopZero.topHistogramCheck = true) (c : Fin 205) :
    topWordCount (c.val+15) = histogramWeight TopZero.topCounts (c.val+15) := by
  have he : packHistogram 136 15 205 TopZero.topCounts =
      (List.range 10).foldl (fun s zeros => s +
        ((SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked >>> (136 * (65536 * zeros + 256 * 146 + 27))) %
          2 ^ (136 * 205))) 0 :=
    by simpa only [TopZero.topHistogramCheck, decide_eq_true_eq] using hcheck
  have hsum (j : Nat) (hj : j < 205) :
      (∑ z : Fin 10, 1*SharedDigitBlock.digit (2^136) SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked
        (65536*z.val+256*146+27+j)) = topWordCount (j+15) := by
    simp only [Nat.one_mul]
    rw [← top_zero_fibers j]
    exact Finset.sum_congr rfl fun z _ => top_zero_digit z.val j hj
  have he' : packHistogram 136 15 205 TopZero.topCounts = ∑ z : Fin 10,
      1*(SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked / (2^136)^(65536*z.val+256*146+27) % (2^136)^205) := by
    rw [he, top_zero_windows_fold]
    simp only [Nat.one_mul]
  have hd : coefficient 136 (packHistogram 136 15 205 TopZero.topCounts) c.val = topWordCount (c.val+15) := by
    rw [coefficient, bits_digit_eq, he']
    exact (SharedDigitBlock.digit_window_sum (2^136) 205
      (fun _ : Fin 10 => SigGolfResearch.NonbinaryTop.ZeroCounting.zpacked)
      (fun z => 65536*z.val+256*146+27) (fun _ => 1) (by positivity)
      (fun j hj => by rw [hsum j hj]; exact topWordCount_lt _) c.val c.isLt).trans (hsum c.val c.isLt)
  exact hd.symm.trans (TopZero.top_histogram_digits c)

theorem topWordCount_eq (hcheck : TopZero.topHistogramCheck = true) (r : Nat) (h15 : 15 ≤ r) (hr : r < 220) :
    topWordCount r = histogramWeight TopZero.topCounts r := by
  have h := top_counts_of_check hcheck ⟨r - 15, by omega⟩
  simpa only [Nat.sub_add_cancel h15] using h

theorem topHighWeight_eq : topHighWeight = TopZero.topHighW := by
  rw [topHighWeight, SigGolfResearch.NonbinaryTop.ZeroCounting.zeroFreeCard_eq]
  rfl

/-- The d6b top selection law at the canonical floor 19, with the top producer zero cap 9. -/
theorem selected_top_histogram_card (hcheck : TopZero.topHistogramCheck = true) (c : Nat) (hc : 19 ≤ c) (hc' : c < 220) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight TopZero.topAcceptedHistogram c := by
  rw [selected_top_path_card 19 c le_rfl hc, TopZero.topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 2 ≤ c), topWordCount_eq hcheck (c - 2) (by omega) (by omega),
    topWordCount_eq hcheck c (by omega) hc', topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (hcheck : TopZero.topHistogramCheck = true) (c : Nat) (hc : 19 ≤ c)
    (hc' : c < 220) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight TopZero.topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) = _ from rfl, selected_top_histogram_card hcheck c hc hc']
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

#print axioms ClaudeWCT.Numerics.CanonicalHistogram.selected_top_histogram_probability
#print axioms ClaudeWCT.Numerics.CanonicalHistogram.selected_lower_histogram_probability
