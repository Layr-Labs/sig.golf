import SigGolfCandidate.ClaudeWCT.Numerics.N600Price
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ProducerDecodeV5
import SigGolfCandidate.T3.Nonbinary.Counting
import SigGolfCandidate.ClaudeWCT.WCT9.Core

/-! Top-policy sections moved here from N600PriceChecks / N600Price (R6 import hygiene): editing the
top counts, packet or ProducerDecodeV5 no longer rebuilds N600Price. -/

-- moved from N600PriceChecks (lines 354-493)
namespace ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.WCT9.CanonicalPolicy
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false
/-- Campaign R6 + RC: LOW-good top words (credit `≥ 16` without the LOW bonus 3, top floor 19) whose LOW half is not
forced (`gate1/packets/packet_R6_RC804_gate.json` freeCount). -/
def topChoiceFree : Nat := SigGolfResearch.R6Top.freeCountR6

/-- Weight (over `2^256`) of an accepted HIGH top word: the LOW halves that are neither good nor forced. -/
def topHighW : Nat := 3 * 2 ^ 126 - topChoiceFree

/-- Campaign R6 + RC: top word counts at target 153 (zeros `≤ 7`) by credit (no path bonus), credit `≥ 16`. -/
def topCounts : List (Nat × Nat) := SigGolfResearch.R6Top.topCountsR6

/-- e7b top histogram: a word of credit `c` is selected through LOW (credit `c + 3`, weight `2^128`) or through HIGH
(credit `c`, weight `topHighW`). Entries below the floor 19 never matter. -/
def topAcceptedHistogram : List (Nat × Nat) :=
  topCounts.flatMap fun e => [(e.1 + 3, e.2 * 2 ^ 128), (e.1, e.2 * topHighW)]

def initialBound : Nat := 366067310084349186981005127673973045684

def checkRows (stage : Nat) (row next : Array Nat) : Bool :=
  (List.range row.size).all fun residual =>
    recurrenceCheck lowerDen lowerHistogram (threshold stage residual) residual next row[residual]!

theorem row_three_checked : checkRows 3 rowThree #[scale] = true := by decide +kernel

theorem row_two_checked : checkRows 2 rowTwo rowThree = true := by decide +kernel

theorem row_one_checked : checkRows 1 rowOne rowTwo = true := by decide +kernel

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 19 73 rowOne initialBound = true := by
  decide +kernel

theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 199896 * scale := by
  decide +kernel

theorem lower_thresholds_checked :
    (List.range rowOne.size).all (fun r => decide (threshold 1 r ≤ 19)) = true ∧
    (List.range rowTwo.size).all (fun r => decide (threshold 2 r ≤ 19)) = true ∧
    (List.range rowThree.size).all (fun r => decide (threshold 3 r ≤ 19)) = true := by
  decide +kernel

theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 19) topDen 1024 = true := by
  decide +kernel

#print axioms row_three_checked

#print axioms row_two_checked

#print axioms row_one_checked

#print axioms initial_checked

#print axioms full_moment_checked

#print axioms top_tail_checked

end ClaudeWCT.Numerics.CanonicalCompression

-- moved from N600PriceChecks (lines 499-534)
namespace ClaudeWCT.Numerics.CanonicalHistogram
open CanonicalCompression
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 10000000
set_option Elab.async false
/-- The raw lower counts are the weight-201 coefficients of the lower generating polynomial (zero bound 5). -/
def lowerHistogramCheck : Bool :=
  let p := SigGolfResearch.LowerEffectiveCounting.packed
  let actual := (List.range 6).foldl (fun s zeros =>
    s + ((p >>> (132 * (65536 * zeros + 128 * 201))) % 2 ^ (132 * 128))) 0
  decide (packHistogram 132 0 128 lowerCounts = actual)


theorem lower_histogram_checked : lowerHistogramCheck = true := by decide +kernel


#print axioms lower_histogram_checked

end ClaudeWCT.Numerics.CanonicalHistogram

-- moved from N600PriceChecks (lines 1470-1520)
namespace ClaudeWCT.Numerics.CanonicalCompression
open ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem initialBound_ge_scale : scale ≤ initialBound := by norm_num [scale,initialBound]

theorem envelope_ratio_le_two : ((fixedBound:ℝ)/scale)*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hmul := mulUp_ratio_ge fixedBound ftsBound
  have hmul2 := mulUp_ratio_ge (mulUp fixedBound ftsBound) initialBound
  have hnum : (mulUp (mulUp fixedBound ftsBound) initialBound:ℝ)/scale<199896/100000 := by
    have hn := full_moment_checked
    have hreal : (mulUp (mulUp fixedBound ftsBound) initialBound:ℝ)*100000<199896*(scale:ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  calc
    _ = (((fixedBound:ℝ)/scale)*((ftsBound:ℝ)/scale))*((initialBound:ℝ)/scale) := by ring
    _ ≤ ((mulUp fixedBound ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale) := by gcongr
    _ ≤ _ := hmul2
    _ ≤ 2 := hnum.le.trans (by norm_num)

#print axioms envelope_ratio_le_two

end ClaudeWCT.Numerics.CanonicalCompression




-- moved from N600Price (lines 5366-5390)
namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset
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

-- moved from N600Price (lines 5736-5756)
namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
set_option quotPrecheck false
theorem counting_digit_eq (bits p i : Nat) :
    CanonicalCounting.digit bits p i = SharedDigitBlock.digit (2^bits) p i :=
  bits_digit_eq bits p i

end ClaudeWCT.Numerics.CanonicalHistogram

-- moved from N600Price (lines 5919-5938)
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

-- moved from N600Price (lines 6125-6169)
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

-- moved from N600Price (lines 6287-6303)
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

-- moved from N600Price (lines 6785-6801)
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

/-- Campaign R6 + RC: the exact top credit law (credits `≥ 16`) is the packet histogram `topCounts`. -/
theorem topWordCount_eq (r : Nat) (h16 : 16 ≤ r) : topWordCount r = histogramWeight topCounts r := by
  rw [ClaudeWCT.W9.T3.ProducerV5.Canonical.topWordCount_eq r h16, histogramWeight_sum]
  rfl

theorem topHighWeight_eq : topHighWeight = topHighW := rfl

/-- The e7b top selection law at the canonical floor 19 (R6 + RC). -/
theorem selected_top_histogram_card (c : Nat) (hc : 19 ≤ c) (hc' : c < 220) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight topAcceptedHistogram c := by
  rw [selected_top_path_card 19 c le_rfl hc, topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 3 ≤ c), topWordCount_eq (c - 3) (by omega),
    topWordCount_eq c (by omega), topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (c : Nat) (hc : 19 ≤ c) (hc' : c < 220) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 19 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) = _ from rfl, selected_top_histogram_card c hc hc']
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
