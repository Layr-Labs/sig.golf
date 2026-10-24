import SigGolfCandidate.T3_Nonbinary_Codec
import SigGolfCandidate.T3_Nonbinary_LowerLayout
import SigGolfCandidate.T3_Nonbinary_TopFlip

namespace SigGolfCandidate.T3.Nonbinary
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem coreDigit_le (lay : Layer) (value : Digest) (i : Nat) :
    coreDigit lay value i ≤  maxDigit lay i := by
  unfold coreDigit maxDigit
  split_ifs
  all_goals have h := Nat.mod_lt (value.toNat / 2 ^ (3*i)) (by decide : 0<8)
  all_goals first | exact Nat.le_pred_of_lt (Nat.mod_lt _ (by decide)) | omega
theorem maxDigit_lt_pow_width (lay : Layer) (i : Nat) : maxDigit lay i<2^width lay i := by
  unfold maxDigit width
  split_ifs <;> decide
theorem dataDigits_getD (lay : Layer) (value : Digest) (i : Nat) (hi : i<dataCount lay) :
    (dataDigits lay value).getD i 0=coreDigit lay value i := by
  simp [dataDigits,List.getD_eq_getElem,hi]
/-! ### Campaign T51: the top word (r6 g0..g8, r5 q9..q15, r7 pair; no spare bit) -/
theorem topRanksValid_parts {v : Digest} (h : topRanksValid v = true) :
    (∀ g, g < 9 → r6Valid v g = true) ∧ (∀ q, 9 ≤ q → q < 16 → r5Rank v q < 125) ∧ r7Rank v < 49 := by
  unfold topRanksValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1] at h
  obtain ⟨⟨h6, h5⟩, h7⟩ := h
  exact ⟨h6, fun q h1 h2 => h5 q ⟨h1, by omega⟩, h7⟩
theorem r6Rank_lt {v : Digest} {g : Nat} (h : r6Valid v g = true) : r6Rank v g < 216 := by
  have hr := Nat.mod_lt (topCode v / 2 ^ r6Shift g) (show 0 < 256 by decide)
  unfold r6Valid at h
  unfold r6Rank
  split_ifs at h ⊢ with hg
  · subst hg; simp only [decide_eq_true_eq] at h; unfold r6Raw at h ⊢; omega
  · simpa only [decide_eq_true_eq] using h
theorem rank6_eq {r s : Nat} (hr : r < 216) (hs : s < 216)
    (h0 : r % 6 = s % 6) (h1 : r / 6 % 6 = s / 6 % 6) (h2 : r / 36 % 6 = s / 36 % 6) : r = s := by omega
theorem rank5_eq {r s : Nat} (hr : r < 125) (hs : s < 125)
    (h0 : r % 5 = s % 5) (h1 : r / 5 % 5 = s / 5 % 5) (h2 : r / 25 % 5 = s / 25 % 5) : r = s := by omega
theorem rank7_eq {r s : Nat} (hr : r < 49) (hs : s < 49)
    (h0 : r % 7 = s % 7) (h1 : r / 7 % 7 = s / 7 % 7) : r = s := by omega
theorem top_core_r6 (v : Digest) (g k : Nat) (hg : g < 9) (hk : k < 3) :
    coreDigit 0 v (3*g+k) = r6Rank v g / 6^k % 6 := by
  have hi : 3*g+k < 27 := by omega
  have hd : (3*g+k)/3 = g := by omega
  have hm : (3*g+k)%3 = k := by omega
  simp [coreDigit, hi, hd, hm]
theorem top_core_r5 (v : Digest) (q k : Nat) (hq1 : 9 ≤ q) (hq : q < 16) (hk : k < 3) :
    coreDigit 0 v (3*q+k) = r5Rank v q / 5^k % 5 := by
  have hi : ¬ 3*q+k < 27 := by omega
  have hi' : 3*q+k < 48 := by omega
  have hd : (3*q+k)/3 = q := by omega
  have hm : (3*q+k)%3 = k := by omega
  simp [coreDigit, hi, hi', hd, hm]
theorem top_core_r7 (v : Digest) (k : Nat) (hk : k < 2) :
    coreDigit 0 v (48+k) = r7Rank v / 7^k % 7 := by
  have hi : ¬ 48+k < 27 := by omega
  have hi' : ¬ 48+k < 48 := by omega
  have hi'' : 48+k < 50 := by omega
  simp [coreDigit, hi, hi', hi'']
theorem top_r6Rank_eq {a b : Digest} {g : Nat} (h : dataDigits 0 a = dataDigits 0 b)
    (ha : r6Valid a g = true) (hb : r6Valid b g = true) (hg : g < 9) : r6Rank a g = r6Rank b g := by
  have hpos (k : Nat) (hk : k < 3) : r6Rank a g / 6^k % 6 = r6Rank b g / 6^k % 6 := by
    have hi : 3*g+k < dataCount 0 := by change 3*g+k < 50; omega
    have hh := congrArg (fun xs : List Nat => xs.getD (3*g+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi, dataDigits_getD 0 b _ hi, top_core_r6 _ _ _ hg hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hpos 2 (by decide)
  norm_num only [Nat.reducePow, Nat.div_one] at h0 h1 h2
  exact rank6_eq (r6Rank_lt ha) (r6Rank_lt hb) h0 h1 h2
theorem top_r5Rank_eq {a b : Digest} {q : Nat} (h : dataDigits 0 a = dataDigits 0 b)
    (ha : r5Rank a q < 125) (hb : r5Rank b q < 125) (hq1 : 9 ≤ q) (hq : q < 16) : r5Rank a q = r5Rank b q := by
  have hpos (k : Nat) (hk : k < 3) : r5Rank a q / 5^k % 5 = r5Rank b q / 5^k % 5 := by
    have hi : 3*q+k < dataCount 0 := by change 3*q+k < 50; omega
    have hh := congrArg (fun xs : List Nat => xs.getD (3*q+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi, dataDigits_getD 0 b _ hi, top_core_r5 _ _ _ hq1 hq hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hpos 2 (by decide)
  norm_num only [Nat.reducePow, Nat.div_one] at h0 h1 h2
  exact rank5_eq ha hb h0 h1 h2
theorem top_r7Rank_eq {a b : Digest} (h : dataDigits 0 a = dataDigits 0 b)
    (ha : r7Rank a < 49) (hb : r7Rank b < 49) : r7Rank a = r7Rank b := by
  have hpos (k : Nat) (hk : k < 2) : r7Rank a / 7^k % 7 = r7Rank b / 7^k % 7 := by
    have hi : 48+k < dataCount 0 := by change 48+k < 50; omega
    have hh := congrArg (fun xs : List Nat => xs.getD (48+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi, dataDigits_getD 0 b _ hi, top_core_r7 _ _ hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  norm_num only [Nat.reducePow, Nat.div_one] at h0 h1
  exact rank7_eq ha hb h0 h1
theorem r6Raw_eq_of_rank {a b : Digest} {g : Nat} (ha : r6Valid a g = true) (hb : r6Valid b g = true)
    (h : r6Rank a g = r6Rank b g) : r6Raw a g = r6Raw b g := by
  unfold r6Valid at ha hb
  unfold r6Rank at h
  split_ifs at ha hb h with hg
  · subst hg; simp only [decide_eq_true_eq] at ha hb; omega
  · exact h
/-- Campaign T51: the top data digits determine the whole 128-bit value of a valid word (9 r6 fields, 7 flipped r5
fields, the flipped r7 field; the fields partition bits 0..127, no spare bit). Decoding is injective (PINNED P3a). -/
theorem top_digest_injective {a b : Digest} (h : dataDigits 0 a=dataDigits 0 b)
    (ha : topRanksValid a=true) (hb : topRanksValid b=true) : a=b := by
  obtain ⟨h6a, h5a, h7a⟩ := topRanksValid_parts ha
  obtain ⟨h6b, h5b, h7b⟩ := topRanksValid_parts hb
  apply topFlip_injective
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have window : ∀ s w, s ≤ bit → bit < s + w → topCode a / 2^s % 2^w = topCode b / 2^s % 2^w →
      (topFlip a).getLsbD bit = (topFlip b).getLsbD bit := by
    intro s w h1 h2 he
    have hx : (topFlip a).extractLsb' s w = (topFlip b).extractLsb' s w := by
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, topCode] using he
    have hh := congrArg (fun d : BitVec w => d.getLsbD (bit - s)) hx
    simpa only [BitVec.getLsbD_extractLsb', show bit - s < w by omega, decide_true,
      Bool.true_and, show s + (bit - s) = bit by omega] using hh
  have r6win : ∀ g, g < 9 → r6Shift g ≤ bit → bit < r6Shift g + 8 →
      (topFlip a).getLsbD bit = (topFlip b).getLsbD bit := by
    intro g hg h1 h2
    have hr := top_r6Rank_eq h (h6a _ hg) (h6b _ hg) hg
    have hw := r6Raw_eq_of_rank (h6a _ hg) (h6b _ hg) hr
    unfold r6Raw at hw
    exact window (r6Shift g) 8 h1 h2 (by simpa using hw)
  by_cases h1 : bit < 56
  · exact r6win (bit / 8) (by omega) (by unfold r6Shift; rw [if_pos (by omega)]; omega)
      (by unfold r6Shift; rw [if_pos (by omega)]; omega)
  by_cases h2 : bit < 63
  · have hr := top_r7Rank_eq h h7a h7b
    unfold r7Rank at hr
    exact window 56 7 (by omega) (by omega) (by simpa using hr)
  by_cases h3 : bit < 112
  · have hq1 : 9 ≤ bit / 7 := by omega
    have hq2 : bit / 7 < 16 := by omega
    have hr := top_r5Rank_eq h (h5a _ hq1 hq2) (h5b _ hq1 hq2) hq1 hq2
    unfold r5Rank at hr
    exact window (7 * (bit / 7)) 7 (by omega) (by omega) (by simpa using hr)
  by_cases h4 : bit < 120
  · exact r6win 7 (by decide) (by unfold r6Shift; rw [if_neg (by omega)]; omega)
      (by unfold r6Shift; rw [if_neg (by omega)]; omega)
  · exact r6win 8 (by decide) (by unfold r6Shift; rw [if_neg (by omega)]; omega)
      (by unfold r6Shift; rw [if_neg (by omega)]; omega)
end SigGolfCandidate.T3.Nonbinary
