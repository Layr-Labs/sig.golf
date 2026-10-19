import SigGolfCandidate.T3.Nonbinary.LowerLayout
import SigGolfCandidate.T3.Nonbinary.TopFlip

namespace SigGolfCandidate.T3.Nonbinary
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem searchDecode_some {lay : Layer} {value : Digest} {digits : List Nat}
    (h : searchDecode lay value=some digits) : decode lay value=some digits := by
  unfold searchDecode at h
  by_cases hc : encCredit lay value<creditFloor lay
  · rw [if_pos hc] at h; cases h
  · rwa [if_neg hc] at h
theorem coreDigit_le (lay : Layer) (value : Digest) (i : Nat) :
    coreDigit lay value i ≤  maxDigit lay i := by
  unfold coreDigit maxDigit
  split_ifs <;> omega
theorem maxDigit_lt_pow_width (lay : Layer) (i : Nat) : maxDigit lay i<2^width lay i := by
  unfold maxDigit width
  split_ifs <;> decide
theorem dataDigits_getD (lay : Layer) (value : Digest) (i : Nat) (hi : i<dataCount lay) :
    (dataDigits lay value).getD i 0=coreDigit lay value i := by
  simp [dataDigits,List.getD_eq_getElem,hi]
/-! ### Campaign R6: the top word (design D1c) -/
theorem topRanksValid_parts {v : Digest} (h : topRanksValid v = true) :
    topSpare v = 0 ∧ (∀ g, g < 8 → r6Valid v g = true) ∧ (∀ q, 8 ≤ q → q < 17 → r5Rank v q < 125) := by
  unfold topRanksValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1] at h
  obtain ⟨⟨hs, h6⟩, h5⟩ := h
  exact ⟨hs, h6, fun q h1 h2 => h5 q ⟨h1, by omega⟩⟩
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
theorem top_core_r6 (v : Digest) (g k : Nat) (hg : g < 8) (hk : k < 3) :
    coreDigit 0 v (3*g+k) = r6Rank v g / 6^k % 6 := by
  have hi : 3*g+k < 24 := by omega
  have hd : (3*g+k)/3 = g := by omega
  have hm : (3*g+k)%3 = k := by omega
  simp [coreDigit, hi, hd, hm]
theorem top_core_r5 (v : Digest) (q k : Nat) (hq1 : 8 ≤ q) (hq : q < 17) (hk : k < 3) :
    coreDigit 0 v (3*q+k) = r5Rank v q / 5^k % 5 := by
  have hi : ¬ 3*q+k < 24 := by omega
  have hi' : 3*q+k < 51 := by omega
  have hd : (3*q+k)/3 = q := by omega
  have hm : (3*q+k)%3 = k := by omega
  simp [coreDigit, hi, hi', hd, hm]
theorem top_r6Rank_eq {a b : Digest} {g : Nat} (h : dataDigits 0 a = dataDigits 0 b)
    (ha : r6Valid a g = true) (hb : r6Valid b g = true) (hg : g < 8) : r6Rank a g = r6Rank b g := by
  have hpos (k : Nat) (hk : k < 3) : r6Rank a g / 6^k % 6 = r6Rank b g / 6^k % 6 := by
    have hi : 3*g+k < dataCount 0 := by change 3*g+k < 51; omega
    have hh := congrArg (fun xs : List Nat => xs.getD (3*g+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi, dataDigits_getD 0 b _ hi, top_core_r6 _ _ _ hg hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hpos 2 (by decide)
  norm_num only [Nat.reducePow, Nat.div_one] at h0 h1 h2
  exact rank6_eq (r6Rank_lt ha) (r6Rank_lt hb) h0 h1 h2
theorem top_r5Rank_eq {a b : Digest} {q : Nat} (h : dataDigits 0 a = dataDigits 0 b)
    (ha : r5Rank a q < 125) (hb : r5Rank b q < 125) (hq1 : 8 ≤ q) (hq : q < 17) : r5Rank a q = r5Rank b q := by
  have hpos (k : Nat) (hk : k < 3) : r5Rank a q / 5^k % 5 = r5Rank b q / 5^k % 5 := by
    have hi : 3*q+k < dataCount 0 := by change 3*q+k < 51; omega
    have hh := congrArg (fun xs : List Nat => xs.getD (3*q+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi, dataDigits_getD 0 b _ hi, top_core_r5 _ _ _ hq1 hq hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hpos 2 (by decide)
  norm_num only [Nat.reducePow, Nat.div_one] at h0 h1 h2
  exact rank5_eq ha hb h0 h1 h2
theorem r6Raw_eq_of_rank {a b : Digest} {g : Nat} (ha : r6Valid a g = true) (hb : r6Valid b g = true)
    (h : r6Rank a g = r6Rank b g) : r6Raw a g = r6Raw b g := by
  unfold r6Valid at ha hb
  unfold r6Rank at h
  split_ifs at ha hb h with hg
  · subst hg; simp only [decide_eq_true_eq] at ha hb; omega
  · exact h
/-- Campaign R6: the top data digits determine the whole 128-bit value of a valid word (8 r6 fields, 9 flipped r5
fields, spare bit 0). Decoding is injective; with a free spare bit it would not be (SEC R1). -/
theorem top_digest_injective {a b : Digest} (h : dataDigits 0 a=dataDigits 0 b)
    (ha : topRanksValid a=true) (hb : topRanksValid b=true) : a=b := by
  obtain ⟨hsa, h6a, h5a⟩ := topRanksValid_parts ha
  obtain ⟨hsb, h6b, h5b⟩ := topRanksValid_parts hb
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
  by_cases h1 : bit < 56
  · have hg : bit / 8 < 8 := by omega
    have hr := top_r6Rank_eq h (h6a _ hg) (h6b _ hg) hg
    have hw := r6Raw_eq_of_rank (h6a _ hg) (h6b _ hg) hr
    unfold r6Raw r6Shift at hw
    rw [if_neg (by omega)] at hw
    exact window (8 * (bit / 8)) 8 (by omega) (by omega) (by simpa using hw)
  by_cases h2 : bit < 119
  · have hq1 : 8 ≤ bit / 7 := by omega
    have hq2 : bit / 7 < 17 := by omega
    have hr := top_r5Rank_eq h (h5a _ hq1 hq2) (h5b _ hq1 hq2) hq1 hq2
    unfold r5Rank at hr
    exact window (7 * (bit / 7)) 7 (by omega) (by omega) (by simpa using hr)
  by_cases h3 : bit < 127
  · have hr := top_r6Rank_eq h (h6a 7 (by decide)) (h6b 7 (by decide)) (by decide)
    have hw := r6Raw_eq_of_rank (h6a 7 (by decide)) (h6b 7 (by decide)) hr
    unfold r6Raw r6Shift at hw
    rw [if_pos rfl] at hw
    exact window 119 8 (by omega) (by omega) (by simpa using hw)
  · unfold topSpare at hsa hsb
    exact window 127 1 (by omega) (by omega) (by simpa using hsa.trans hsb.symm)
end SigGolfCandidate.T3.Nonbinary
