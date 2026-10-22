import SigGolfCandidate.T3M_Search_CounterSearch
import SigGolfCandidate.T3M_Search_Selector
import SigGolfCandidate.T3M_Search_CreditBlock
import SigGolfCandidate.T3M_Search_ZeroBlocks
import SigGolfCandidate.T3M_Search_ZeroCap
import SigGolfCandidate.ClaudeWCT_WCT9_TopDecode
import SigGolfCandidate.T3_Nonbinary_CreditFilter

section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option Elab.async false
set_option maxRecDepth 8192
/-- Per-layer counter window of the img-v4/v6 check `((s0 + 3) >> 1) << 20`. -/
def capLimit (lay : Nat) : Nat := (min lay 3 + 3) / 2 * 2 ^ 20
def scanM : BitVec 64 := 1317624576693539401#64
def lanes6 (x : BitVec 64) : BitVec 64 := x >>> 1 &&& x >>> 2 &&& (x ^^^ 18446744073709551615#64) &&& scanM
def scanX (c lo hi : BitVec 64) : BitVec 64 :=
  (if (c - 6#64).ult 1#64 = true then 1#64 else 0#64) <<< 63 ||| lanes6 lo ||| lanes6 hi <<< 1
theorem scanM_getLsbD (j : Nat) (hj : j < 64) : scanM.getLsbD j = decide (j % 3 = 0 ∧ j ≤ 60) := by
  revert j; decide
theorem lanes6_getLsbD (x : BitVec 64) (j : Nat) (hj : j < 64) :
    (lanes6 x).getLsbD j =
      (decide (j % 3 = 0 ∧ j ≤ 60) && (x.getLsbD (j + 1) && x.getLsbD (j + 2) && !x.getLsbD j)) := by
  unfold lanes6
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, scanM_getLsbD j hj]
  have hall : (18446744073709551615#64).getLsbD j = true := by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes]; simp [hj]
  rw [hall, Nat.add_comm 1 j, Nat.add_comm 2 j]
  cases x.getLsbD (j + 1) <;> cases x.getLsbD (j + 2) <;> cases x.getLsbD j <;>
    cases decide (j % 3 = 0 ∧ j ≤ 60) <;> rfl
theorem digit_eq_six_iff (n j : Nat) :
    n / 2 ^ j % 8 = 6 ↔ (n.testBit (j + 1) = true ∧ n.testBit (j + 2) = true ∧ n.testBit j = false) := by
  have hr : n / 2 ^ j % 8 < 8 := Nat.mod_lt _ (by decide)
  have h0 : n.testBit j = (n / 2 ^ j % 8).testBit 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp
  have h1 : n.testBit (j + 1) = (n / 2 ^ j % 8).testBit 1 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [Nat.add_comm]
  have h2 : n.testBit (j + 2) = (n / 2 ^ j % 8).testBit 2 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [Nat.add_comm]
  rw [h0, h1, h2]
  generalize n / 2 ^ j % 8 = r at hr ⊢
  revert r; decide
theorem lane_bits (v : Digest) (k : Nat) :
    (v.getLsbD (k + 1) && v.getLsbD (k + 2) && !v.getLsbD k) = decide (v.toNat / 2 ^ k % 8 = 6) := by
  have := digit_eq_six_iff v.toNat k
  simp only [BitVec.getLsbD] at *
  by_cases h : v.toNat / 2 ^ k % 8 = 6
  · obtain ⟨a, b, c⟩ := this.mp h; simp [a, b, c, h]
  · rw [decide_eq_false h]
    cases ha : v.toNat.testBit (k + 1) <;> cases hb : v.toNat.testBit (k + 2) <;> cases hc : v.toNat.testBit k <;>
      simp_all
theorem flag_six (c : Nat) (hc : c < 8) :
    ((BitVec.ofNat 64 c - 6#64).ult 1#64 = true) ↔ c = 6 := by
  revert c; decide
theorem flag_getLsbD (c : Nat) (hc : c < 8) (j : Nat) (hj : j < 64) :
    ((if (BitVec.ofNat 64 c - 6#64).ult 1#64 = true then 1#64 else 0#64) <<< 63 : BitVec 64).getLsbD j =
      (decide (j = 63) && decide (c = 6)) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h6 : c = 6
  · subst h6
    rw [if_pos (by decide)]
    by_cases hj63 : j = 63
    · subst hj63; decide
    · have : ¬ (j < 63) → False := fun h => hj63 (by omega)
      by_cases hlt : j < 63
      · simp [hlt, hj63]
      · exact (this hlt).elim
  · rw [if_neg (fun h => h6 ((flag_six c hc).mp h))]
    simp [h6]
theorem scanX_getLsbD (v : Digest) (c : Nat) (hc : c < 8) (j : Nat) (hj : j < 64) :
    (scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64)).getLsbD j =
      (if j = 63 then decide (c = 6)
       else if j % 3 = 0 then decide (v.toNat / 2 ^ (3 * (j / 3)) % 8 = 6)
       else if j % 3 = 1 then decide (v.toNat / 2 ^ (64 + 3 * (j / 3)) % 8 = 6)
       else false) := by
  unfold scanX
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, flag_getLsbD c hc j hj, lanes6_getLsbD _ j hj,
    BitVec.getLsbD_shiftLeft]
  have hlo : ∀ k, k < 64 → (v.extractLsb' 0 64).getLsbD k = v.getLsbD k := by
    intro k hk; simp [hk]
  have hhi : ∀ k, k < 64 → (v.extractLsb' 64 64).getLsbD k = v.getLsbD (64 + k) := by
    intro k hk; simp [hk]
  by_cases h63 : j = 63
  · subst h63
    rw [lanes6_getLsbD _ 62 (by decide)]
    simp
  · simp only [h63, decide_false, Bool.false_and, Bool.false_or, if_false, hj, decide_true, Bool.true_and]
    have hm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    ·
      have hj60 : j ≤ 60 := by omega
      have hshift : (!decide (j < 1) && (lanes6 (v.extractLsb' 64 64)).getLsbD (j - 1)) = false := by
        by_cases h0 : j = 0
        · subst h0; simp
        · rw [lanes6_getLsbD _ (j - 1) (by omega)]
          simp [show ¬ (j - 1) % 3 = 0 by omega]
      rw [hshift, Bool.or_false, if_pos hm, show 3 * (j / 3) = j by omega,
        hlo (j + 1) (by omega), hlo (j + 2) (by omega), hlo j (by omega), lane_bits]
      simp [hm, hj60]
    ·
      have hlo0 : (decide (j % 3 = 0 ∧ j ≤ 60) && ((v.extractLsb' 0 64).getLsbD (j + 1) &&
          (v.extractLsb' 0 64).getLsbD (j + 2) && !(v.extractLsb' 0 64).getLsbD j)) = false := by
        simp [hm]
      rw [hlo0, Bool.false_or, if_neg (by omega), if_pos hm, lanes6_getLsbD _ (j - 1) (by omega),
        hhi _ (by omega), hhi _ (by omega), hhi _ (by omega),
        show 64 + (j - 1 + 1) = 64 + (j - 1) + 1 by omega, show 64 + (j - 1 + 2) = 64 + (j - 1) + 2 by omega,
        lane_bits, show 64 + (j - 1) = 64 + 3 * (j / 3) by omega]
      simp [show (j - 1) % 3 = 0 by omega, show j - 1 ≤ 60 by omega, show ¬ j < 1 by omega]
    ·
      have hlo0 : (decide (j % 3 = 0 ∧ j ≤ 60) && ((v.extractLsb' 0 64).getLsbD (j + 1) &&
          (v.extractLsb' 0 64).getLsbD (j + 2) && !(v.extractLsb' 0 64).getLsbD j)) = false := by
        simp [hm]
      rw [hlo0, Bool.false_or, if_neg (by omega), if_neg (by omega), lanes6_getLsbD _ (j - 1) (by omega)]
      simp [show ¬ (j - 1) % 3 = 0 by omega]
def clr (x : BitVec 64) : BitVec 64 := x &&& (x - 1#64)
def pop (x : BitVec 64) : Nat := ∑ j ∈ Finset.range 64, if x.getLsbD j then 1 else 0
def scanCredit (v : Digest) (c : Nat) : Nat :=
  ∑ i ∈ Finset.range 43, if (lowDigits v ++ [c]).getD i 0 = 6 then 1 else 0
theorem pop_eq_zero_iff (x : BitVec 64) : pop x = 0 ↔ x = 0#64 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hle := Finset.single_le_sum (f := fun j => if x.getLsbD j then 1 else 0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
    unfold pop at h
    rw [h] at hle
    simp only [BitVec.getLsbD_zero]
    by_contra hb
    simp only [Bool.not_eq_false] at hb
    simp [hb] at hle
  · rintro rfl; simp [pop]
theorem exists_lowest_bit {n : Nat} (hn : n ≠ 0) :
    ∃ m, n.testBit m = true ∧ ∀ j < m, n.testBit j = false := by
  classical
  have hex : ∃ i, n.testBit i = true := Nat.exists_testBit_of_ne_zero hn
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_⟩
  have := Nat.find_min hex hj
  simpa using this
theorem testBit_and_sub_one {n m : Nat} (hm : n.testBit m = true) (hlow : ∀ j < m, n.testBit j = false) (j : Nat) :
    (n &&& (n - 1)).testBit j = (n.testBit j && decide (j ≠ m)) := by
  have hmod : n % 2 ^ (m + 1) = 2 ^ m := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hi : i < m + 1
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · simp [hi, hlow i hi, Nat.ne_of_gt hi]
      · simp [hm]
    · simp [hi]; omega
  have hn : n = 2 ^ (m + 1) * (n / 2 ^ (m + 1)) + 2 ^ m := by
    have := Nat.div_add_mod n (2 ^ (m + 1)); rw [hmod] at this; omega
  generalize n / 2 ^ (m + 1) = q at hn
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hn1 : n - 1 = 2 ^ (m + 1) * q + (2 ^ m - 1) := by omega
  have hlt1 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hlt2 : 2 ^ m - 1 < 2 ^ (m + 1) := by omega
  rw [Nat.testBit_and, hn1, hn, Nat.testBit_two_pow_mul_add _ hlt1, Nat.testBit_two_pow_mul_add _ hlt2]
  by_cases hj : j < m + 1
  · simp only [hj, if_true, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hjm : j = m
    · subst hjm; simp
    · have : j < m := by omega
      simp [hjm, Nat.ne_of_gt this]
  · simp only [hj, if_false]
    have : j ≠ m := by omega
    simp [this]
theorem pop_clr {x : BitVec 64} (hx : x ≠ 0#64) : pop (clr x) = pop x - 1 := by
  have hn : x.toNat ≠ 0 := by
    intro h; apply hx; apply BitVec.eq_of_toNat_eq; simpa using h
  obtain ⟨m, hm, hlow⟩ := exists_lowest_bit hn
  have hm64 : m < 64 := by
    by_contra hge
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ m)))
    rw [hm] at this; cases this
  have hclr : ∀ j, (clr x).getLsbD j = (x.getLsbD j && decide (j ≠ m)) := by
    intro j
    have e : (clr x).toNat = x.toNat &&& (x.toNat - 1) := by
      unfold clr
      rw [BitVec.toNat_and, BitVec.toNat_sub]
      congr 1
      have := x.isLt
      rw [show (1#64).toNat = 1 from rfl, show 2 ^ 64 - 1 + x.toNat = 2 ^ 64 + (x.toNat - 1) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [BitVec.getLsbD, e]
    exact testBit_and_sub_one hm hlow j
  unfold pop
  simp only [hclr]
  have hmem : m ∈ Finset.range 64 := Finset.mem_range.mpr hm64
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hxm : x.getLsbD m = true := by simpa [BitVec.getLsbD] using hm
  have hrest : ∑ j ∈ (Finset.range 64).erase m, (if (x.getLsbD j && decide (j ≠ m)) = true then 1 else 0) =
      ∑ j ∈ (Finset.range 64).erase m, (if x.getLsbD j = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have : j ≠ m := Finset.ne_of_mem_erase hj
    simp [this]
  rw [hrest, hxm]
  simp
theorem clr_zero : clr 0#64 = 0#64 := by decide
theorem clr_iter_eq_zero_iff (k : Nat) (x : BitVec 64) : (clr^[k] x = 0#64) ↔ pop x ≤ k := by
  induction k generalizing x with
  | zero => simp [pop_eq_zero_iff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hx : x = 0#64
    · subst hx; rw [clr_zero]; simp [(pop_eq_zero_iff _).mpr rfl]
    · rw [pop_clr hx]
      have : pop x ≠ 0 := fun h => hx ((pop_eq_zero_iff x).mp h)
      omega
theorem sum_range_three (n : Nat) (f : Nat → Nat) :
    ∑ j ∈ Finset.range (3 * n), f j = ∑ a ∈ Finset.range n, (f (3 * a) + f (3 * a + 1) + f (3 * a + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
theorem getD_lowDigits_append (v : Digest) (c i : Nat) :
    (lowDigits v ++ [c]).getD i 0 =
      if i < 42 then v.toNat / 2 ^ T3.lowerShift i % 8 else if i = 42 then c else 0 := by
  by_cases hi : i < 42
  · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length]; exact hi), if_pos hi]
    simp [lowDigits, List.getD_eq_getElem?_getD, hi]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by rw [lowDigits_length]; omega), lowDigits_length]
    by_cases h42 : i = 42
    · subst h42; simp
    · rw [if_neg h42, List.getD_eq_default _ _ (by simp; omega)]
theorem pop_scanX (v : Digest) (c : Nat) (hc : c < 8) :
    pop (scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64)) = scanCredit v c := by
  have hX := scanX_getLsbD v c hc
  generalize scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64) = X at hX ⊢
  let f : Nat → Nat := fun j => if X.getLsbD j then 1 else 0
  let g : Nat → Nat := fun i => if (lowDigits v ++ [c]).getD i 0 = 6 then 1 else 0
  let d : Nat → Nat := fun i => if v.toNat / 2 ^ T3.lowerShift i % 8 = 6 then 1 else 0
  have e0 : ∀ a < 21, f (3 * a) = d a := by
    intro a ha
    have h1 : ¬ (3 * a = 63) := by omega
    have h2 : (3 * a) % 3 = 0 := by omega
    have h3 : 3 * a / 3 = a := by omega
    have hs : T3.lowerShift a = 3 * a := by simp [T3.lowerShift, ha]
    simp only [f, d, hX _ (show 3 * a < 64 by omega), if_neg h1, if_pos h2, h3, hs]
    by_cases h : v.toNat / 2 ^ (3 * a) % 8 = 6 <;> simp [h]
  have e1 : ∀ a < 21, f (3 * a + 1) = d (21 + a) := by
    intro a ha
    have h1 : ¬ (3 * a + 1 = 63) := by omega
    have h2 : ¬ ((3 * a + 1) % 3 = 0) := by omega
    have h2' : (3 * a + 1) % 3 = 1 := by omega
    have h3 : (3 * a + 1) / 3 = a := by omega
    have hs : T3.lowerShift (21 + a) = 64 + 3 * a := by simp [T3.lowerShift]
    simp only [f, d, hX _ (show 3 * a + 1 < 64 by omega), if_neg h1, if_neg h2, if_pos h2', h3, hs]
    by_cases h : v.toNat / 2 ^ (64 + 3 * a) % 8 = 6 <;> simp [h]
  have e2 : ∀ a < 21, f (3 * a + 2) = 0 := by
    intro a ha
    have h1 : ¬ (3 * a + 2 = 63) := by omega
    have h2 : ¬ ((3 * a + 2) % 3 = 0) := by omega
    have h2' : ¬ ((3 * a + 2) % 3 = 1) := by omega
    simp only [f, hX _ (show 3 * a + 2 < 64 by omega), if_neg h1, if_neg h2, if_neg h2']
    rfl
  have e63 : f 63 = if c = 6 then 1 else 0 := by
    simp only [f, hX 63 (by omega)]; by_cases h : c = 6 <;> simp [h]
  have g0 : ∀ i < 42, g i = d i := by
    intro i hi; simp only [g, d, getD_lowDigits_append, if_pos hi]
  have g42 : g 42 = if c = 6 then 1 else 0 := by
    simp only [g]; rw [getD_lowDigits_append]; simp
  have hL : pop X = ∑ a ∈ Finset.range 21, (f (3 * a) + f (3 * a + 1) + f (3 * a + 2)) + f 63 := by
    have : pop X = ∑ j ∈ Finset.range (3 * 21 + 1), f j := rfl
    rw [this, Finset.sum_range_succ, sum_range_three]
  have hR : scanCredit v c = (∑ a ∈ Finset.range 21, g a + ∑ a ∈ Finset.range 21, g (21 + a)) + g 42 := by
    have : scanCredit v c = ∑ i ∈ Finset.range (21 + 21 + 1), g i := rfl
    rw [this, Finset.sum_range_succ, Finset.sum_range_add]
  rw [hL, hR, e63, g42, ← Finset.sum_add_distrib]
  apply congrArg (· + (if c = 6 then 1 else 0))
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  rw [e0 a ha', e1 a ha', e2 a ha', g0 a (by omega), g0 (21 + a) (by omega), Nat.add_zero]
theorem digit_eq_zero_iff (n j : Nat) :
    n / 2 ^ j % 8 = 0 ↔ (n.testBit (j + 1) = false ∧ n.testBit (j + 2) = false ∧ n.testBit j = false) := by
  have hr : n / 2 ^ j % 8 < 8 := Nat.mod_lt _ (by decide)
  have h0 : n.testBit j = (n / 2 ^ j % 8).testBit 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp
  have h1 : n.testBit (j + 1) = (n / 2 ^ j % 8).testBit 1 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [Nat.add_comm]
  have h2 : n.testBit (j + 2) = (n / 2 ^ j % 8).testBit 2 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [Nat.add_comm]
  rw [h0, h1, h2]
  generalize n / 2 ^ j % 8 = r at hr ⊢
  revert r; decide

theorem lanes0_getLsbD (x : BitVec 64) (j : Nat) (hj : j < 64) :
    (Zero.lanes0 x).getLsbD j =
      (decide (j % 3 = 0 ∧ j ≤ 60) && decide (x.toNat / 2 ^ j % 8 = 0)) := by
  have hM := scanM_getLsbD j hj
  have hall : (18446744073709551615#64).getLsbD j = true := by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes]; simp [hj]
  unfold Zero.lanes0
  change (((x >>> 1 ||| x ||| x >>> 2) ^^^ 18446744073709551615#64) &&& scanM).getLsbD j = _
  rw [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, hM, hall]
  have hz := digit_eq_zero_iff x.toNat j
  simp only [BitVec.getLsbD, Nat.add_comm 1 j, Nat.add_comm 2 j]
  cases ha : x.toNat.testBit (j + 1) <;> cases hb : x.toNat.testBit (j + 2) <;>
    cases hc : x.toNat.testBit j <;> simp_all

theorem pop_lanes0 (x : BitVec 64) :
    pop (Zero.lanes0 x) = ∑ i ∈ Finset.range 21, if x.toNat / 2 ^ (3 * i) % 8 = 0 then 1 else 0 := by
  let f : Nat → Nat := fun j => if (Zero.lanes0 x).getLsbD j then 1 else 0
  have hz : f 63 = 0 := by
    change (if (Zero.lanes0 x).getLsbD 63 then 1 else 0) = 0
    rw [lanes0_getLsbD x 63 (by decide)]
    rfl
  have e0 : ∀ i < 21, f (3 * i) = if x.toNat / 2 ^ (3 * i) % 8 = 0 then 1 else 0 := by
    intro i hi; simp [f, lanes0_getLsbD x (3 * i) (by omega), show 3 * i ≤ 60 by omega]
  have e1 : ∀ i < 21, f (3 * i + 1) = 0 := by
    intro i hi; simp [f, lanes0_getLsbD x (3 * i + 1) (by omega), show ¬ (3 * i + 1) % 3 = 0 by omega]
  have e2 : ∀ i < 21, f (3 * i + 2) = 0 := by
    intro i hi; simp [f, lanes0_getLsbD x (3 * i + 2) (by omega), show ¬ (3 * i + 2) % 3 = 0 by omega]
  change (∑ j ∈ Finset.range (3 * 21 + 1), f j) = _
  rw [Finset.sum_range_succ, hz, Nat.add_zero, sum_range_three]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [e0 i (Finset.mem_range.mp hi), e1 i (Finset.mem_range.mp hi), e2 i (Finset.mem_range.mp hi),
    Nat.add_zero]

theorem count_zero_sum_getD (l : List Nat) :
    l.count 0 = ∑ i ∈ Finset.range l.length, if l.getD i 0 = 0 then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.count_cons]
      simpa [ih, Nat.add_comm]

theorem filter_zero_count (l : List Nat) : (l.filter (· = 0)).length = l.count 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : a = 0
      · subst a; simp [ih]
      · simp [ha, ih]

set_option maxHeartbeats 1000000 in
theorem pop_zero_digits (v : Digest) (c : Nat) :
    pop (Zero.lanes0 (v.extractLsb' 0 64)) + pop (Zero.lanes0 (v.extractLsb' 64 64)) +
      (if c = 0 then 1 else 0) = (lowDigits v ++ [c]).count 0 := by
  rw [pop_lanes0, pop_lanes0, count_zero_sum_getD]
  have hl : (lowDigits v ++ [c]).length = 21 + 21 + 1 := by simp [lowDigits_length]
  rw [hl]
  conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_add]
  have hc : (lowDigits v ++ [c]).getD (21 + 21) 0 = c := by rw [getD_lowDigits_append]; rfl
  rw [hc]
  apply congrArg (· + (if c = 0 then 1 else 0))
  apply congrArg₂ (fun a b : Nat => a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [getD_lowDigits_append, if_pos (show i < 42 by omega)]
    have hs : T3.lowerShift i = 3 * i := by simp [T3.lowerShift, hi']
    rw [hs]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
    rw [show (2 : Nat) ^ 64 = 2 ^ (3 * i) * 2 ^ (64 - 3 * i) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by
        change 2 ^ 3 ∣ 2 ^ (64 - 3 * i)
        apply Nat.pow_dvd_pow 2; omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [getD_lowDigits_append, if_pos (show 21 + i < 42 by omega)]
    have hs : T3.lowerShift (21 + i) = 64 + 3 * i := by simp [T3.lowerShift]
    rw [hs]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    have hh : v.toNat / 2 ^ 64 < 2 ^ 64 := by have := v.isLt; omega
    rw [Nat.mod_eq_of_lt hh, Nat.div_div_eq_div_mul, ← pow_add]

/-- The first scan establishes floor 4; the appended block checks layer 2's extra credit. -/
def scanFloor (_lay : Nat) : Nat := 4
def producerScanFloor (lay : Nat) : Nat := if lay = 3 then 4 else 5

theorem pop_le_64 (x : BitVec 64) : pop x ≤ 64 := by
  unfold pop
  calc
    _ ≤ ∑ _j ∈ Finset.range 64, (1 : Nat) := Finset.sum_le_sum (fun _ _ => by split <;> omega)
    _ = 64 := by simp

theorem zero_pop_loop {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (high : Bool) :
    ∀ n (s : MachineState) (x : BitVec 64) (a : Nat), pop x = n → a + n < 2 ^ 64 →
      s.pc = pcOf (zBase b + (if high then 27 else 22)) →
      s.getReg (if high then .x28 else .x29) = x → s.getReg .x21 = BitVec.ofNat 64 a →
      ∃ u, Steps image s (5 * n + 1) (5 * n + 1) u ∧
        u.pc = pcOf (zBase b + (if high then 32 else 27)) ∧
        u.getReg (if high then .x28 else .x29) = 0#64 ∧
        u.getReg .x21 = BitVec.ofNat 64 (a + n) ∧
        RegsExcept s u [.x21, (if high then .x28 else .x29), .x30] ∧ Frame s u (fun _ => False) := by
  have test : ∀ s : MachineState, s.pc = pcOf (zBase b + (if high then 27 else 22)) →
      ∃ t, Steps image s 1 1 t ∧
        t.pc = pcOf (zBase b + (if s.getReg (if high then .x28 else .x29) = 0#64 then
          (if high then 32 else 27) else (if high then 28 else 23))) ∧
        RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
    cases high <;> intro s hp
    · exact Zero.test_lo_spec hK s hp
    · exact Zero.test_hi_spec hK s hp
  have clear : ∀ s : MachineState, s.pc = pcOf (zBase b + (if high then 28 else 23)) →
      ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (zBase b + (if high then 27 else 22)) ∧
        t.getReg (if high then .x28 else .x29) = clr (s.getReg (if high then .x28 else .x29)) ∧
        t.getReg .x21 = s.getReg .x21 + 1#64 ∧
        RegsExcept s t [.x21, (if high then .x28 else .x29), .x30] ∧ Frame s t (fun _ => False) := by
    cases high <;> intro s hp
    · simpa [Zero.clear, clr] using Zero.clear_lo_spec hK s hp
    · simpa [Zero.clear, clr] using Zero.clear_hi_spec hK s hp
  intro n
  induction n with
  | zero =>
      intro s x a hn ha hp hx h21
      have hz : x = 0#64 := (pop_eq_zero_iff x).mp hn
      obtain ⟨t, st, pt, rt, ft⟩ := test s hp
      rw [hx, hz, if_pos rfl] at pt
      refine ⟨t, by simpa using st, pt, ?_, ?_, rt.mono (by simp), ft⟩
      · rw [rt.get (by simp), hx, hz]
      · simpa using (rt.get (by simp)).trans h21
  | succ n ih =>
      intro s x a hn ha hp hx h21
      have hz : x ≠ 0#64 := fun h => by rw [h, (pop_eq_zero_iff _).mpr rfl] at hn; omega
      obtain ⟨t, st, pt, rt, ft⟩ := test s hp
      rw [hx, if_neg hz] at pt
      obtain ⟨u, su, pu, gu, g21, ru, fu⟩ := clear t pt
      have hpop : pop (clr x) = n := by rw [pop_clr hz, hn]; omega
      have hx' : u.getReg (if high then .x28 else .x29) = clr x := by rw [gu, rt.get (by simp), hx]
      have ha' : u.getReg .x21 = BitVec.ofNat 64 (a + 1) := by
        rw [g21, rt.get (by simp), h21, show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]
      obtain ⟨v, sv, pv, gv, ga, rv, fv⟩ := ih u (clr x) (a + 1) hpop (by omega) pu hx' ha'
      refine ⟨v, ((st.trans su).trans sv).of_eq (by omega) (by omega), pv, gv, ?_,
        ((rt.trans ru).trans rv).mono (by simp), ((ft.trans fu).trans fv).mono (fun _ _ h => by simp at h)⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ga

section blocks
variable {image : Image} {b : Nat}

theorem lowZeros_bound (v : Digest) (hSum : 192 ≤ (lowDigits v).sum) :
    (lowDigits v).count 0 ≤ 14 := by
  have aux : ∀ ds : List Nat, (∀ x ∈ ds, x ≤ 7) →
      ds.sum + 7 * ds.count 0 ≤ 7 * ds.length := by
    intro ds
    induction ds with
    | nil => simp
    | cons x xs ih =>
      intro hx
      have hxs := ih (fun y hy => hx y (by simp [hy]))
      have hxb := hx x (by simp)
      by_cases hz : x = 0
      · subst x
        simp only [List.sum_cons, List.count_cons_self, List.length_cons] at *
        omega
      · simp only [List.sum_cons, List.count_cons_of_ne hz, List.length_cons] at *
        omega
  have hmax : ∀ x ∈ lowDigits v, x ≤ 7 := by
    intro x hx; simp only [lowDigits, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx; omega
  have h := aux (lowDigits v) hmax
  rw [lowDigits_length] at h
  omega

/-- Counts all 42 payload digits plus the checksum. The bound is conservative; it is not a
    verifier cost claim. This routine only executes after the existing sum and credit checks. -/
theorem zero_count_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 5))
    (v : Digest) (T S : Nat) (hT : T < 256) (hS : S ≤ T)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 T) (h25 : s.getReg .x25 = BitVec.ofNat 64 S) :
    ∃ k c u, Steps image s k c u ∧
      k ≤ 5 * (lowDigits v).count 0 + 28 ∧ c ≤ 5 * (lowDigits v).count 0 + 28 ∧
      u.pc = (if (lowDigits v ++ [T - S]).count 0 ≤ 5 then pcOf (zBase b+38) else pcOf (b+468)) ∧
      RegsExcept s u [.x20, .x21, .x28, .x29, .x30] ∧ Frame s u (fun _ => False) := by
  let xl := Zero.lanes0 (v.extractLsb' 0 64)
  let xh := Zero.lanes0 (v.extractLsb' 64 64)
  let nl := pop xl
  let nh := pop xh
  have bl : nl ≤ 64 := pop_le_64 xl
  have bh : nh ≤ 64 := pop_le_64 xh
  have hpayload : nl + nh = (lowDigits v).count 0 := by
    have h := pop_zero_digits v 1
    simpa [xl, xh, nl, nh, List.count_append] using h
  obtain ⟨t0, st0, p0, gl, gh, g0, r0, f0⟩ := Zero.setup_spec hK s hpc
  rw [h6] at gl
  rw [h7] at gh
  obtain ⟨t1, st1, p1, gx1, ga1, r1, f1⟩ := zero_pop_loop hK false nl t0 xl 0 rfl (by omega) p0 gl g0
  have hi1 : t1.getReg .x28 = xh := by rw [r1.get (by simp)]; exact gh
  obtain ⟨t2, st2, p2, gx2, ga2, r2, f2⟩ := zero_pop_loop hK true nh t1 xh nl rfl (by omega) p1 hi1 (by simpa using ga1)
  have r02 := (r0.trans r1).trans r2
  have ht : t2.getReg .x17 = BitVec.ofNat 64 T := (r02.get (by simp)).trans h17
  have hs : t2.getReg .x25 = BitVec.ofNat 64 S := (r02.get (by simp)).trans h25
  obtain ⟨t3, st3, p3, r3, f3⟩ := Zero.checksum_test_spec hK t2 p2
  have heq : t2.getReg .x17 = t2.getReg .x25 ↔ T = S := by
    rw [ht, hs]
    constructor
    · intro h
      have hh := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show T < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega)] at hh
      exact hh
    · intro h; rw [h]
  let q := if T = S then 1 else 0
  have hcnt : nl + nh + q = (lowDigits v ++ [T - S]).count 0 := by
    have hc : T - S = 0 ↔ T = S := by omega
    simpa only [xl, xh, nl, nh, q, hc] using pop_zero_digits v (T - S)
  obtain ⟨t4, k4, st4, bk4, p4, ga4, r4, f4⟩ :
      ∃ t4 k4, Steps image t3 k4 k4 t4 ∧ k4 ≤ 1 ∧ t4.pc = pcOf (zBase b + 34) ∧
        t4.getReg .x21 = BitVec.ofNat 64 (nl + nh + q) ∧
        RegsExcept t3 t4 [.x21] ∧ Frame t3 t4 (fun _ => False) := by
    by_cases h : T = S
    · rw [if_pos (heq.mpr h)] at p3
      obtain ⟨u, su, pu, gu, ru, fu⟩ := Zero.checksum_inc_spec hK t3 p3
      refine ⟨u, 1, su, by omega, pu, ?_, ru, fu⟩
      rw [gu, r3.get (by simp), ga2, show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]
      simp [q, h]
    · rw [if_neg (fun he => h (heq.mp he))] at p3
      refine ⟨t3, 0, Steps.refl t3, by omega, p3, ?_, RegsExcept.refl t3 [.x21], Frame.refl t3 (fun _ => False)⟩
      rw [r3.get (by simp), ga2]; simp [q, h]
  have bq : q ≤ 1 := by unfold q; split <;> omega
  obtain ⟨t5, st5, p5, r5, f5⟩ := Zero.limit_spec hK t4 p4 (nl + nh + q) (by omega) ga4
  obtain ⟨u, su, pu, ru, fu⟩ := Zero.exit_spec hK t5 (if nl + nh + q ≤ 5 then 36 else 37)
    (by split <;> simp) p5
  refine ⟨_, _, u, ((((((st0.trans st1).trans st2).trans st3).trans st4).trans st5).trans su),
    by omega, by omega, ?_, ?_, ?_⟩
  · rw [hcnt] at pu
    simpa using pu
  · exact ((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans ru).mono (by simp)
  · exact (((((((f0.trans f1).trans f2).trans f3).trans f4).trans f5).trans fu)).mono
      (fun _ _ h => by simp at h)

theorem capA0_thr (x : Word) (lay : Nat) (hl : lay < 4) (h8 : x = BitVec.ofNat 64 lay) :
    BinOp.eval .sll (BinOp.eval .srl (BinOp.eval .add x 3#64) 1#64) 20#64 = BitVec.ofNat 64 (capLimit lay) := by
  subst h8
  rcases (by omega : lay = 0 ∨ lay = 1 ∨ lay = 2 ∨ lay = 3) with h | h | h | h <;> subst h <;> rfl
def capThrE : E := .bin .sll (.bin .srl (.bin .add (.reg .x8) (.c 3#64)) (.c 1#64)) (.c 20#64)
theorem pcEa_0_eq (b : Nat) :
    pcEa_0 b = .ite .ltu (.reg .x19) capThrE (.c (pcOf (capBase b + 5))) (.c (pcOf (capBase b + 4))) := by
  unfold pcEa_0
  rw [show blkA354_0.res.pc = .ite .ltu (.reg .x19) capThrE (.c (pcOf (41066 + 5))) (.c (pcOf (41066 + 4))) by
    kernel_rfl]
  rfl
theorem capA0_frame (s : MachineState) (b : Nat) :
    Frame s (Result.toState ⟨sta_0, pcEa_0 b, blkA354_0.res.stop, blkA354_0.res.steps,
      blkA354_0.res.cycles⟩ s) (fun _ => False) := by
  intro A _ _; simp [sta_0, blkA354_0.res, rv_simp]
theorem capA0_pc (s : MachineState) (b lay i : Nat) (hl : lay < 4) (hi : i < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    (pcEa_0 b).eval s = (if i < capLimit lay then pcOf (capBase b + 5) else pcOf (capBase b + 4)) := by
  have hcl : capLimit lay < 2 ^ 64 := by unfold capLimit; omega
  rw [pcEa_0_eq]
  simp only [E.eval, capThrE]
  rw [capA0_thr (s.getReg .x8) lay hl h8, h19]
  by_cases h : i < capLimit lay
  · have : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 (capLimit lay)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hcl]; simpa using h
    simp [CmpOp.eval, this, h]
  · have : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 (capLimit lay)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hcl]; simp; omega
    simp [CmpOp.eval, this, h]
theorem capA0_regs (s : MachineState) (b : Nat) :
    RegsExcept s (Result.toState ⟨sta_0, pcEa_0 b, blkA354_0.res.stop, blkA354_0.res.steps,
      blkA354_0.res.cycles⟩ s) [.x6] := by
  intro r hr; simp at hr; cases r <;> simp_all [sta_0, blkA354_0.res, rv_simp] <;> rfl
theorem capA0_steps : blkA354_0.res.steps = 4 ∧ blkA354_0.res.cycles = 4 := by
  constructor <;> kernel_rfl
set_option maxHeartbeats 1000000 in
theorem capA0_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 0)) (lay i : Nat)
    (hl : lay < 4) (hi : i < 2 ^ 64) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 4 4 t ∧
      t.pc = (if i < capLimit lay then pcOf (capBase b + 5) else pcOf (capBase b + 4)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hS := symRun_sound (runa_0 hK.2.1) (codeAt_a_0 hK) s hpc (by simp [sta_0, blkA354_0.res, rv_simp])
  rw [capA0_steps.1, capA0_steps.2] at hS
  refine ⟨_, hS, ?_, capA0_regs s b, capA0_frame s b⟩
  rw [Result.toState_pc]
  exact capA0_pc s b lay i hl hi h8 h19
theorem capA4_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 4)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (capBase b + 6) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_4 hK.2.1) (codeAt_a_4 hK) s hpc (by simp [sta_4, blkA354_4.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcEa_4, blkA354_4.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_4, blkA354_4.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_4, blkA354_4.res, rv_simp]
theorem capA5_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 115) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_5 hK.2.1) (codeAt_a_5 hK) s hpc (by simp [sta_5, blkA354_5.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcEa_5, blkA354_5.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_5, blkA354_5.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_5, blkA354_5.res, rv_simp]
theorem capA6_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 6)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 424) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_6 hK.2.1) (codeAt_a_6 hK) s hpc (by simp [sta_6, blkA354_6.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcEa_6, blkA354_6.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_6, blkA354_6.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_6, blkA354_6.res, rv_simp]
theorem capLimit_lt (lay : Nat) (hl : lay < 4) : capLimit lay ≤ 3 * 2 ^ 20 := by
  unfold capLimit; interval_cases lay <;> decide
theorem cap_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b)) (lay i : Nat)
    (hl : lay < 4) (hi : i ≤ capLimit lay) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ k t, Steps image s k k t ∧ k ≤ 6 ∧
      t.pc = (if i = capLimit lay then pcOf (b + 424) else pcOf (b + 115)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hcl := capLimit_lt lay hl
  have hi64 : i < 2 ^ 64 := by omega
  obtain ⟨t0, s0, p0, r0, f0⟩ := capA0_spec hK s (by simpa using hpc) lay i hl hi64 h8 h19
  by_cases hlow : i < capLimit lay
  · rw [if_pos hlow] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := capA5_spec hK t0 p0
    have hne : i ≠ capLimit lay := by omega
    refine ⟨_, _, s0.trans s1, by omega, by rw [p1, if_neg hne], (r0.trans r1).mono (by decide),
      (f0.trans f1).mono (fun _ _ h => by simp at h)⟩
  · rw [if_neg hlow] at p0
    have heq : i = capLimit lay := by omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := capA4_spec hK t0 p0
    obtain ⟨t2, s2, p2, r2, f2⟩ := capA6_spec hK t1 p1
    refine ⟨_, _, s0.trans (s1.trans s2), by omega, by rw [p2, if_pos heq],
      (r0.trans (r1.trans r2)).mono (by decide), (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
theorem scanA7_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (c lo hi : BitVec 64)
    (h28 : s.getReg .x28 = c) (h6 : s.getReg .x6 = lo) (h7 : s.getReg .x7 = hi) :
    ∃ t, Steps image s 26 29 t ∧
      t.pc = pcOf (capBase b + 35) ∧
      t.getReg .x28 = clr (scanX c lo hi) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_7 hK.2.1) (codeAt_a_7 hK) s hpc (by simp [sta_7, blkA354_7.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [Result.toState_getReg, sta_7, blkA354_7.res]
    simp only [rv_simp, h6, h7, h28, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [sta_7, blkA354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_7, blkA354_7.res, rv_simp]
/-- The extra lowest-bit clear taken on layers 1 and 2 (credit floor 5). -/
theorem scanA33_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 33)) (x : BitVec 64)
    (h28 : s.getReg .x28 = x) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (capBase b + 35) ∧ t.getReg .x28 = clr x ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_33 hK.2.1) (codeAt_a_33 hK) s hpc (by simp [sta_33, blkA354_33.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcEa_33, blkA354_33.res, E.eval]
  · simp only [Result.toState_getReg, sta_33, blkA354_33.res]
    simp only [rv_simp, h28]
    have hm : ∀ y : BitVec 64, y + 18446744073709551615#64 = y - 1#64 := fun y => by
      rw [BitVec.sub_eq_add_neg]; rfl
    simp only [clr, hm]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_33, blkA354_33.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_33, blkA354_33.res, rv_simp]
theorem scanA35_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 35)) (x : BitVec 64)
    (h28 : s.getReg .x28 = x) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if clr (clr x) = 0#64 then pcOf (capBase b + 41) else pcOf (capBase b + 40)) ∧
      t.getReg .x28 = clr (clr x) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_35 hK.2.1) (codeAt_a_35 hK) s hpc (by simp [sta_35, blkA354_35.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_35, rebase, blkA354_35.res, E.eval, CmpOp.eval, BinOp.eval, h28]
    have hm : ∀ y : BitVec 64, y + 18446744073709551615#64 = y - 1#64 := fun y => by
      rw [BitVec.sub_eq_add_neg]; rfl
    have e : (x &&& x + 18446744073709551615#64 &&& (x &&& x + 18446744073709551615#64) + 18446744073709551615#64) =
        clr (clr x) := by simp only [clr, hm]
    rw [e]
    by_cases h : clr (clr x) = 0#64 <;> simp [h]
  · simp only [Result.toState_getReg, sta_35, blkA354_35.res]
    simp only [rv_simp, h28]
    have hm : ∀ y : BitVec 64, y + 18446744073709551615#64 = y - 1#64 := fun y => by
      rw [BitVec.sub_eq_add_neg]; rfl
    simp only [clr, hm]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_35, blkA354_35.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_35, blkA354_35.res, rv_simp]
theorem scanJump_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) {o : Nat} (ho : o = 40 ∨ o = 41)
    (hpc : s.pc = pcOf (capBase b + o)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if o = 41 then pcOf (b + 468) else pcOf (zBase b)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  rcases ho with rfl | rfl
  · refine ⟨_, symRun_sound (runa_40 hK.2.1) (codeAt_a_40 hK) s hpc (by simp [sta_40, blkA354_40.res, rv_simp]),
      ?_, ?_, ?_⟩
    · simp [pcEa_40, blkA354_40.res, E.eval]
    · intro r hr; simp at hr; cases r <;> simp_all [sta_40, blkA354_40.res, rv_simp] <;> rfl
    · intro A _ _; simp [sta_40, blkA354_40.res, rv_simp]
  · refine ⟨_, symRun_sound (runa_41 hK.2.1) (codeAt_a_41 hK) s hpc (by simp [sta_41, blkA354_41.res, rv_simp]),
      ?_, ?_, ?_⟩
    · simp [pcEa_41, blkA354_41.res, E.eval]
    · intro r hr; simp at hr; cases r <;> simp_all [sta_41, blkA354_41.res, rv_simp] <;> rfl
    · intro A _ _; simp [sta_41, blkA354_41.res, rv_simp]
theorem scan_base_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7))
    (lay : Nat) (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (v : Digest) (c : Nat)
    (hc : c < 8) (h28 : s.getReg .x28 = BitVec.ofNat 64 c) (h6 : s.getReg .x6 = v.extractLsb' 0 64)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 32 35 t ∧
      t.pc = (if 4 ≤ scanCredit v c then pcOf (zBase b) else pcOf (b + 468)) ∧
      t.getReg .x28 = (clr^[3]) (scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64)) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, x0, r0, f0⟩ := scanA7_spec hK s hpc lay hl h8 _ _ _ h28 h6 h7
  set X := scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64)
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ := scanA35_spec hK t0 p0 _ x0
  have hz : clr (clr (clr X)) = 0#64 ↔ ¬ 4 ≤ scanCredit v c := by
    have h := clr_iter_eq_zero_iff 3 X
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h
    rw [h, pop_scanX v c hc]; omega
  by_cases h0 : clr (clr (clr X)) = 0#64
  · rw [if_pos h0] at p1
    obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 41) (by omega) p1
    refine ⟨t2, (s0.trans (s1.trans s2)).of_eq (by omega) (by omega), ?_, ?_,
      (r0.trans (r1.trans r2)).mono (by decide), (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
    · rw [p2, if_pos rfl, if_neg (hz.mp h0)]
    · rw [r2.get (by decide), x1]; rfl
  · rw [if_neg h0] at p1
    obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 40) (by omega) p1
    refine ⟨t2, (s0.trans (s1.trans s2)).of_eq (by omega) (by omega), ?_, ?_,
      (r0.trans (r1.trans r2)).mono (by decide), (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
    · rw [p2, if_neg (by decide), if_pos (by by_contra hn; exact h0 (hz.mpr hn))]
    · rw [r2.get (by decide), x1]; rfl

/-- Shared base scan, layer-2-only fifth-credit check, then checksum-inclusive zero cap. -/
theorem scan_pre_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (v : Digest) (c : Nat)
    (hc : c < 8) (h28 : s.getReg .x28 = BitVec.ofNat 64 c) (h6 : s.getReg .x6 = v.extractLsb' 0 64)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) (T : Nat) (hT : T < 256)
    (hSum : (lowDigits v).sum ≤ T) (hcT : c = T - (lowDigits v).sum)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 T) (h25 : s.getReg .x25 = BitVec.ofNat 64 (lowDigits v).sum)
    (hZeros : (lowDigits v).count 0 ≤ 14) :
    ∃ k n t, Steps image s k n t ∧ n ≤ 70 + 5 * (lowDigits v).count 0 ∧
      t.pc = (if producerScanFloor lay ≤ scanCredit v c ∧ (lowDigits v ++ [c]).count 0 ≤ 5
        then pcOf (zBase b+38) else pcOf (b + 468)) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, st0, p0, gx0, r0, f0⟩ := scan_base_spec hK s hpc lay hl h8 v c hc h28 h6 h7
  by_cases hb : 4 ≤ scanCredit v c
  · rw [if_pos hb] at p0
    obtain ⟨t1, st1, p1, r1, f1⟩ := Zero.entry_spec hK t0 p0 lay hl (by rw [r0.get (by decide), h8])
    obtain ⟨t2, k2, st2, bk2, p2, r2, f2⟩ :
        ∃ t2 k2, Steps image t1 k2 k2 t2 ∧ k2 ≤ 3 ∧
          t2.pc = pcOf (zBase b + (if producerScanFloor lay ≤ scanCredit v c then 5 else 37)) ∧
          RegsExcept t1 t2 [.x28, .x29] ∧ Frame t1 t2 (fun _ => False) := by
      by_cases hl2 : lay ≠ 3
      · rw [if_pos hl2] at p1
        obtain ⟨u, su, pu, ru, fu⟩ := Zero.extra_credit_spec hK t1 p1
        have hzero : Zero.clear (t1.getReg .x28) = 0#64 ↔ ¬ 5 ≤ scanCredit v c := by
          rw [r1.get (by decide), gx0]
          change clr ((clr^[3]) (scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64))) = 0#64 ↔ _
          have h := clr_iter_eq_zero_iff 4 (scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64))
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h ⊢
          rw [h, pop_scanX v c hc]; omega
        refine ⟨u, 3, su, by omega, ?_, ru, fu⟩
        rw [pu]; simp only [producerScanFloor, if_neg hl2, hzero]
        by_cases h : 5 ≤ scanCredit v c <;> simp [h]
      · rw [if_neg hl2] at p1
        refine ⟨t1, 0, Steps.refl t1, by omega, ?_, RegsExcept.refl t1 [.x28, .x29], Frame.refl t1 (fun _ => False)⟩
        have hl3 : lay = 3 := not_ne_iff.mp hl2
        simpa only [producerScanFloor, if_pos hl3, if_pos hb] using p1
    have r02 := (r0.trans r1).trans r2
    have f02 := (f0.trans f1).trans f2
    by_cases hp : producerScanFloor lay ≤ scanCredit v c
    · rw [if_pos hp] at p2
      obtain ⟨k3, n3, u, st3, bk3, bn3, pu, ru, fu⟩ := zero_count_spec hK t2 p2 v T (lowDigits v).sum hT hSum
        ((r02.get (by simp)).trans h6) ((r02.get (by simp)).trans h7)
        ((r02.get (by simp)).trans h17) ((r02.get (by simp)).trans h25)
      refine ⟨_, _, u, ((st0.trans st1).trans st2).trans st3, by omega, ?_,
        (r02.trans ru).mono (by simp), (f02.trans fu).mono (fun _ _ h => by simp at h)⟩
      rw [← hcT] at pu
      by_cases hz : (lowDigits v ++ [c]).count 0 ≤ 5
      · simpa only [hp, true_and, if_pos hz] using pu
      · simpa only [hp, true_and, if_neg hz] using pu
    · rw [if_neg hp] at p2
      obtain ⟨u, su, pu, ru, fu⟩ := Zero.exit_spec hK t2 37 (by simp) p2
      refine ⟨_, _, u, ((st0.trans st1).trans st2).trans su, by omega, ?_,
        (r02.trans ru).mono (by simp), (f02.trans fu).mono (fun _ _ h => by simp at h)⟩
      simpa [hp] using pu
  · rw [if_neg hb] at p0
    have hp : ¬ producerScanFloor lay ≤ scanCredit v c := by
      unfold producerScanFloor; split <;> omega
    exact ⟨32, 35, t0, st0, by omega, by simpa [hp] using p0, r0, f0⟩
theorem scan_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (v : Digest) (c : Nat)
    (hc : c < 8) (h28 : s.getReg .x28 = BitVec.ofNat 64 c) (h6 : s.getReg .x6 = v.extractLsb' 0 64)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) (T : Nat) (hT : T < 256)
    (hSum : (lowDigits v).sum ≤ T) (hcT : c = T - (lowDigits v).sum)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 T) (h25 : s.getReg .x25 = BitVec.ofNat 64 (lowDigits v).sum)
    (hZeros : (lowDigits v).count 0 ≤ 14) :
    ∃ k n t, Steps image s k n t ∧ n ≤ 154 ∧
      t.pc = (if producerScanFloor lay ≤ scanCredit v c ∧ (lowDigits v ++ [c]).count 0 ≤ 5 ∧ Rank.rankOK v
        then pcOf (Reward.base b false) else pcOf (b + 468)) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨k,n,t,st,bn,pt,rt,ft⟩ := scan_pre_spec hK s hpc lay hl h8 v c hc h28 h6 h7 T hT hSum hcT h17 h25 hZeros
  by_cases h : producerScanFloor lay ≤ scanCredit v c ∧ (lowDigits v ++ [c]).count 0 ≤ 5
  · rw [if_pos h] at pt
    obtain ⟨u,su,pu,ru,fu⟩ := Rank.spec hK t pt v
      ((rt.get (by decide)).trans h6) ((rt.get (by decide)).trans h7)
    have hz : (lowDigits v).count 0 ≤ 5 := by
      have hh := h.2
      rw [List.count_append] at hh
      omega
    refine ⟨k+59,n+59,u,st.trans su,by omega,?_,(rt.trans ru).mono (by simp),
      (ft.trans fu).mono (fun _ _ h => by simp at h)⟩
    simp only [h.1,h.2,true_and]
    by_cases hr : Rank.rankOK v
    · rw [if_pos hr]
      simpa only [if_pos hr] using pu
    · rw [if_neg hr]
      simpa only [if_neg hr] using pu
  · rw [if_neg h] at pt
    refine ⟨k,n,t,st,by omega,?_,rt,ft⟩
    have h' : ¬ (producerScanFloor lay ≤ scanCredit v c ∧ (lowDigits v ++ [c]).count 0 ≤ 5 ∧ Rank.rankOK v) :=
      fun h' => h ⟨h'.1,h'.2.1⟩
    simpa only [if_neg h'] using pt

theorem zero_rank_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 5))
    (v : Digest) (T : Nat) (hT : T < 256) (hSum : (lowDigits v).sum ≤ T)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 T) (h25 : s.getReg .x25 = BitVec.ofNat 64 (lowDigits v).sum)
    (hZeros : (lowDigits v).count 0 ≤ 14) :
    ∃ k c t, Steps image s k c t ∧ c ≤ 112 ∧
      t.pc = (if (lowDigits v ++ [T-(lowDigits v).sum]).count 0 ≤ 5 ∧ Rank.rankOK v
        then pcOf (Reward.base b false) else pcOf (b+468)) ∧
      RegsExcept s t [.x20,.x21,.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨k,c,u,su,bk,bc,pu,ru,fu⟩ := zero_count_spec hK s hpc v T (lowDigits v).sum (by omega) hSum h6 h7 h17 h25
  by_cases hz : (lowDigits v ++ [T-(lowDigits v).sum]).count 0 ≤ 5
  · rw [if_pos hz] at pu
    obtain ⟨t,st,pt,rt,ft⟩ := Rank.spec hK u pu v
      ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7)
    have hzero := hz
    rw [List.count_append] at hzero
    refine ⟨k+59,c+59,t,su.trans st,by omega,?_,(ru.trans rt).mono (by simp),
      (fu.trans ft).mono (by simp)⟩
    by_cases hr : Rank.rankOK v
    · simpa only [hz,true_and,if_pos hr] using pt
    · simpa only [hz,true_and,if_neg hr] using pt
  · rw [if_neg hz] at pu
    refine ⟨k,c,u,su,by omega,?_,ru,fu⟩
    simpa only [hz,false_and,if_false] using pu

#print axioms zero_count_spec
#print axioms scan_spec
end blocks
end SigGolfCandidate.T3M.Search
end
end

section






section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT
def left : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def right : WCT9.LayerMsg → Digest
  | .forest _ => 0
  | .pair _ r => r
theorem counterWords (c : BitVec 32) :
    wordsOf (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) = [BitVec.ofNat 64 c.toNat, 0] := by
  have hc : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [show bytesLE 12 (0 : BitVec 96) = List.replicate 4 0 ++ List.replicate 8 0 by decide,
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc]
  rfl
theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    wordsOf (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)) =
      [(left msg).extractLsb' 0 64, (left msg).extractLsb' 64 64,
        rowLo lay tree leaf, BitVec.ofNat 64 1,
        BitVec.ofNat 64 c.toNat, 0, (right msg).extractLsb' 0 64, (right msg).extractLsb' 64 64] := by
  cases msg with
  | forest root => simpa [WCT9.layerEncodingInput, left, right] using Search.wordsOf_encodingInput lay tree leaf root c
  | pair l r =>
    change wordsOf (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)) = _
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    have he : WCT9.pairEncodingInputP lay tree leaf l r c 0 =
        (bytesLE 16 l ++ bytesLE 16 (T3.rowTweak lay tree leaf)) ++
          (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) ++ bytesLE 16 r := by
      simp only [WCT9.pairEncodingInputP, List.append_assoc]
    rw [he, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_bytesLE16, wordsOf_bytesLE16, rowTweak_lo, rowTweak_hi, counterWords, wordsOf_bytesLE16]
    rfl
theorem encodingInput_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)).length = 64 := by
  cases msg with
  | forest root => exact Search.encodingInput_length lay tree leaf root c
  | pair l r =>
    change (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)).length = 64
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    simp [WCT9.pairEncodingInputP, bytesLE_length]
theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (toQ (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl := encodingInput_length lay tree leaf msg c
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]
end SigGolfCandidate.T3M.Search.BC
end
section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
def csT (lay : Layer) : Nat := if lay = 0 then 270 else 380
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
def rewardOK (lay : Layer) (ds : List Nat) : Prop :=
  WCT9.producerFloor lay + WCT9.dispatchPenalty lay ds ≤ WCT9.wordCredit lay ds + 4 * WCT9.savedCopies lay ds
instance (lay : Layer) (ds : List Nat) : Decidable (rewardOK lay ds) := by unfold rewardOK; infer_instance
theorem producerDecode_top (v : Digest) {ds : List Nat} (hd : T3.decode 0 v = some ds) :
    WCT9.producerDecode 0 v = if rewardOK 0 ds then some ds else none := by
  simp [WCT9.producerDecode,hd,WCT9.producerZeroBound,WCT9.producerRankBound,rewardOK]
theorem producerDecode_lower {lay : Layer} (hlz : lay ≠ 0) (v : Digest) (c : Nat) {ds : List Nat}
    (hdec : T3.decode lay v = some ds) (hds : ds = lowDigits v ++ [c]) :
    WCT9.producerDecode lay v =
      if rewardOK lay ds ∧ (lowDigits v ++ [c]).count 0 ≤ 5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.producerDecode,hdec,WCT9.producerZeroBound,WCT9.producerRankBound,rewardOK,
    Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]
def cfFlag (b : Nat) : Nat := if b = 543 then 1 else 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ DigW A
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target A.lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 32
  x15 : A.tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay)
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if A.lay = 0 ∧ b = 543 then DummyOut A s0 t else
      t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, T3.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target A.lay
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
-- r3-lean-sign: the legacy (bit-127 selector) BC counter-search loop was removed; the kernel now implements the
-- restricted top choice (see `Canonical.cs_loop`).
structure FailedAt (b : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 2)
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure CsPreS (b : Nat) (s : MachineState) (lay : Layer) (tree leaf : Nat) (message : WCT9.LayerMsg) (ret : Nat) :
    Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  hroute : tree * 2 ^ T3.height lay + leaf < 2 ^ 32
  x15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)
  msg : DigAt s ENC (left message)
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right message).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right message).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
def DummyOutS (s : MachineState) (ret : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
    (t.getReg .x25).toNat ≤ 129
def CsPostS (b : Nat) (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 ∧ b = 543 then DummyOutS s ret t else FailedAt b t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
def csCostS (lay : Layer) : Nat := (if lay = 0 then T3.counterLimit * 270 else WCT9.lowerSearchLimit * 380) + 8192
theorem CsPreS.toCsPre {b : Nat} {s : MachineState} {lay : Layer} {tree leaf : Nat} {msg : WCT9.LayerMsg} {ret : Nat}
    (h : CsPreS b s lay tree leaf msg ret) : CsPre b ⟨lay, tree, leaf, msg, ret⟩ s :=
  ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.hroute, h.x15, h.msg.1, h.msg.2,
    ⟨_, h.c32, (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm⟩, h.z40, h.r48, h.r56, h.table, h.cf, h.reward⟩
end SigGolfCandidate.T3M.Search.BC
end
end

namespace SigGolfCandidate.T3M.Search.CanonicalHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def lowerFloorCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x10e3e03,0x8f1fe06f]
def lowerCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x14e3c23,0xfb9ea06f]
def topCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xff4a0e93,0x1de3c23,0xf79ea06f]
sym_block lowerFloorRun := symRun {noAlias := true} lowerFloorCode (pcOf 22491) 6
sym_block lowerCreditRun := symRun {noAlias := true} lowerCreditCode (pcOf 22495) 6
sym_block topCreditRun := symRun {noAlias := true} topCreditCode (pcOf 22499) 7

theorem lowerFloor_steps {image : Image} (hc : CodeAt image (pcOf 22491) lowerFloorCode)
    (s : MachineState) (hp : s.pc=pcOf 22491) (floor : BitVec 64)
    (hf : s.getMem (0x66010#64)=floor) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 21018 ∧ t.getReg .x28=floor ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerFloorRun hc s hp (by simp [lowerFloorRun.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [lowerFloorRun.res,rv_simp]
  · simp [lowerFloorRun.res,rv_simp,hf]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [lowerFloorRun.res,rv_simp]

theorem lowerCredit_steps {image : Image} (hc : CodeAt image (pcOf 22495) lowerCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 22495) (credit : BitVec 64) (hx : s.getReg .x20=credit) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 976 ∧ t.getMem (0x66018#64)=credit ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=0x66018) := by
  refine ⟨_,symRun_sound lowerCreditRun hc s hp (by simp [lowerCreditRun.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [lowerCreditRun.res,rv_simp]
  · simp [lowerCreditRun.res,rv_simp,hx]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,lowerCreditRun.res]; t3n []
    rw [if_neg (by omega)]

theorem topCredit_steps {image : Image} (hc : CodeAt image (pcOf 22499) topCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 22499) (acc : Nat) (ha : 12≤acc) (hb : acc<2^64)
    (hx : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 965 ∧ t.getMem (0x66018#64)=BitVec.ofNat 64 (acc-12) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66018) := by
  refine ⟨_,symRun_sound topCreditRun hc s hp (by simp [topCreditRun.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [topCreditRun.res,rv_simp]
  · simp only [Result.toState_getMem,topCreditRun.res];t3n [hx]
    omega
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,topCreditRun.res]; t3n []
    rw [if_neg (by omega)]
#print axioms lowerFloor_steps
#print axioms lowerCredit_steps
#print axioms topCredit_steps
end SigGolfCandidate.T3M.Search.CanonicalHooks

namespace SigGolfCandidate.T3M.Search.CanonicalHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

def lowerAddCode : List (BitVec 32) := bv_list% 32 [0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33]
def lowerJumpCode : List (BitVec 32) := bv_list% 32 [0x7100106f]
/-- `21015: jal zero, pa` (path-aware lower credit, choice block). -/
def floorJumpCode : List (BitVec 32) := bv_list% 32 [0x0880006f]
def lowerBranchCode : List (BitVec 32) := bv_list% 32 [0x1ca6463]
def lowerBadCode : List (BitVec 32) := bv_list% 32 [0xf5cec06f]
/-- `21438: jal zero, topcr` (path-aware top credit). -/
def topBranchCode : List (BitVec 32) := bv_list% 32 [0xbf5ff06f]
/-- `topcr` (21179): `s4 += 2` on the LOW path (choice flag clear; d6b head), then the floor test `s4 < 31`
(floor 19 + 12) fails into `choice_r`, else `jal` to the zero-cap routine `zc` (21667; top-bytes layer), which
continues to the top credit hook (22499) or fails into `choice_r`. -/
def topCr0 : List (BitVec 32) := bv_list% 32 [0x00066e37,0x7f8e3e03,0x000e1463]
def topCr3 : List (BitVec 32) := bv_list% 32 [0x002a0a13]
def topCr4 : List (BitVec 32) := bv_list% 32 [0x02200e13,0xdbca66e3]
def topCr6 : List (BitVec 32) := bv_list% 32 [0x7880006f]
sym_block lowerAddRun := symRun {noAlias:=true} lowerAddCode (pcOf 21011) 6
sym_block lowerFloorJumpRun := symRun {noAlias:=true} floorJumpCode (pcOf 21015) 2
sym_block lowerCreditJumpRun := symRun {noAlias:=true} lowerJumpCode (pcOf 21019) 2
sym_block lowerBranchRun := symRun {noAlias:=true} lowerBranchCode (pcOf 21018) 2
sym_block lowerBadRun := symRun {noAlias:=true} lowerBadCode (pcOf 21020) 2
sym_block topBranchRun := symRun {noAlias:=true} topBranchCode (pcOf 21438) 2
sym_block topCr0Run := symRun {noAlias:=true} topCr0 (pcOf 21179) 4
sym_block topCr3Run := symRun {noAlias:=true} topCr3 (pcOf 21182) 2
sym_block topCr4Run := symRun {noAlias:=true} topCr4 (pcOf 21183) 3
sym_block topCr6Run := symRun {noAlias:=true} topCr6 (pcOf 21185) 2

structure Code (image : Image) : Prop where
  scoring : CanonicalReward.PrefixAt image 543
  floorJump : CodeAt image (pcOf 21015) floorJumpCode
  lowerBranch : CodeAt image (pcOf 21018) lowerBranchCode
  lowerJump : CodeAt image (pcOf 21019) lowerJumpCode
  lowerBad : CodeAt image (pcOf 21020) lowerBadCode
  topBranch : CodeAt image (pcOf 21438) topBranchCode
  cr0 : CodeAt image (pcOf 21179) topCr0
  cr3 : CodeAt image (pcOf 21182) topCr3
  cr4 : CodeAt image (pcOf 21183) topCr4
  cr6 : CodeAt image (pcOf 21185) topCr6
  zc : CodeAt image (pcOf 21667) (ZeroCap.code 543)
  floorHook : CodeAt image (pcOf 22491) lowerFloorCode
  lowerHook : CodeAt image (pcOf 22495) lowerCreditCode
  topHook : CodeAt image (pcOf 22499) topCreditCode

theorem lowerAdd_steps {image : Image} (hc : CodeAt image (pcOf 21011) lowerAddCode)
    (s : MachineState) (hp : s.pc=pcOf 21011) (a T S : Nat) (hs : S≤T)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hc8 : T-S<8) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 21015 ∧
      t.getReg .x20=BitVec.ofNat 64 (a+if T-S=6 then 1 else 0) ∧
      RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _=>False) := by
  have hsub : s.getReg .x17-s.getReg .x25=BitVec.ofNat 64 (T-S) := by
    rw [h17,h25]
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hs,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hflag := Reward.eq_small (T-S) 6 hc8 (by decide) (by decide)
  change (if (BitVec.ofNat 64 (T-S)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=
    BitVec.ofNat 64 (if T-S=6 then 1 else 0) at hflag
  refine ⟨_,symRun_sound lowerAddRun hc s hp (by simp [lowerAddRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · change s.getReg .x20+(if ((s.getReg .x17-s.getReg .x25)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=_
    rw [hsub,hflag,h20,BitVec.ofNat_add]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem lowerFloorJump_steps {image : Image} (hc : CodeAt image (pcOf 21015) floorJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 21015) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (choiceBase 543+17) ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerFloorJumpRun hc s hp (by simp [lowerFloorJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerCreditJump_steps {image : Image} (hc : CodeAt image (pcOf 21019) lowerJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 21019) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 22495 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerCreditJumpRun hc s hp (by simp [lowerCreditJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBranch_steps {image : Image} (hc : CodeAt image (pcOf 21018) lowerBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 21018) (a floor : Nat) (ha : a<2^64) (hf : floor<2^64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h28 : s.getReg .x28=BitVec.ofNat 64 floor) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=(if floor≤a then pcOf 21019 else pcOf 21020) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBranchRun hc s hp (by simp [lowerBranchRun.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult (s.getReg .x28) then _ else _)=_
    rw [h20,h28,ofNat_ult a floor ha hf]
    split_ifs <;> simp_all [E.eval] <;> omega
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBad_steps {image : Image} (hc : CodeAt image (pcOf 21020) lowerBadCode)
    (s : MachineState) (hp : s.pc=pcOf 21020) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 1011 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBadRun hc s hp (by simp [lowerBadRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topBranch_steps {image : Image} (hc : CodeAt image (pcOf 21438) topBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 21438) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 21179 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topBranchRun hc s hp (by simp [topBranchRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topCr0_steps {image : Image} (hc : CodeAt image (pcOf 21179) topCr0)
    (s : MachineState) (hp : s.pc=pcOf 21179) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc=(if s.getMem (BitVec.ofNat 64 FLAG)=0 then pcOf 21182 else pcOf 21183) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr0Run hc s hp (by simp [topCr0Run.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_⟩
  · simp only [Result.toState_pc,topCr0Run.res,E.eval,CmpOp.eval,BinOp.eval]
    t3n []
    by_cases h : s.getMem (BitVec.ofNat 64 FLAG)=0
    · simp [FLAG] at h; simp [h]
    · simp [FLAG] at h; simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [topCr0Run.res,rv_simp] <;> rfl
  · intro A _ _; simp [topCr0Run.res,rv_simp]

theorem topCr3_steps {image : Image} (hc : CodeAt image (pcOf 21182) topCr3)
    (s : MachineState) (hp : s.pc=pcOf 21182) (a : Nat) (h20 : s.getReg .x20=BitVec.ofNat 64 a) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 21183 ∧ t.getReg .x20=BitVec.ofNat 64 (a+2) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr3Run hc s hp (by simp [topCr3Run.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [topCr3Run.res,rv_simp,h20,BitVec.ofNat_add]
  · intro r hr; simp at hr; cases r <;> simp_all [topCr3Run.res,rv_simp] <;> rfl
  · intro A _ _; simp [topCr3Run.res,rv_simp]

theorem topCr4_steps {image : Image} (hc : CodeAt image (pcOf 21183) topCr4)
    (s : MachineState) (hp : s.pc=pcOf 21183) (a : Nat) (ha : a<2^64) (h20 : s.getReg .x20=BitVec.ofNat 64 a) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if 34≤a then pcOf 21185 else pcOf (choiceBase 543+3)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr4Run hc s hp (by simp [topCr4Run.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult 34#64 then _ else _)=_
    rw [h20,ofNat_ult a 34 ha (by decide)]
    split_ifs <;> simp_all [E.eval,choiceBase] <;> omega
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem topCr6_steps {image : Image} (hc : CodeAt image (pcOf 21185) topCr6)
    (s : MachineState) (hp : s.pc=pcOf 21185) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 21667 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr6Run hc s hp (by simp [topCr6Run.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl
end SigGolfCandidate.T3M.Search.CanonicalHooks

namespace SigGolfCandidate.T3M.Search.CanonicalHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open LowerLUT
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

def CreditW (A : Nat) : Prop := A=0x66018

/-- Lower reward with the path-aware bonus (`pa`): `low` = the LOW half at `EOUT` is spare. -/
theorem lower_spec {image : Image} (hK : KernAt image 543 (Code image)) (s : MachineState) (v : Digest)
    (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 543 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hf : floor<22) (hm : s.getMem (0x66010#64)=BitVec.ofNat 64 floor) :
    ∃ k t, Steps image s k k t ∧ k≤95 ∧
      t.pc=(if floor≤partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
        then pcOf 976 else pcOf 1011) ∧
      (floor≤partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0) →
        t.getMem (0x66018#64)=BitVec.ofNat 64 (partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t CreditW := by
  have hC := hK.reward
  have ha0 : partialScore v 14+(if T-S=6 then 1 else 0)<2^60 := by have h := partial_bound v 14; split_ifs <;> omega
  have ha : partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)<2^64 := by
    split_ifs <;> omega
  obtain ⟨u,su,pu,ux11,ux20,ru,fu⟩ := CanonicalReward.Lower.init_spec (Or.inr rfl) hC.scoring s hp
  obtain ⟨v1,sv,pv,vx,rv,fv⟩ := CanonicalReward.Lower.loop_spec (Or.inr rfl) hC.scoring u v
    (ht.frame fu (by simp)) pu ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7) ux11 ux20 14 (by omega)
  have had : CodeAt image (pcOf 21011) lowerAddCode := by
    have h := CanonicalReward.lower_slice hC.scoring 73 4 (by decide)
    convert h using 1 <;> rfl
  obtain ⟨v2,s2,p2,x2,r2,f2⟩ := lowerAdd_steps had v1 (by simpa [Reward.base] using pv) (partialScore v 14) T S hST vx
    (((ru.trans rv).get (by decide)).trans h17) (((ru.trans rv).get (by decide)).trans h25) hc
  obtain ⟨v3,s3,p3,r3,f3⟩ := lowerFloorJump_steps hC.floorJump v2 p2
  have f03 := ((fu.trans fv).trans f2).trans f3
  obtain ⟨kp,vp,sp,kple,pp,xp,rp,fp⟩ := pa_spec hK v3 p3 L (partialScore v 14+(if T-S=6 then 1 else 0)) (by omega)
    (by rw [f03.get (by decide) (by simp)]; exact hm0) (by rw [f03.get (by decide) (by simp)]; exact hm8)
    (by rw [r3.get (by decide),x2])
  obtain ⟨v4,s4,p4,x4,r4,f4⟩ := lowerFloor_steps hC.floorHook vp (by simpa [paTarget] using pp)
    (BitVec.ofNat 64 floor) (by rw [fp.get (by decide) (by simp),f03.get (by decide) (by simp),hm])
  have x20 : v4.getReg .x20=BitVec.ofNat 64 (partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)) := by
    rw [r4.get (by decide),xp]
  obtain ⟨v5,s5,p5,r5,f5⟩ := lowerBranch_steps hC.lowerBranch v4 p4 _ floor ha (by omega) x20 x4
  have rr := ((((ru.trans rv).trans r2).trans r3).trans rp).trans r4
  have ff := (f03.trans fp).trans f4
  by_cases hg : floor≤partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
  · rw [if_pos hg] at p5
    obtain ⟨v6,s6,p6,r6,f6⟩ := lowerCreditJump_steps hC.lowerJump v5 p5
    obtain ⟨t,st,pt,mt,rt,ft⟩ := lowerCredit_steps hC.lowerHook v6 p6 _
      (by rw [r6.get (by decide),r5.get (by decide),x20])
    refine ⟨_,t,(((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans s6).trans st,
      by omega,by rw [if_pos hg]; exact pt,fun _=>mt,?_,?_⟩
    · exact ((rr.trans r5).trans r6).trans rt |>.mono (by decide)
    · exact ((ff.trans f5).trans f6).trans ft |>.mono (by simp [CreditW])
  · rw [if_neg hg] at p5
    obtain ⟨t,st,pt,rt,ft⟩ := lowerBad_steps hC.lowerBad v5 p5
    refine ⟨_,t,((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans st,
      by omega,?_,fun h=>False.elim (hg h),?_,?_⟩
    · rw [if_neg hg]; exact pt
    · exact (rr.trans r5).trans rt |>.mono (by decide)
    · exact (ff.trans f5).trans ft |>.mono (by simp [CreditW])

/-- Top reward with the path-aware LOW bonus 2 (`topcr`); the choice flag is clear exactly on the LOW trial.
A half passing the floor (`31 = 19 + 12`) is then checked by the zero cap `zc` (at most 9 zero digits). -/
theorem top_spec {image : Image} (hC : Code image) (s : MachineState) (v : Digest)
    (ht : Reward.RewardTablesOK s) (hz : ZeroCap.ZtOK 543 s) (hv : T3.topRanksValid (T3.topFlip v)=true)
    (hp : s.pc=pcOf (Reward.base 543 true))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (low : Bool) (hfl : s.getMem (BitVec.ofNat 64 FLAG)=0 ↔ low=true) :
    let good := 34 ≤ Reward.packedTopScore v+(if low then 2 else 0) ∧ ZeroCap.zcount v ≤ 9
    ∃ k t, Steps image s k k t ∧ k≤226 ∧
      t.pc=(if good then pcOf 965 else pcOf (choiceBase 543+3)) ∧
      (good → t.getMem (0x66018#64)=BitVec.ofNat 64 (Reward.packedTopScore v+(if low then 2 else 0)-12)) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29] ∧ Frame s t CreditW := by
  intro good
  obtain ⟨t1,s1,p1,g11,g20,r1,f1⟩ := CanonicalReward.Top.init_spec (Or.inr rfl) hC.scoring s hp
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := CanonicalReward.Top.iter (Or.inr rfl) hC.scoring t1 v 18 (by decide)
    (ht.frame f1 (by simp)) p1 ((r1.get (by decide)).trans h6) ((r1.get (by decide)).trans h7) g11 g20
  rw [Reward.PackedTop.runningSum_eq] at g2
  have he := Reward.packedTopScore_reward v hv
  have hb := Reward.total_reward_bound 0 (topDigits (T3.topFlip v))
  obtain ⟨t3,s3,p3,r3,f3⟩ := topBranch_steps hC.topBranch t2 (by simpa [Reward.base,Reward.PackedTop.start] using p2)
  obtain ⟨t4,s4,p4,r4,f4⟩ := topCr0_steps hC.cr0 t3 p3
  have hflag : t3.getMem (BitVec.ofNat 64 FLAG)=s.getMem (BitVec.ofNat 64 FLAG) := by
    rw [f3.get (by decide) (by simp),f2.get (by decide) (by simp),f1.get (by decide) (by simp)]
  rw [hflag] at p4
  have x20 : t4.getReg .x20=BitVec.ofNat 64 (Reward.packedTopScore v) := by
    rw [r4.get (by decide),r3.get (by decide),g2]
  obtain ⟨t5,k5,s5,k5le,p5,x5,r5,f5⟩ : ∃ t5 k5, Steps image t4 k5 k5 t5 ∧ k5≤1 ∧ t5.pc=pcOf 21183 ∧
      t5.getReg .x20=BitVec.ofNat 64 (Reward.packedTopScore v+(if low then 2 else 0)) ∧
      RegsExcept t4 t5 [.x20] ∧ Frame t4 t5 (fun _=>False) := by
    cases low
    · have hne : ¬ s.getMem (BitVec.ofNat 64 FLAG)=0 := fun h => by simpa using hfl.mp h
      rw [if_neg hne] at p4
      exact ⟨t4,0,Steps.refl _,by omega,p4,by simpa using x20,RegsExcept.refl _ _,fun _ _ _=>rfl⟩
    · rw [if_pos (hfl.mpr rfl)] at p4
      obtain ⟨t5,s5,p5,x5,r5,f5⟩ := topCr3_steps hC.cr3 t4 p4 _ x20
      exact ⟨t5,1,s5,le_refl _,p5,by simpa using x5,r5,f5⟩
  have ha3 : Reward.packedTopScore v+(if low then 2 else 0)<2^64 := by split <;> omega
  obtain ⟨t6,s6,p6,r6,f6⟩ := topCr4_steps hC.cr4 t5 p5 (Reward.packedTopScore v+(if low then 2 else 0)) ha3 x5
  have rr := (((r1.trans r2).trans r3).trans r4).trans r5
  have ff := (((f1.trans f2).trans f3).trans f4).trans f5
  have hs12 : (3 : Nat)+(Reward.PackedTop.start 18-3)=95 := by decide
  by_cases hg : 34≤Reward.packedTopScore v+(if low then 2 else 0)
  · rw [if_pos hg] at p6
    obtain ⟨t7,s7,p7,r7,f7⟩ := topCr6_steps hC.cr6 t6 p6
    have rr7 := (rr.trans r6).trans r7
    have ff7 := (ff.trans f6).trans f7
    obtain ⟨kz,tz,sz,kzle,pz,rz,fz⟩ := ZeroCap.zc_spec (b := 543) (Or.inr rfl) hC.zc t7 v
      (hz.frame ff7 (by simp)) (by simpa [ZeroCap.zcBase] using p7)
      (by rw [rr7.get (by decide)]; exact h6) (by rw [rr7.get (by decide)]; exact h7)
    by_cases hzc : ZeroCap.zcount v ≤ 9
    · rw [if_pos hzc] at pz
      have hgood : good := ⟨hg, hzc⟩
      obtain ⟨t,st,pt,mt,rt,ft⟩ := topCredit_steps hC.topHook tz (by simpa [ZeroCap.zcPass] using pz)
        (Reward.packedTopScore v+(if low then 2 else 0)) (by omega) ha3
        (by rw [rz.get (by decide),r7.get (by decide),r6.get (by decide),x5])
      refine ⟨_,t,(((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans sz).trans st,?_,
        by rw [if_pos hgood]; exact pt,fun _=>mt,?_,?_⟩
      · omega
      · exact ((rr7.trans rz).trans rt) |>.mono (by decide)
      · exact ((ff7.trans fz).trans ft) |>.mono (by simp [CreditW])
    · rw [if_neg hzc] at pz
      have hgood : ¬ good := fun h => hzc h.2
      refine ⟨_,tz,((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans sz,?_,
        by rw [if_neg hgood]; simpa [ZeroCap.zcFail,choiceBase] using pz,fun h=>False.elim (hgood h),?_,?_⟩
      · omega
      · exact (rr7.trans rz) |>.mono (by decide)
      · exact (ff7.trans fz) |>.mono (by simp [CreditW])
  · rw [if_neg hg] at p6
    have hgood : ¬ good := fun h => hg h.1
    refine ⟨_,t6,(((((s1.trans s2).trans s3).trans s4).trans s5).trans s6),?_,
      by rw [if_neg hgood]; exact p6,fun h=>False.elim (hgood h),?_,?_⟩
    · omega
    · exact (rr.trans r6) |>.mono (by decide)
    · exact (ff.trans f6) |>.mono (by simp [CreditW])
#print axioms lower_spec
#print axioms top_spec
end SigGolfCandidate.T3M.Search.CanonicalHooks

namespace SigGolfCandidate.T3M.Search.CanonicalHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

theorem lower_reward (lay : Layer) (hl : lay≠0) (v : Digest) (T S : Nat) (low : Bool) :
    LowerLUT.partialScore v 14+(if T-S=6 then 1 else 0)+(if low then 4 else 0)=
      credit lay low (lowDigits v++[T-S]) := by
  have h := LowerLUT.packed_reward lay hl v (T-S)
  rw [credit_lower hl]
  simp only [LowerLUT.partialScore,reward] at h ⊢
  omega

theorem lower_spec_credit {image : Image} (hK : KernAt image 543 (Code image)) (s : MachineState) (lay : Layer)
    (hl : lay≠0) (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 543 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hf : floor<22) (hm : s.getMem (0x66010#64)=BitVec.ofNat 64 floor) :
    let low := decide (T3.lowerSpare L)
    let good := floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤pathReward lay low (lowDigits v++[T-S])
    ∃ k t, Steps image s k k t ∧ k≤95 ∧
      t.pc=(if good then pcOf 976 else pcOf 1011) ∧
      (good → t.getMem (0x66018#64)=BitVec.ofNat 64 (credit lay low (lowDigits v++[T-S]))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t CreditW := by
  dsimp only
  have h := lower_spec hK s v ht hp h6 h7 L hm0 hm8 T S floor h17 h25 hST hc hf hm
  have e := lower_reward lay hl v T S (decide (T3.lowerSpare L))
  have e' : (if T3.lowerSpare L then 4 else 0)=(if decide (T3.lowerSpare L) then 4 else 0) := by
    by_cases hs : T3.lowerSpare L <;> simp [hs]
  have hg : (floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤
      pathReward lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]))↔
      floor≤credit lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]) := by
    simp [credit,WCT9.dispatchPenalty,hl]
  rw [e',e] at h
  simpa only [hg] using h

theorem top_reward (v : Digest) (hv : T3.topRanksValid (T3.topFlip v)=true) (low : Bool) :
    Reward.packedTopScore v+(if low then 2 else 0)-12=credit 0 low (topDigits (T3.topFlip v)) := by
  have h := Reward.packedTopScore_reward v hv
  rw [credit_top]
  unfold reward
  split <;> omega

theorem top_spec_credit {image : Image} (hC : Code image) (s : MachineState) (v : Digest)
    (ht : Reward.RewardTablesOK s) (hz : ZeroCap.ZtOK 543 s) (hv : T3.topRanksValid (T3.topFlip v)=true)
    (hp : s.pc=pcOf (Reward.base 543 true))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (low : Bool) (hfl : s.getMem (BitVec.ofNat 64 FLAG)=0 ↔ low=true) :
    let good := 22+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤pathReward 0 low (topDigits (T3.topFlip v)) ∧
      WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip v))
    ∃ k t, Steps image s k k t ∧ k≤226 ∧
      t.pc=(if good then pcOf 965 else pcOf (choiceBase 543+3)) ∧
      (good → t.getMem (0x66018#64)=BitVec.ofNat 64 (credit 0 low (topDigits (T3.topFlip v)))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29] ∧ Frame s t CreditW := by
  have he := Reward.packedTopScore_reward v hv
  have hi : (34≤Reward.packedTopScore v+(if low then 2 else 0) ∧ ZeroCap.zcount v ≤ 9)↔
      (22+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤pathReward 0 low (topDigits (T3.topFlip v)) ∧
        WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip v))) := by
    have h1 : (34≤Reward.packedTopScore v+(if low then 2 else 0)) ↔
        22+WCT9.dispatchPenalty 0 (topDigits (T3.topFlip v))≤pathReward 0 low (topDigits (T3.topFlip v)) := by
      rw [pathReward_top]
      unfold reward
      split <;> omega
    have h2 : ZeroCap.zcount v ≤ 9 ↔ WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip v)) := by
      rw [WCT9.canonicalZeroBound, ← ZeroCap.zcount_eq v hv]
      simp [WCT9.producerZeroCap]
    exact and_congr h1 h2
  have h := top_spec hC s v ht hz hv hp h6 h7 low hfl
  simpa only [hi,top_reward v hv low] using h
#print axioms lower_spec_credit
#print axioms top_spec_credit
end SigGolfCandidate.T3M.Search.CanonicalHooks

namespace SigGolfCandidate.T3M.Search.Canonical
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
  floor : Nat
def csT (lay : Layer) : Nat := if lay = 0 then 755 else 391
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
/-- Path-aware producer reward test (`low` = the LOW half was selected). -/
def rewardOK (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Prop :=
  floor + WCT9.dispatchPenalty lay ds ≤ WCT9.CanonicalPolicy.pathReward lay low ds
instance (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Decidable (rewardOK lay floor low ds) := by
  unfold rewardOK; infer_instance
theorem reward_credit_le {lay : Layer} {floor : Nat} {low : Bool} {ds : List Nat}
    (h : rewardOK lay floor low ds) : floor ≤ WCT9.CanonicalPolicy.credit lay low ds := by
  unfold rewardOK WCT9.CanonicalPolicy.credit at *
  omega
theorem producerDecode_top (v : Digest) (floor : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 floor low v =
      if rewardOK 0 floor low ds ∧ WCT9.canonicalZeroBound 0 ds then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerRankBound,rewardOK]
  try exact if_congr Iff.rfl rfl rfl
theorem producerDecode_lower {lay : Layer} (hlz : lay≠0) (v : Digest) (floor c : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode lay v=some ds) (hds : ds=lowDigits v++[c]) :
    WCT9.CanonicalPolicy.producerDecodeAt lay floor low v=
      if rewardOK lay floor low ds ∧ (lowDigits v++[c]).count 0≤5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.canonicalZeroBound,WCT9.producerZeroCap,WCT9.producerRankBound,
    rewardOK,Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]
/-! Producer output on a full 256-bit answer, split by the machine's trial order. -/
theorem producerDecodeOut_top_low (a : BitVec 256) {ds : List Nat}
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 22 true (a.extractLsb' 0 128) = some ds) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 22 a = some (ds, true) := by
  have hg : WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 22 from rfl, h]; rfl
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_blocked (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 22 true (a.extractLsb' 0 128) = none)
    (hb : T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 22 a = none := by
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_high (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 22 true (a.extractLsb' 0 128) = none)
    (hb : ¬ T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 22 a =
      (WCT9.CanonicalPolicy.producerDecodeAt 0 22 false (a.extractLsb' 128 128)).map (·, false) := by
  have hg : ¬ WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 22 from rfl, h]; simp
  have hl : WCT9.lowSelected 0 a = false := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 128 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl]
def cfFlag (_b : Nat) : Nat := 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨
    (DigW A ∨ (CanonicalHooks.CreditW A ∨ A = FLAG))
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 32
  x15 : A.tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay)
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
  zt : ZeroCap.ZtOK b s
  floorLt : A.lay≠0 → A.floor<22
  floorTop : A.lay=0 → A.floor=22
  floorMem : A.lay≠0 → s.getMem (0x66010#64)=BitVec.ofNat 64 A.floor
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) :
    Option (BitVec 32 × List Nat × Bool) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds, low), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, WCT9.CanonicalPolicy.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧
      t.getMem (0x66018#64)=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds) ∧
      A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.stepCredit {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' CanonicalHooks.CreditW) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalHooks.CreditW ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalHooks.CreditW ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalHooks.CreditW ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
theorem TrialSt.stepFlag {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (fun A => A = FLAG)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat × Bool) → MachineState → Prop}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < capLimit A.lay.val)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  have hcap := capLimit_le A.lay.val
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl
theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
structure RewardReady (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (ds : List Nat) (low : Bool)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf A.ret
  trial : TrialSt b A s0 i t
  len : ds.length=T3.chainCount A.lay
  digs : ∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)
  credit : t.getMem (0x66018#64)=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} {ds : List Nat} {low : Bool}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0) (hu : RewardReady b A s0 i ds low u)
    (hi : i < capLimit A.lay.val) (answer : Digest) (hdec : WCT9.CanonicalPolicy.decode A.lay answer = some ds)
    (hfloor : A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds) :
    TBSim image sk u 0 (pure (some (BitVec.ofNat 32 i,ds,low))) (CsPost image b A s0) := by
  have hcap := capLimit_le A.lay.val
  have hc : (BitVec.ofNat 32 i).toNat=i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.pure ⟨hu.pc,?_,?_,?_,⟨answer,hdec⟩,hu.len,hu.digs,hu.trial.regs,hu.trial.frame,hu.sum,hu.credit,hfloor⟩
  · rw [hc]; omega
  · rw [hc]; exact hu.trial.x19
  · rw [hc]; exact hu.trial.c32

theorem cs_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 433)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (hv : T3.lowerSpare v) (S : Nat) (ds : List Nat) (hdec : WCT9.CanonicalPolicy.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) - S]) (hS : S ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) (low : Bool)
    (hcredit : u.getMem (0x66018#64)=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)) :
    ∃ k t, Steps image u k k t ∧ k ≤ 815 ∧ RewardReady b A s0 i ds low t := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨u1, su1, pu1, a6, a7, ru1, fu1⟩ := Credit.align_spec hK u hpc v hv h6 h7
  have hu1 := hu.step ru1 (by decide) fu1
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u1 pu1 (BitVec.ofNat 128 (T3.lowerWord v)) A.lay.val
    (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu1.reg (by decide), hpre.x1]) (by rw [hu1.reg (by decide), hpre.x8])
    (by rw [hu1.reg (by decide), hpre.x17]) (by rw [ru1.get (by decide), h25])
    (by rw [hu1.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu1.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) a6 a7
  rw [if_neg hl0] at kle tdig
  have hfr := (hu1.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hregs : RegsExcept s0 t csRegs := (hu1.regs.trans tr).mono (by decide)
  refine ⟨5+k,t,su1.trans st,by omega,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu1.x19]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h16]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h24]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.c32]
  · rw [hds,chainCount_eq,if_neg hlz]; simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq,if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length];exact hj),lowDigits_eq,getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]),lowDigits_length]
      simpa using tchk hl0
  · rw [tr.get (by decide),ru1.get (by decide),h25,BitVec.toNat_ofNat]
    have := target_lt (WCT9.CanonicalPolicy.normalLayer A.lay)
    omega
  · rw [tf.get (by decide) (by unfold DigW DIGITS;omega),fu1.get (by decide) (by simp),hcredit]
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW CanonicalHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.reward {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : Reward.RewardTablesOK s0) : Reward.RewardTablesOK u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.zt {A : CsArgs} {s0 u : MachineState} {i : Nat} {b' : Nat} (hb' : b' = 354 ∨ b' = 543)
    (hu : TrialSt b A s0 i u) (ht : ZeroCap.ZtOK b' s0) : ZeroCap.ZtOK b' u :=
  ht.frame hu.frame (by
    intro j hj; rcases hb' with rfl | rfl <;>
      simp only [ZeroCap.ZT, CsW, CanonicalHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] <;> norm_num <;> omega)
theorem cs_top_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 363))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest)
    (hvalid : T3.topRanksValid (T3.topFlip v) = true)
    (hdec : WCT9.CanonicalPolicy.decode A.lay (T3.topFlip v) = some (topDigits (T3.topFlip v)))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 146#64) (h20 : u.getReg .x20 = 0) (low : Bool)
    (hcredit : u.getMem (0x66018#64)=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low (topDigits (T3.topFlip v)))) :
    ∃ t, Steps image u 301 301 t ∧ RewardReady b A s0 i (topDigits (T3.topFlip v)) low t := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hvalid (hu.table hpre.table) hpc h6 h7 h30 h20 A.ret
    (by rw [hu.reg (by decide),hpre.x1])
  have hregs : RegsExcept s0 t csRegs := (hu.regs.trans tr).mono (by decide)
  have hfr : Frame s0 t CsW := (hu.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  refine ⟨t,st,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu.x19]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.h16]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.h24]
    · rw [tf.get (by unfold ENC;omega) (by unfold TopUnpack.Writes DIGITS ENC;omega),hu.c32]
  · rw [hlz,topDigits_length];rfl
  · intro j hj
    rw [hlz] at hj
    change j<54 at hj
    rw [tdig j hj]
    simp only [topDigits,getD_map_range hj]
  · rw [tr.get (by decide),h25,hlz];decide
  · rw [tf.get (by decide) (by unfold TopUnpack.Writes DIGITS;omega),hcredit]
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ 14 ∧ t2.pc = pcOf (b + 123) ∧
      fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  have hcap := capLimit_le A.lay.val
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 CsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ A, A < 2 ^ 64 → ¬ CsW A → t2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  have hk : k1 + 8 ≤ 14 := by omega
  refine ⟨_, t2, s1.trans s2, hk, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (BC.encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, BC.wordsOf_encodingInput, hc]
  have nw : ∀ A, A = ENC ∨ A = ENC + 8 ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 → ¬ CsW A := by
    intro A hA; simp only [CsW, CanonicalHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by change 0<256;decide
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i=capLimit A.lay.val) :
    TBSim image sk t (0*csT A.lay+csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨k1,t1,s1,k1le,p1,r1,f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide),hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1≤6 := k1le
  have h8 : t1.getReg .x8=BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide),hI.regs.get (by decide),hpre.x8]
  have fr1 : Frame s0 t1 CsW := (hI.frame.trans f1).mono (fun A _ h=>by simpa using h)
  have hcf : CfTableOK 0 t1 := hpre.cf.frame fr1
    (by intro j hj hj';unfold CsW CanonicalHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG;omega)
  obtain ⟨n,t2,hn,s2,p2,r2,f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 0
    (by decide) hcf (Or.inr rfl)
  obtain ⟨t3,s3,p3,h5,h10,hf⟩ := cs0_spec hK t2 p2
  change TBSim image sk t _ (pure none) _
  refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h=>h)
  · exact ⟨p3,h5,h10,hf⟩
  · unfold csOk;split_ifs <;> omega

end trial
end SigGolfCandidate.T3M.Search.Canonical

namespace SigGolfCandidate.T3M.Search.Canonical
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
variable {image : Image} {sk : BitVec 256}
/-- One top trial (r3-lean-sign): from the top flip (`tcBase`) with the raw half `v` in `x6`, `x7` and the choice flag
clear exactly on the LOW trial, either accept (`RewardReady`) or reach `choice_r`. -/
theorem top_trial {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hK : KernAt image 543 (CanonicalHooks.Code image)) (hpre : CsPre 543 A s0) (hlz : A.lay = 0)
    (hu : TrialSt 543 A s0 i u) (hpc : u.pc = pcOf (tcBase 543)) (hi22 : i < 2 ^ 22) (v : Digest)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (low : Bool) (hfl : u.getMem (BitVec.ofNat 64 FLAG) = 0 ↔ low = true) :
    (∀ ds, WCT9.CanonicalPolicy.producerDecodeAt 0 22 low v = some ds →
      ∃ k t, Steps image u k k t ∧ k ≤ 640 ∧ RewardReady 543 A s0 i ds low t ∧
        WCT9.CanonicalPolicy.decode A.lay v = some ds ∧ A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds) ∧
    (WCT9.CanonicalPolicy.producerDecodeAt 0 22 low v = none →
      ∃ k t, Steps image u k k t ∧ k ≤ 335 ∧ t.pc = pcOf (choiceBase 543 + 3) ∧ TrialSt 543 A s0 i t ∧
        Frame u t (fun A => A = 0x66018)) := by
  have hfloor : A.floor = 22 := hpre.floorTop hlz
  obtain ⟨tc,sc,pcc,h6c,h7c,rc,fc⟩ := tc_spec hK u hpc v h6 h7
  have hTc := hu.step rc (by decide) fc
  obtain ⟨w,rfl⟩ : ∃ w, v = T3.topFlip w := ⟨T3.topFlip v,(T3.topFlip_topFlip v).symm⟩
  rw [T3.topFlip_topFlip] at h6c h7c
  have hdec : WCT9.CanonicalPolicy.decode 0 (T3.topFlip w)=
      (if topLookupSum w=146 then some (topDigits (T3.topFlip w)) else none) := by
    simpa [WCT9.CanonicalPolicy.decode,WCT9.CanonicalPolicy.normalLayer] using decode_top_lookup w
  obtain ⟨t5,s5,p5,r5,f5⟩ := cs263_spec hK tc pcc
  have hT5 := hTc.step r5 (by decide) f5
  obtain ⟨t6,s6,p6,h25',h30',r6,f6⟩ := topCheck_spec hK t5 w p5
    (by rw [r5.get (by decide),h6c]) (by rw [r5.get (by decide),h7c])
    (by rw [hT5.reg (by decide),hpre.x17,hlz];rfl) (hT5.table hpre.table).sum
  have hT6 := hT5.step r6 (by decide) f6
  by_cases hs : topLookupSum w=146
  · rw [if_pos hs] at p6
    have hd' : WCT9.CanonicalPolicy.decode 0 (T3.topFlip w)=some (topDigits (T3.topFlip w)) := by rw [hdec,if_pos hs]
    have hpd := producerDecode_top (T3.topFlip w) 22 low hd'
    have hvalid := ((topLookupSum_eq_iff w).mp hs).1
    obtain ⟨t7,s7,p7,r7,f7⟩ := TopUnpack.jump_spec hK t6 p6
    have hT7 := hT6.step r7 (by decide) f7
    have hfl7 : t7.getMem (BitVec.ofNat 64 FLAG) = 0 ↔ low = true := by
      rw [f7.get (by decide) (by simp),f6.get (by decide) (by simp),f5.get (by decide) (by simp),
        fc.get (by decide) (by simp)]; exact hfl
    obtain ⟨kf,tf,sf,kfle,pf,mf,rf,ff⟩ := CanonicalHooks.top_spec_credit hK.reward t7 w
      (hT7.reward hpre.reward) (hT7.zt (Or.inr rfl) hpre.zt) hvalid p7
      (by rw [r7.get (by decide),r6.get (by decide),r5.get (by decide),h6c])
      (by rw [r7.get (by decide),r6.get (by decide),r5.get (by decide),h7c]) low hfl7
    have hTf := hT7.stepCredit rf (by decide) (ff.mono (fun A _ h => h))
    change tf.pc=(if rewardOK 0 22 low (topDigits (T3.topFlip w)) ∧
      WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip w)) then _ else _) at pf
    change (rewardOK 0 22 low (topDigits (T3.topFlip w)) ∧ WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip w)) → _) at mf
    by_cases hok : rewardOK 0 22 low (topDigits (T3.topFlip w)) ∧ WCT9.canonicalZeroBound 0 (topDigits (T3.topFlip w))
    · rw [if_pos hok] at pf
      rw [if_pos hok] at hpd
      refine ⟨fun ds hds => ?_, fun hn => (by rw [hpd] at hn; cases hn)⟩
      rw [hpd] at hds; cases hds
      obtain ⟨t8,s8,p8,g20,r8,f8⟩ := Credit.ok_spec hK tf pf
      have hT8 := hTf.step r8 (by decide) f8
      obtain ⟨t9,s9,hR⟩ := cs_top_prepare hK hpre hT8 p8 hi22 hlz w hvalid (by rw [hlz]; exact hd')
        (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),r6.get (by decide),r5.get (by decide),h6c])
        (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),r6.get (by decide),r5.get (by decide),h7c])
        (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide),h30'])
        (by rw [r8.get (by decide),rf.get (by decide),r7.get (by decide)];simpa only [hs] using h25') g20 low
        (by rw [f8.get (by decide) (by simp),hlz];exact mf hok)
      refine ⟨_,t9,(((((((sc.trans s5).trans s6).trans s7).trans sf).trans s8).trans s9)),by omega,hR,
        by rw [hlz]; exact hd',?_⟩
      rw [hfloor,hlz]; exact reward_credit_le hok.1
    · rw [if_neg hok] at pf
      rw [if_neg hok] at hpd
      refine ⟨fun ds hds => (by rw [hpd] at hds; cases hds), fun _ => ?_⟩
      exact ⟨_,tf,((((sc.trans s5).trans s6).trans s7).trans sf),by omega,pf,hTf,
        ((((fc.trans f5).trans f6).trans f7).trans ff).mono (fun A _ h => by
          simp only [false_or] at h; exact h)⟩
  · rw [if_neg hs] at p6
    have hd' : WCT9.CanonicalPolicy.decode 0 (T3.topFlip w)=none := by rw [hdec,if_neg hs]
    have hpd : WCT9.CanonicalPolicy.producerDecodeAt 0 22 low (T3.topFlip w)=none := by
      simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
    refine ⟨fun ds hds => (by rw [hpd] at hds; cases hds), fun _ => ?_⟩
    obtain ⟨t7,s7,p7,r7,f7⟩ := retry_spec hK t6 p6
    exact ⟨_,t7,(((sc.trans s5).trans s6).trans s7),by omega,p7,hT6.step r7 (by decide) f7,
      (((fc.trans f5).trans f6).trans f7).mono (fun A _ h => by simp at h)⟩

theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image 543 (CanonicalHooks.Code image)) (hpre : CsPre 543 A s0) :
    ∀ F i t, i + F = capLimit A.lay.val → CsInv 543 A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i F)
        (CsPost image 543 A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h,fun h => by rw [h];rfl⟩
  have hcap := capLimit_le A.lay.val
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < capLimit A.lay.val := by omega
    have hi22 : i < 2 ^ 22 := by omega
    obtain ⟨k2,t2,s2,k2le,p2,hf,h5,hv,hq,h12,hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i (F+1) =
        (T3.publicHash (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor answer with
          | none => WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F
          | some found => pure (some (BitVec.ofNat 32 i,found))) := rfl
    have ih' : ∀ t, CsInv 543 A s0 (i+1) t → TBSim image sk t (F*csT A.lay+csOk A.lay)
        (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F) (CsPost image 543 A s0) :=
      fun t ht => ih (i+1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.publicHash_bindC hf h5 hv hq
      (W:=F*csT A.lay+csOk A.lay+(csT A.lay-22)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [BC.blocks_encodingInput,Nat.succ_mul];unfold csT at *;split_ifs at k2le ⊢ <;> omega
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc=pcOf (543+124) := by rw [pc_writeHash,p2,pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    have hhi := DigAt.writeHash_hi t2 a EOUT h12 (by decide)
    obtain ⟨t4,s4,p4,h6,h7,h25,r4,f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide),hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    -- the answer halves stay in `EOUT .. EOUT + 32` (frames below never write there)
    have mL0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 EOUT) = t4.getMem (BitVec.ofNat 64 EOUT) →
        w.getMem (BitVec.ofNat 64 EOUT) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.1
    have mL8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+8)) = t4.getMem (BitVec.ofNat 64 (EOUT+8)) →
        w.getMem (BitVec.ofNat 64 (EOUT+8)) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.2
    have mH0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+16)) = t4.getMem (BitVec.ofNat 64 (EOUT+16)) →
        w.getMem (BitVec.ofNat 64 (EOUT+16)) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.1
    have mH8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+24)) = t4.getMem (BitVec.ofNat 64 (EOUT+24)) →
        w.getMem (BitVec.ofNat 64 (EOUT+24)) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.2
    by_cases hlz : A.lay=0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hfl : A.floor = 22 := hpre.floorTop hlz
      have e : WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor a = WCT9.CanonicalPolicy.producerDecodeOut 0 22 a := by
        rw [hlz,hfl]
      rw [e]
      obtain ⟨tg,sg,pg,gflag,rg,fg⟩ := top_select_spec hK t4 p4
      have hTg := hT4.stepFlag rg (by decide) fg
      have fgE : ∀ X, X ≠ FLAG → X < 2^64 → tg.getMem (BitVec.ofNat 64 X) = t4.getMem (BitVec.ofNat 64 X) :=
        fun X hX hX' => fg.get hX' hX
      obtain ⟨hLs,hLn⟩ := top_trial hK hpre hlz hTg pg hi22 (a.extractLsb' 0 128)
        (by rw [rg.get (by decide),h6]) (by rw [rg.get (by decide),h7]) true (by simp [gflag])
      cases hL : WCT9.CanonicalPolicy.producerDecodeAt 0 22 true (a.extractLsb' 0 128) with
      | some ds =>
        rw [producerDecodeOut_top_low a hL]
        obtain ⟨k,t,st,kle,hR,hdec,hfloor⟩ := hLs ds hL
        have done := cs_success (sk:=sk) hK hpre hR hi _ hdec hfloor
        refine (TBSim.steps ((s4.trans sg).trans st) done).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz];omega
      | none =>
        obtain ⟨k,t,st,kle,pt,hTt,ft⟩ := hLn hL
        have ftE : ∀ X, X ≠ 0x66018 → X < 2^64 → t.getMem (BitVec.ofNat 64 X) = tg.getMem (BitVec.ofNat 64 X) :=
          fun X hX hX' => ft.get hX' hX
        obtain ⟨kr,tr,sr,krle,hr,rr,fr⟩ := choiceR_spec hK t pt a
          (mL8 t (by rw [ftE _ (by unfold EOUT;omega) (by unfold EOUT;omega),fgE _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega)]))
          (mH0 t (by rw [ftE _ (by unfold EOUT;omega) (by unfold EOUT;omega),fgE _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega)]))
          (mH8 t (by rw [ftE _ (by unfold EOUT;omega) (by unfold EOUT;omega),fgE _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega)]))
        have tflag : t.getMem (BitVec.ofNat 64 FLAG) = 0 := by rw [ftE _ (by unfold FLAG;omega) (by unfold FLAG;omega)]; exact gflag
        have hTr := hTt.stepFlag rr (by decide) fr
        by_cases hb : T3.TopChoice.blocked (a.extractLsb' 0 128)
        · rw [producerDecodeOut_top_blocked a hL hb]
          rw [if_neg (fun h => h.2 hb)] at hr
          refine (TBSim.steps (((s4.trans sg).trans st).trans sr) (cs_next hK hTr hr hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_pos hlz];omega
        · rw [producerDecodeOut_top_high a hL hb]
          rw [if_pos ⟨tflag,hb⟩] at hr
          obtain ⟨pr,r6',r7',rflag⟩ := hr
          obtain ⟨hHs,hHn⟩ := top_trial hK hpre hlz hTr pr hi22 (a.extractLsb' 128 128) r6' r7' false
            (by rw [rflag]; decide)
          have frE : ∀ X, X ≠ FLAG → X < 2^64 → tr.getMem (BitVec.ofNat 64 X) = t.getMem (BitVec.ofNat 64 X) :=
            fun X hX hX' => fr.get hX' hX
          cases hH : WCT9.CanonicalPolicy.producerDecodeAt 0 22 false (a.extractLsb' 128 128) with
          | some ds =>
            obtain ⟨k',t',st',kle',hR,hdec,hfloor⟩ := hHs ds hH
            have done := cs_success (sk:=sk) hK hpre hR hi _ hdec hfloor
            refine (TBSim.steps ((((s4.trans sg).trans st).trans sr).trans st') done).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_pos hlz];omega
          | none =>
            obtain ⟨k',t',st',kle',pt',hTt',ft'⟩ := hHn hH
            have ftE' : ∀ X, X ≠ 0x66018 → X < 2^64 → t'.getMem (BitVec.ofNat 64 X) = tr.getMem (BitVec.ofNat 64 X) :=
              fun X hX hX' => ft'.get hX' hX
            have back : ∀ X, X ≠ FLAG → X ≠ 0x66018 → X < 2^64 →
                t'.getMem (BitVec.ofNat 64 X) = t4.getMem (BitVec.ofNat 64 X) := by
              intro X h1 h2 h3; rw [ftE' X h2 h3,frE X h1 h3,ftE X h2 h3,fgE X h1 h3]
            obtain ⟨kr',tr',sr',krle',hr',rr',fr'⟩ := choiceR_spec hK t' pt' a
              (mL8 t' (back _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega) (by unfold EOUT;omega)))
              (mH0 t' (back _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega) (by unfold EOUT;omega)))
              (mH8 t' (back _ (by unfold EOUT FLAG;omega) (by unfold EOUT;omega) (by unfold EOUT;omega)))
            have t'flag : t'.getMem (BitVec.ofNat 64 FLAG) = BitVec.ofNat 64 128 := by
              rw [ftE' _ (by unfold FLAG;omega) (by unfold FLAG;omega)]; exact rflag
            rw [if_neg (fun h => by rw [t'flag] at h; exact absurd h.1 (by decide))] at hr'
            have hTr' := hTt'.stepFlag rr' (by decide) fr'
            refine (TBSim.steps (((((s4.trans sg).trans st).trans sr).trans st').trans sr')
              (cs_next hK hTr' hr' hi ih')).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_pos hlz];omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      set v := WCT9.encodingAnswer A.lay a with hvdef
      set low := decide (T3.lowerSpare (a.extractLsb' 0 128)) with hlowdef
      have hlow : WCT9.lowSelected A.lay a = low := by simp [WCT9.lowSelected,hlz,hlowdef]
      unfold WCT9.CanonicalPolicy.producerDecodeOut
      rw [hlow]
      obtain ⟨td,sd,pd,rd,fd⟩ := cs130_spec hK t4 p4
      have hTd := hT4.step rd (by decide) fd
      obtain ⟨ks,t5,ss,hs7,p5,h6s,h7s,r5,f5⟩ := selector_spec hK td pd a A.lay hlz
        ((rd.get (by decide)).trans h6) ((rd.get (by decide)).trans h7)
        (by rw [rd.get (by decide),r4.get (by decide),getReg_writeHash,h12])
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.1)
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.2)
      have s5 := sd.trans ss
      have hT5 := hTd.step r5 (by decide) f5
      change t5.pc=(if T3.lowerSpare v then _ else _) at p5
      change t5.getReg .x6=v.extractLsb' 0 64 at h6s
      change t5.getReg .x7=v.extractLsb' 64 64 at h7s
      have hnormal : WCT9.CanonicalPolicy.normalLayer A.lay≠0 := by
        simp [WCT9.CanonicalPolicy.normalLayer,hlz]
      have hdec := decode_low (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal v
      change WCT9.CanonicalPolicy.decode A.lay v=_ at hdec
      by_cases hr : T3.lowerSpare v
      · rw [if_pos hr] at p5
        obtain ⟨t6,s6,p6,h25',h28',r6,f6⟩ := cs132_spec hK t5 p5 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (target_lt _) h6s h7s
          (by rw [r5.get (by decide),rd.get (by decide),h25]) (by rw [hT5.reg (by decide),hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum≤T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum<8
        · rw [if_pos hs] at p6
          obtain ⟨t7,s7,p7,r7,f7⟩ := cs259_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=some (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) := by rw [hdec,if_pos ⟨hr,hs⟩]
          rw [producerDecode_lower hlz v A.floor _ low hd' rfl]
          obtain ⟨k8,n8,t8,s8,n8le,p8,r8,f8⟩ := zero_rank_spec hK t7 p7 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
            (by
              have h : ∀ lay : T3.Layer,T3.target lay<256 := by decide
              exact h (WCT9.CanonicalPolicy.normalLayer A.lay)) hs.1
            (by rw [r7.get (by decide),r6.get (by decide),h6s])
            (by rw [r7.get (by decide),r6.get (by decide),h7s])
            (by rw [hT7.reg (by decide),hpre.x17]) (by rw [r7.get (by decide),h25'])
            (lowZeros_bound v (by
              have hmin : ∀ lay : T3.Layer,lay≠0 → 199≤T3.target lay := by decide
              have ht := hmin (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal;omega))
          have hT8 := hT7.step r8 (by decide) f8
          have fL8 : Frame t4 t8 (fun _ => False) := ((((((fd.trans f5).trans f6).trans f7).trans f8)).mono
            (fun A _ h => by simp at h))
          by_cases hok : (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v
          · rw [if_pos hok] at p8
            have hTables : Reward.RewardTablesOK t8 := hpre.reward.frame hT8.frame
              (by intro j hj hj'; unfold CsW CanonicalHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
            obtain ⟨kR,tR,sR,kRle,pR,mR,rR,fR⟩ := CanonicalHooks.lower_spec_credit hK t8 A.lay hlz v hTables p8
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
              (a.extractLsb' 0 128) (mL0 t8 (fL8.get (by decide) (by simp))) (mL8 t8 (fL8.get (by decide) (by simp)))
              (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (lowDigits v).sum A.floor
              (by rw [hT8.reg (by decide),hpre.x17])
              (by rw [r8.get (by decide),r7.get (by decide),h25']) hs.1 hs.2 (hpre.floorLt hlz)
              (by rw [hT8.frame.get (by decide) (by unfold CsW CanonicalHooks.CreditW ENC EOUT DigW DIGITS FLAG;omega),hpre.floorMem hlz])
            have hTR := hT8.stepCredit rR (by decide) fR
            change tR.pc=(if rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
              then pcOf (543+433) else pcOf (543+468)) at pR
            change (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) → _) at mR
            by_cases hreward : rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
            · rw [if_pos hreward] at pR
              simp only [hreward,hok,and_self,if_true]
              obtain ⟨k9,t9,s9,k9le,hR⟩ := cs_prepare hK hpre hTR pR hi22 hlz v hr _ _ hd' rfl hs.1
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),h25']) low (mR hreward)
              have done := cs_success (sk:=sk) hK hpre hR hi v hd' (reward_credit_le hreward)
              refine (TBSim.steps ((((((s4.trans s5).trans s6).trans s7).trans s8).trans sR).trans s9) done).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
            · rw [if_neg hreward] at pR
              simp only [hreward,false_and,if_false]
              refine (TBSim.steps (((((s4.trans s5).trans s6).trans s7).trans s8).trans sR)
                (cs_next hK hTR pR hi ih')).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
          · rw [if_neg hok] at p8
            have hno : ¬ (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) ∧
                (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v) := fun hh => hok hh.2
            simp only [if_neg hno]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_neg hlz];omega
        · rw [if_neg hs] at p6
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hs h.2)]
          have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
          rw [hpd]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_neg hlz];omega
      · rw [if_neg hr] at p5
        have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hr h.1)]
        have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
        rw [hpd]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_neg hlz];omega
end SigGolfCandidate.T3M.Search.Canonical

namespace SigGolfCandidate.T3M.Search.Canonical
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
variable {image : Image} {sk : BitVec 256}
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image 543 (CanonicalHooks.Code image)) (hpre : CsPre 543 A s0) :
    TBSim image sk s0 (18 + capLimit A.lay.val * csT A.lay + csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay)) (CsPost image 543 A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay A.tree A.leaf hpre.hroute
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  obtain ⟨t', st', pt', rt', ft'⟩ := cs113_spec hK t pt
  have hI : CsInv 543 A s0 0 t' := by
    refine ⟨pt', Nat.zero_le _, by rw [rt'.get (by decide), h19], by rw [ft'.get (by simp only [ENC]; omega) (by simp), h16],
      by rw [ft'.get (by simp only [ENC]; omega) (by simp), h24], ?_,
      (rt.trans rt').mono (by decide), (ft.trans ft').mono (fun A _ h => by
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd h id)⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft'.get (by simp only [ENC]; omega) (by simp), ft.get (by simp only [ENC]; omega)
      (by simp only [ENC]; omega), hx32]⟩
  rw [← capLimit_eq]
  have := TBSim.steps st (TBSim.steps st' (cs_loop (sk := sk) hK hpre (capLimit A.lay.val) 0 t' (by omega) hI))
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)

def csCost (lay : Layer) : Nat := (WCT9.searchLimit lay * csT lay)+8192

theorem counterSearch_good {A : CsArgs} {s0 : MachineState}
    (hK : KernAt image 543 (CanonicalHooks.Code image)) (hp : CsPre 543 A s0) :
    TBSim image sk s0 (csCost A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
      (CsPost image 543 A s0) := by
  refine (counterSearch_tbsim hK hp).mono ?_ (fun _ _ h=>h)
  rw [capLimit_eq]
  unfold csCost csOk
  split_ifs <;> omega
end SigGolfCandidate.T3M.Search.Canonical

