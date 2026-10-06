import SigGolfCandidate.T3M.Search.CsBlocks

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
def capLimit (lay : Nat) : Nat := if lay = 0 then 2 ^ 22 else 2 ^ 21
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
def scanFloor (lay : Nat) : Nat := if lay = 3 then 2 else 4
section blocks
variable {image : Image} {b : Nat}
theorem capA0_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 0)) (i : Nat)
    (hi : i < 2 ^ 64) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if i < 2 ^ 21 then pcOf (capBase b + 5) else pcOf (capBase b + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_0 hK.2) (codeAt_a_0 hK) s hpc (by simp [sta_0, blkA354_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_0, rebase, blkA354_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i < 2 ^ 21
    · have : (BitVec.ofNat 64 i).ult 2097152#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; simpa using h
      simp [this, show i < 2097152 by omega]
    · have : (BitVec.ofNat 64 i).ult 2097152#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; simp; omega
      simp [this, show ¬ i < 2097152 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_0, blkA354_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_0, blkA354_0.res, rv_simp]
theorem capA2_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 2)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if lay = 0 then pcOf (capBase b + 3) else pcOf (capBase b + 6)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_2 hK.2) (codeAt_a_2 hK) s hpc (by simp [sta_2, blkA354_2.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_2, rebase, blkA354_2.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 lay != 0#64) = true := by
        rw [bne_iff_ne, ne_eq, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]; omega
      simp [this, h]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_2, blkA354_2.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_2, blkA354_2.res, rv_simp]
theorem capA3_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 3)) (i : Nat)
    (hi : i < 2 ^ 64) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if i = 2 ^ 22 then pcOf (capBase b + 6) else pcOf (capBase b + 5)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_3 hK.2) (codeAt_a_3 hK) s hpc (by simp [sta_3, blkA354_3.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_3, rebase, blkA354_3.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 22
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 4194304#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_3, blkA354_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_3, blkA354_3.res, rv_simp]
theorem capA5_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 115) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_5 hK.2) (codeAt_a_5 hK) s hpc (by simp [sta_5, blkA354_5.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcEa_5, blkA354_5.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_5, blkA354_5.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_5, blkA354_5.res, rv_simp]
theorem capA6_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 6)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 424) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_6 hK.2) (codeAt_a_6 hK) s hpc (by simp [sta_6, blkA354_6.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcEa_6, blkA354_6.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_6, blkA354_6.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_6, blkA354_6.res, rv_simp]
theorem cap_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b)) (lay i : Nat)
    (hl : lay < 4) (hi : i ≤ capLimit lay) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ k t, Steps image s k k t ∧ k ≤ (if lay = 0 then 6 else 4) ∧
      t.pc = (if i = capLimit lay then pcOf (b + 424) else pcOf (b + 115)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hi64 : i < 2 ^ 64 := by unfold capLimit at hi; split_ifs at hi <;> omega
  obtain ⟨t0, s0, p0, r0, f0⟩ := capA0_spec hK s (by simpa using hpc) i hi64 h19
  by_cases hlow : i < 2 ^ 21
  · rw [if_pos hlow] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := capA5_spec hK t0 p0
    have hne : i ≠ capLimit lay := by unfold capLimit; split_ifs <;> omega
    refine ⟨_, _, s0.trans s1, by split_ifs <;> omega, by rw [p1, if_neg hne], (r0.trans r1).mono (by decide),
      (f0.trans f1).mono (fun _ _ h => by simp at h)⟩
  · rw [if_neg hlow] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := capA2_spec hK t0 p0 lay hl (by rw [r0.get (by decide), h8])
    by_cases hz : lay = 0
    · rw [if_pos hz] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := capA3_spec hK t1 p1 i hi64
        (by rw [r1.get (by decide), r0.get (by decide), h19])
      have hcap : capLimit lay = 2 ^ 22 := by unfold capLimit; rw [if_pos hz]
      by_cases htop : i = 2 ^ 22
      · rw [if_pos htop] at p2
        obtain ⟨t3, s3, p3, r3, f3⟩ := capA6_spec hK t2 p2
        refine ⟨_, _, s0.trans (s1.trans (s2.trans s3)), by rw [if_pos hz], by rw [p3, hcap, if_pos htop],
          (r0.trans (r1.trans (r2.trans r3))).mono (by decide),
          (f0.trans (f1.trans (f2.trans f3))).mono (fun _ _ h => by simp at h)⟩
      · rw [if_neg htop] at p2
        obtain ⟨t3, s3, p3, r3, f3⟩ := capA5_spec hK t2 p2
        refine ⟨_, _, s0.trans (s1.trans (s2.trans s3)), by rw [if_pos hz], by rw [p3, hcap, if_neg htop],
          (r0.trans (r1.trans (r2.trans r3))).mono (by decide),
          (f0.trans (f1.trans (f2.trans f3))).mono (fun _ _ h => by simp at h)⟩
    · rw [if_neg hz] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := capA6_spec hK t1 p1
      have hcap : capLimit lay = 2 ^ 21 := by unfold capLimit; rw [if_neg hz]
      have heq : i = capLimit lay := by rw [hcap]; unfold capLimit at hi; rw [if_neg hz] at hi; omega
      refine ⟨_, _, s0.trans (s1.trans s2), by rw [if_neg hz], by rw [p2, if_pos heq],
        (r0.trans (r1.trans r2)).mono (by decide), (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
theorem scanA7_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (c lo hi : BitVec 64)
    (h28 : s.getReg .x28 = c) (h6 : s.getReg .x6 = lo) (h7 : s.getReg .x7 = hi) :
    ∃ t, Steps image s 26 29 t ∧
      t.pc = (if lay = 3 then pcOf (capBase b + 33) else pcOf (capBase b + 35)) ∧
      t.getReg .x28 = clr (scanX c lo hi) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_7 hK.2) (codeAt_a_7 hK) s hpc (by simp [sta_7, blkA354_7.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_7, rebase, blkA354_7.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 3
    · subst h; simp
    · have : (BitVec.ofNat 64 lay != 3#64) = true := by
        rw [bne_iff_ne, ne_eq, show (3#64) = BitVec.ofNat 64 3 from rfl, ofNat_eq_iff]; omega
      simp [this, h]
  · simp only [Result.toState_getReg, sta_7, blkA354_7.res]
    simp only [rv_simp, h6, h7, h28, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [sta_7, blkA354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_7, blkA354_7.res, rv_simp]
theorem scanA33_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 33)) (x : BitVec 64)
    (h28 : s.getReg .x28 = x) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if x = 0#64 then pcOf (capBase b + 41) else pcOf (capBase b + 34)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_33 hK.2) (codeAt_a_33 hK) s hpc (by simp [sta_33, blkA354_33.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_33, rebase, blkA354_33.res, E.eval, CmpOp.eval, h28]
    by_cases h : x = 0#64
    · subst h; simp
    · simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_33, blkA354_33.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_33, blkA354_33.res, rv_simp]
theorem scanA35_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 35)) (x : BitVec 64)
    (h28 : s.getReg .x28 = x) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if clr (clr x) = 0#64 then pcOf (capBase b + 41) else pcOf (capBase b + 40)) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (runa_35 hK.2) (codeAt_a_35 hK) s hpc (by simp [sta_35, blkA354_35.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEa_35, rebase, blkA354_35.res, E.eval, CmpOp.eval, BinOp.eval, h28]
    have hm : ∀ y : BitVec 64, y + 18446744073709551615#64 = y - 1#64 := fun y => by
      rw [BitVec.sub_eq_add_neg]; rfl
    have e : (x &&& x + 18446744073709551615#64 &&& (x &&& x + 18446744073709551615#64) + 18446744073709551615#64) =
        clr (clr x) := by simp only [clr, hm]
    rw [e]
    by_cases h : clr (clr x) = 0#64 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [sta_35, blkA354_35.res, rv_simp] <;> rfl
  · intro A _ _; simp [sta_35, blkA354_35.res, rv_simp]
theorem scanJump_spec (hK : KernAt image b) (s : MachineState) {o : Nat} (ho : o = 34 ∨ o = 40 ∨ o = 41)
    (hpc : s.pc = pcOf (capBase b + o)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if o = 41 then pcOf (b + 468) else pcOf (b + 433)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  rcases ho with rfl | rfl | rfl
  · refine ⟨_, symRun_sound (runa_34 hK.2) (codeAt_a_34 hK) s hpc (by simp [sta_34, blkA354_34.res, rv_simp]),
      ?_, ?_, ?_⟩
    · simp [pcEa_34, blkA354_34.res, E.eval]
    · intro r hr; simp at hr; cases r <;> simp_all [sta_34, blkA354_34.res, rv_simp] <;> rfl
    · intro A _ _; simp [sta_34, blkA354_34.res, rv_simp]
  · refine ⟨_, symRun_sound (runa_40 hK.2) (codeAt_a_40 hK) s hpc (by simp [sta_40, blkA354_40.res, rv_simp]),
      ?_, ?_, ?_⟩
    · simp [pcEa_40, blkA354_40.res, E.eval]
    · intro r hr; simp at hr; cases r <;> simp_all [sta_40, blkA354_40.res, rv_simp] <;> rfl
    · intro A _ _; simp [sta_40, blkA354_40.res, rv_simp]
  · refine ⟨_, symRun_sound (runa_41 hK.2) (codeAt_a_41 hK) s hpc (by simp [sta_41, blkA354_41.res, rv_simp]),
      ?_, ?_, ?_⟩
    · simp [pcEa_41, blkA354_41.res, E.eval]
    · intro r hr; simp at hr; cases r <;> simp_all [sta_41, blkA354_41.res, rv_simp] <;> rfl
    · intro A _ _; simp [sta_41, blkA354_41.res, rv_simp]
theorem scan_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (capBase b + 7)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (v : Digest) (c : Nat)
    (hc : c < 8) (h28 : s.getReg .x28 = BitVec.ofNat 64 c) (h6 : s.getReg .x6 = v.extractLsb' 0 64)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ k n t, Steps image s k n t ∧ n ≤ 38 ∧
      t.pc = (if scanFloor lay ≤ scanCredit v c then pcOf (b + 433) else pcOf (b + 468)) ∧
      RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, x0, r0, f0⟩ := scanA7_spec hK s hpc lay hl h8 _ _ _ h28 h6 h7
  have hpop := pop_scanX v c hc
  set X := scanX (BitVec.ofNat 64 c) (v.extractLsb' 0 64) (v.extractLsb' 64 64)
  by_cases h3 : lay = 3
  · rw [if_pos h3] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := scanA33_spec hK t0 p0 _ x0
    have hz : clr X = 0#64 ↔ ¬ scanFloor lay ≤ scanCredit v c := by
      have := clr_iter_eq_zero_iff 1 X
      simp only [Function.iterate_one] at this
      rw [this, hpop, scanFloor, if_pos h3]; omega
    by_cases h0 : clr X = 0#64
    · rw [if_pos h0] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 41) (by omega) p1
      refine ⟨_, _, _, s0.trans (s1.trans s2), by omega, ?_, (r0.trans (r1.trans r2)).mono (by decide),
        (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
      rw [p2, if_pos rfl, if_neg (hz.mp h0)]
    · rw [if_neg h0] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 34) (by omega) p1
      refine ⟨_, _, _, s0.trans (s1.trans s2), by omega, ?_, (r0.trans (r1.trans r2)).mono (by decide),
        (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
      rw [p2, if_neg (by decide), if_pos (by by_contra hn; exact h0 (hz.mpr hn))]
  · rw [if_neg h3] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := scanA35_spec hK t0 p0 _ x0
    have hz : clr (clr (clr X)) = 0#64 ↔ ¬ scanFloor lay ≤ scanCredit v c := by
      have := clr_iter_eq_zero_iff 3 X
      simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq] at this
      rw [this, hpop, scanFloor, if_neg h3]; omega
    by_cases h0 : clr (clr (clr X)) = 0#64
    · rw [if_pos h0] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 41) (by omega) p1
      refine ⟨_, _, _, s0.trans (s1.trans s2), by omega, ?_, (r0.trans (r1.trans r2)).mono (by decide),
        (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
      rw [p2, if_pos rfl, if_neg (hz.mp h0)]
    · rw [if_neg h0] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := scanJump_spec hK t1 (o := 40) (by omega) p1
      refine ⟨_, _, _, s0.trans (s1.trans s2), by omega, ?_, (r0.trans (r1.trans r2)).mono (by decide),
        (f0.trans (f1.trans f2)).mono (fun _ _ h => by simp at h)⟩
      rw [p2, if_neg (by decide), if_pos (by by_contra hn; exact h0 (hz.mpr hn))]
end blocks
end SigGolfCandidate.T3M.Search
end
