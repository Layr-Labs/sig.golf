import SigGolfCandidate.T3.Nonbinary.CreditFilter

/-! Campaign R6 + RC (COUNT): exact counting model of the R6 top word.
A word is the 8 r6 ranks (`< 216`, groups 0..7, chains `3g .. 3g+2`) and the 9 r5 ranks (`< 125`, groups 8..16).
Per triple: digit sum, zero digits, credit (digits one below the maximum), safe copies, and the dispatch-penalty
complement on the penalised r5 groups 8, 10, 11, 12. The generating polynomial in `B = 2^128` with exponent
`stat = 34808 * zeros + 152 * sum + score` (score `≤ 149`, sum `≤ 228`) is computed modulo `B^(34808*8)` (zero
counts `≤ 7`). -/
namespace SigGolfResearch.R6Top
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-- Digit `k` (0, 1, 2) of a triple rank in radix `b`. -/
def dg (b r k : Nat) : Nat := r / b ^ k % b
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def tsum (b r : Nat) : Nat := dg b r 0 + dg b r 1 + dg b r 2
def tzeros (b r : Nat) : Nat := ind (dg b r 0 = 0) + ind (dg b r 1 = 0) + ind (dg b r 2 = 0)
def tcredit (b r : Nat) : Nat := ind (dg b r 0 + 1 = b - 1) + ind (dg b r 1 + 1 = b - 1) + ind (dg b r 2 + 1 = b - 1)
def tcopies (b : Nat) (first : Bool) (r : Nat) : Nat :=
  ind (first = true ∧ dg b r 0 = b - 1) + ind (dg b r 1 = b - 1 ∧ dg b r 0 = b - 1) +
    ind (dg b r 2 = b - 1 ∧ dg b r 1 = b - 1)
/-- Score of a triple: credit, 4 per safe copy, and on a penalised group 1 when its digit sum is at least 3. -/
def tscore (b : Nat) (first pen : Bool) (r : Nat) : Nat :=
  tcredit b r + 4 * tcopies b first r + (if pen = true then ind (3 ≤ tsum b r) else 0)
def tstat (b : Nat) (first pen : Bool) (r : Nat) : Nat := 34808 * tzeros b r + 152 * tsum b r + tscore b first pen r

/-- The penalised r5 groups: 8, 10, 11, 12 (index `j = q - 8`). -/
def pen (j : Fin 9) : Bool := decide (j.val = 0 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4)

abbrev R6Word := (Fin 8 → Fin 216) × (Fin 9 → Fin 125)

def weight (w : R6Word) : Nat := (∑ g : Fin 8, tsum 6 (w.1 g).val) + ∑ j : Fin 9, tsum 5 (w.2 j).val
def zeros (w : R6Word) : Nat := (∑ g : Fin 8, tzeros 6 (w.1 g).val) + ∑ j : Fin 9, tzeros 5 (w.2 j).val
def score (w : R6Word) : Nat :=
  (∑ g : Fin 8, tscore 6 (decide (g.val = 0)) false (w.1 g).val) + ∑ j : Fin 9, tscore 5 false (pen j) (w.2 j).val
def stat (w : R6Word) : Nat :=
  (∑ g : Fin 8, tstat 6 (decide (g.val = 0)) false (w.1 g).val) + ∑ j : Fin 9, tstat 5 false (pen j) (w.2 j).val
/-- LOW is not forced (`TopChoice.blocked` fails): the r6 rank of group 7 is at least 128. -/
def isFree (w : R6Word) : Prop := 128 ≤ (w.1 7).val
instance (w : R6Word) : Decidable (isFree w) := inferInstanceAs (Decidable (128 ≤ (w.1 7).val))

theorem stat_eq (w : R6Word) : stat w = 34808 * zeros w + 152 * weight w + score w := by
  simp only [stat, tstat, zeros, weight, score, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem tscore6_le (first : Bool) (r : Fin 216) : tscore 6 first false r.val ≤ if first then 12 else 8 := by
  revert first r; decide +kernel
theorem tscore5_le (p : Bool) (r : Fin 125) : tscore 5 false p r.val ≤ 9 := by
  revert p r; decide +kernel
theorem tsum6_le (r : Fin 216) : tsum 6 r.val ≤ 15 := by revert r; decide +kernel
theorem tsum5_le (r : Fin 125) : tsum 5 r.val ≤ 12 := by revert r; decide +kernel

theorem score_le (w : R6Word) : score w ≤ 149 := by
  have h6 : (∑ g : Fin 8, tscore 6 (decide (g.val = 0)) false (w.1 g).val) ≤
      ∑ g : Fin 8, (if g.val = 0 then 12 else 8) := by
    apply Finset.sum_le_sum; intro g _
    simpa using tscore6_le (decide (g.val = 0)) (w.1 g)
  have h5 : (∑ j : Fin 9, tscore 5 false (pen j) (w.2 j).val) ≤ ∑ _j : Fin 9, 9 :=
    Finset.sum_le_sum fun j _ => tscore5_le (pen j) (w.2 j)
  have hb : (∑ g : Fin 8, (if g.val = 0 then 12 else 8)) = 68 := by decide +kernel
  simp only [hb, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h6 h5
  unfold score; omega

theorem weight_le (w : R6Word) : weight w ≤ 228 := by
  have h6 : (∑ g : Fin 8, tsum 6 (w.1 g).val) ≤ ∑ _g : Fin 8, 15 := Finset.sum_le_sum fun g _ => tsum6_le (w.1 g)
  have h5 : (∑ j : Fin 9, tsum 5 (w.2 j).val) ≤ ∑ _j : Fin 9, 12 := Finset.sum_le_sum fun j _ => tsum5_le (w.2 j)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h6 h5
  unfold weight; omega

theorem word_card : Fintype.card R6Word = 216 ^ 8 * 125 ^ 9 := by
  simp [R6Word, Fintype.card_prod, Fintype.card_fun]

/-! ### Generating polynomial -/
def B : Nat := 2 ^ 128

/-- Per-group weights; `free` restricts group 7 to ranks `≥ 128`. -/
def w6 (y : Nat) (free : Bool) (g : Fin 8) (r : Fin 216) : Nat :=
  if free = true ∧ g.val = 7 ∧ r.val < 128 then 0 else y ^ tstat 6 (decide (g.val = 0)) false r.val
def w5 (y : Nat) (j : Fin 9) (r : Fin 125) : Nat := y ^ tstat 5 false (pen j) r.val

theorem prod_w6 (y : Nat) (free : Bool) (f : Fin 8 → Fin 216) :
    (∏ g : Fin 8, w6 y free g (f g)) =
      if free = true ∧ (f 7).val < 128 then 0 else y ^ ∑ g : Fin 8, tstat 6 (decide (g.val = 0)) false (f g).val := by
  rw [← Finset.prod_pow_eq_pow_sum]
  by_cases h : free = true ∧ (f 7).val < 128
  · rw [if_pos h]
    apply Finset.prod_eq_zero (Finset.mem_univ 7)
    simp [w6, h.1, h.2]
  · rw [if_neg h]
    apply Finset.prod_congr rfl
    intro g _
    unfold w6
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    apply h
    have hg : g = 7 := Fin.ext h2
    subst hg
    exact ⟨h1, h3⟩

theorem prod_w5 (y : Nat) (f : Fin 9 → Fin 125) :
    (∏ j : Fin 9, w5 y j (f j)) = y ^ ∑ j : Fin 9, tstat 5 false (pen j) (f j).val := by
  rw [← Finset.prod_pow_eq_pow_sum]; rfl

/-- The (free-restricted) weighted word sum factors over the 17 groups. -/
theorem weighted_words (y : Nat) (free : Bool) :
    (∑ w : R6Word, if free = true ∧ ¬ isFree w then 0 else y ^ stat w) =
      (∏ g : Fin 8, ∑ r : Fin 216, w6 y free g r) * ∏ j : Fin 9, ∑ r : Fin 125, w5 y j r := by
  rw [Fintype.prod_sum (fun g r => w6 y free g r), Fintype.prod_sum (fun j r => w5 y j r),
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro e _
  rw [prod_w6, prod_w5]
  simp only [isFree, not_le, stat, pow_add]
  split_ifs <;> simp

/-- The 17 group factors in order. -/
def G6 (y : Nat) (first : Bool) : Nat := ∑ r : Fin 216, y ^ tstat 6 first false r.val
def G6H (y : Nat) : Nat := ∑ r : Fin 216, if r.val < 128 then 0 else y ^ tstat 6 false false r.val
def G5 (y : Nat) (p : Bool) : Nat := ∑ r : Fin 125, y ^ tstat 5 false p r.val

def factors (y : Nat) (free : Bool) : List Nat :=
  [G6 y true, G6 y false, G6 y false, G6 y false, G6 y false, G6 y false, G6 y false,
    if free then G6H y else G6 y false,
    G5 y true, G5 y false, G5 y true, G5 y true, G5 y true, G5 y false, G5 y false, G5 y false, G5 y false]

theorem factors_prod (y : Nat) (free : Bool) :
    (factors y free).prod = (∏ g : Fin 8, ∑ r : Fin 216, w6 y free g r) * ∏ j : Fin 9, ∑ r : Fin 125, w5 y j r := by
  cases free
  · simp [factors, Fin.prod_univ_succ, w6, w5, G6, G5, pen]
    ring
  · simp [factors, Fin.prod_univ_succ, w6, w5, G6, G6H, G5, pen]
    ring

/-! ### Digits of a sum of powers -/
theorem sum_pow_lt {α : Type} (s : Finset α) (g : α → Nat) (y k : Nat) (hy : 1 ≤ y) (hc : s.card < y)
    (hg : ∀ a ∈ s, g a < k) : (∑ a ∈ s, y ^ g a) < y ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : s = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => by have := hg a ha; omega
    subst this; simp
  · calc (∑ a ∈ s, y ^ g a) ≤ ∑ _a ∈ s, y ^ (k - 1) :=
          Finset.sum_le_sum fun a ha => Nat.pow_le_pow_right hy (by have := hg a ha; omega)
      _ = s.card * y ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ < y * y ^ (k - 1) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = y ^ k := by rw [← pow_succ']; congr 1; omega

theorem digit_of_sum {α : Type} (s : Finset α) (g : α → Nat) (y k : Nat) (hy : 2 ≤ y) (hc : s.card < y) :
    (∑ a ∈ s, y ^ g a) / y ^ k % y = (s.filter fun a => g a = k).card := by
  classical
  have hk1 : (∑ a ∈ s, y ^ g a) % y ^ (k + 1) = ∑ a ∈ s.filter (fun a => g a < k + 1), y ^ g a :=
    SigGolfResearch.Gate6.mod_pow_sum_generic (by omega) s g hc
  have hsplit : (∑ a ∈ s.filter (fun a => g a < k + 1), y ^ g a) =
      (∑ a ∈ s.filter (fun a => g a < k), y ^ g a) + (s.filter fun a => g a = k).card * y ^ k := by
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun a => g a < k + 1)) (fun a => g a < k),
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · apply Finset.sum_congr (Finset.filter_congr fun a _ => by omega) (fun _ _ => rfl)
    · rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr (Finset.filter_congr fun a _ => by omega)
      intro a ha
      simp only [Finset.mem_filter] at ha
      rw [ha.2]
  have hlt : (∑ a ∈ s.filter (fun a => g a < k), y ^ g a) < y ^ k :=
    sum_pow_lt _ g y k (by omega) ((Finset.card_filter_le _ _).trans_lt hc) fun a ha => (Finset.mem_filter.mp ha).2
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, hk1, hsplit, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-! ### Truncated product (zero counts below 8)
Generic in the modulus `m`; instantiated at `m = B ^ cutExp` (the kernel only ever evaluates `Nat.pow` with exponent
`cutExp < 2^24`). -/
def cutExp : Nat := 34808 * 8
def tmulM (m a b : Nat) : Nat := a * b % m
def tprodM (m : Nat) : List Nat → Nat
  | [] => 1 % m
  | a :: t => tmulM m a (tprodM m t)

theorem tprodM_eq (m : Nat) (L : List Nat) : tprodM m L = L.prod % m := by
  induction L with
  | nil => rfl
  | cons a t ih => rw [tprodM, tmulM, ih, List.prod_cons, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

def packedT (free : Bool) : Nat := tprodM (B ^ cutExp) (factors B free)
attribute [irreducible] packedT

theorem word_card_lt : Fintype.card R6Word < B := by rw [word_card, B]; norm_num

theorem digit_mod_pow (P b n k : Nat) (hk : k < n) : P % b ^ n / b ^ k % b = P / b ^ k % b := by
  have h : b ^ n = b ^ k * b ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self b (by omega : n - k ≠ 0))]

/-- Coefficient `k < 34808 * 8` of the truncated product counts the (free) words of statistic `k`. -/
theorem packedT_digit (free : Bool) (k : Nat) (hk : k < cutExp) :
    packedT free / B ^ k % B =
      (univ.filter fun w : R6Word => (free = true → isFree w) ∧ stat w = k).card := by
  classical
  have hsum : (factors B free).prod =
      ∑ w ∈ univ.filter (fun w : R6Word => free = true → isFree w), B ^ stat w := by
    rw [factors_prod, ← weighted_words, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro w _
    split_ifs with h1 h2 h2
    · exact absurd (h2 h1.1) h1.2
    · rfl
    · rfl
    · exact absurd ⟨Classical.byContradiction fun hf => h2 fun h => absurd h hf,
        fun hw => h2 fun _ => hw⟩ h1
  rw [packedT, tprodM_eq, digit_mod_pow _ _ _ _ hk, hsum,
    digit_of_sum _ _ _ _ (by norm_num [B]) ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_lt)),
    Finset.filter_filter]

/-- Count of the (free) model words of statistic `k` (irreducible: never unfolded by the elaborator). -/
def Sk (free : Bool) (k : Nat) (w : R6Word) : Prop := (free = true → isFree w) ∧ stat w = k
instance (free : Bool) (k : Nat) : DecidablePred (Sk free k) := fun w => by unfold Sk; infer_instance
def cnt (free : Bool) (k : Nat) : Nat := (univ.filter (Sk free k)).card
attribute [irreducible] cnt

theorem packedT_cnt (free : Bool) (k : Nat) (hk : k < cutExp) : packedT free / B ^ k % B = cnt free k := by
  rw [packedT_digit free k hk, cnt]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rfl

/-! ### Histogram windows
A credit `c` (no path bonus) of an accepted top word is `score + [checksum = 6] - 4`; the checksum digit is
`d = 153 - weight ∈ [0, 7]`, and the zero filter is `zeros + [d = 0] ≤ 7`. For each admissible `(d, z)` the
coefficients of the credits `16 ..< 147` form one window of 131 radix-`B` digits. -/
/-- Admissible (checksum digit, data zero count) pairs. -/
def pairsL : List (Nat × Nat) :=
  ((List.range 8).flatMap fun d => (List.range 8).map fun z => (d, z)).filter
    fun pr => decide (pr.2 + ind (pr.1 = 0) ≤ 7)
def pos (pr : Nat × Nat) (c : Nat) : Nat := 34808 * pr.2 + 152 * (153 - pr.1) + (c + 4 - ind (pr.1 = 6))
def winLen : Nat := 131
def window (p : Nat) (pr : Nat × Nat) : Nat := (p >>> (128 * pos pr 16)) % B ^ winLen
def windows (free : Bool) : List Nat := pairsL.map (window (packedT free))
attribute [irreducible] windows
def digitAt (i W : Nat) : Nat := (W >>> (128 * i)) % B
def histAt (ws : List Nat) (i : Nat) : Nat := (ws.map (digitAt i)).sum
def histW (h : List (Nat × Nat)) (c : Nat) : Nat := (h.map fun e => if e.1 = c then e.2 else 0).sum
def histCheck (counts : List (Nat × Nat)) (free : Bool) : Bool :=
  (List.range winLen).all fun i => histW counts (16 + i) == histAt (windows free) i

theorem pairsL_nodup : pairsL.Nodup := by decide
theorem mem_pairsL (d z : Nat) : (d, z) ∈ pairsL ↔ d < 8 ∧ z < 8 ∧ z + ind (d = 0) ≤ 7 := by
  simp only [pairsL, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl, rfl⟩, h⟩; exact ⟨ha, hb, h⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨d, h1, z, h2, rfl, rfl⟩, h3⟩

attribute [irreducible] pairsL

theorem shiftRight_B (p n : Nat) : p >>> (128 * n) = p / B ^ n := by
  rw [Nat.shiftRight_eq_div_pow, B, ← pow_mul]

theorem window_digit (p : Nat) (pr : Nat × Nat) (i : Nat) (hi : i < winLen) :
    (window p pr >>> (128 * i)) % B = p / B ^ (pos pr 16 + i) % B := by
  rw [window, shiftRight_B, shiftRight_B, digit_mod_pow _ _ _ _ hi, Nat.div_div_eq_div_mul, ← pow_add]

theorem pos_add (pr : Nat × Nat) (i : Nat) : pos pr (16 + i) = pos pr 16 + i := by
  unfold pos ind; split_ifs <;> omega

theorem ind_le (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split_ifs <;> omega
theorem ind_cases (p : Prop) [Decidable p] : (p ∧ ind p = 1) ∨ (¬p ∧ ind p = 0) := by
  by_cases h : p
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩
theorem ind_pos {p : Prop} [Decidable p] (h : p) : ind p = 1 := if_pos h
theorem ind_neg {p : Prop} [Decidable p] (h : ¬p) : ind p = 0 := if_neg h

theorem pos_lt (d z : Nat) (hpr : (d, z) ∈ pairsL) (c : Nat) (hc : c < 147) : pos (d, z) c < cutExp := by
  obtain ⟨h1, h2, h3⟩ := (mem_pairsL d z).mp hpr
  have hi := ind_le (d = 6)
  show 34808 * z + 152 * (153 - d) + (c + 4 - ind (d = 6)) < 34808 * 8
  omega

/-- The windows of the truncated product are the fibre counts. -/
theorem sum_map_map_congr {α β : Type} (l : List α) (f : α → β) (g : β → Nat) (h : α → Nat)
    (H : ∀ a ∈ l, g (f a) = h a) : ((l.map f).map g).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [H a (by simp), ih (fun b hb => H b (by simp [hb]))]

theorem histAt_eq (free : Bool) (i : Nat) (hi : i < winLen) :
    histAt (windows free) i = (pairsL.map fun pr => cnt free (pos pr (16 + i))).sum := by
  have hmap : ∀ pr ∈ pairsL, digitAt i (window (packedT free) pr) = cnt free (pos pr (16 + i)) := by
    intro pr hpr
    obtain ⟨d, z⟩ := pr
    rw [digitAt, window_digit _ _ _ hi, ← pos_add]
    exact packedT_cnt free _ (pos_lt d z hpr _ (by unfold winLen at hi; omega))
  unfold histAt
  rw [windows]
  exact sum_map_map_congr pairsL (window (packedT free)) (digitAt i) _ hmap

/-- The model predicate of an accepted top word of credit `c` (no path bonus). -/
def accepts (c : Nat) (w : R6Word) : Prop :=
  146 ≤ weight w ∧ weight w ≤ 153 ∧ zeros w + ind (weight w = 153) ≤ 7 ∧ score w + ind (weight w = 147) = c + 4
def Qc (free : Bool) (c : Nat) (w : R6Word) : Prop := (free = true → isFree w) ∧ accepts c w
instance (free : Bool) (c : Nat) : DecidablePred (Qc free c) := fun w => by unfold Qc accepts; infer_instance

theorem key_mem (c : Nat) (w : R6Word) (h : accepts c w) : (153 - weight w, zeros w) ∈ pairsL := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine (mem_pairsL _ _).mpr ⟨by omega, ?_, ?_⟩
  · have := ind_le (weight w = 153); omega
  · by_cases w3 : weight w = 153
    · rw [ind_pos w3] at h3; rw [ind_pos (by omega)]; omega
    · rw [ind_neg w3] at h3; rw [ind_neg (by omega)]; omega

theorem fiber_card {ι M : Type} [DecidableEq M] (f : ι → M) (s : Finset ι) (t : Finset M)
    (H : ∀ a ∈ s, f a ∈ t) : s.card = ∑ b ∈ t, (s.filter fun a => f a = b).card :=
  Finset.card_eq_sum_card_fiberwise fun a ha => H a ha

theorem fiber_card_filter {ι M : Type} [Fintype ι] [DecidableEq M] (Q : ι → Prop) [DecidablePred Q]
    (f : ι → M) (t : Finset M) (H : ∀ a, Q a → f a ∈ t) :
    (univ.filter Q).card = ∑ b ∈ t, ((univ.filter Q).filter fun a => f a = b).card :=
  fiber_card f _ t (fun a ha => H a (Finset.mem_filter.mp ha).2)

theorem fiber_eq (free : Bool) (c : Nat) (hc2 : c < 147) (d z : Nat) (hd8 : d < 8) (hz8 : z < 8)
    (hz7 : z + ind (d = 0) ≤ 7) (w : R6Word) :
    (Qc free c w ∧ (153 - weight w, zeros w) = (d, z)) ↔ Sk free (pos (d, z) c) w := by
  have hs := stat_eq w
  have hsc := score_le w
  have hw := weight_le w
  unfold Qc accepts Sk
  rw [Prod.mk.injEq]
  show _ ↔ _ ∧ stat w = 34808 * z + 152 * (153 - d) + (c + 4 - ind (d = 6))
  rcases ind_cases (d = 6) with ⟨i6, e6⟩ | ⟨i6, e6⟩ <;> rw [e6] <;>
  rcases ind_cases (d = 0) with ⟨i0, e0⟩ | ⟨i0, e0⟩ <;> rw [e0] at hz7 <;>
  rcases ind_cases (weight w = 153) with ⟨i3, e3⟩ | ⟨i3, e3⟩ <;> rw [e3] <;>
  rcases ind_cases (weight w = 147) with ⟨i7, e7⟩ | ⟨i7, e7⟩ <;> rw [e7] <;>
  · constructor
    · intro h
      have g1 := h.1.2.1
      have g2 := h.1.2.2.1
      have g3 := h.1.2.2.2.1
      have g4 := h.1.2.2.2.2
      have g5 := h.2.1
      have g6 := h.2.2
      exact ⟨h.1.1, by omega⟩
    · intro h
      have g := h.2
      have k1 : 146 ≤ weight w := by omega
      have k2 : weight w ≤ 153 := by omega
      have k3 : zeros w = z := by omega
      have k4 : 153 - weight w = d := by omega
      exact ⟨⟨h.1, k1, k2, by omega, by omega⟩, k4, k3⟩

theorem model_count (free : Bool) (c : Nat) (hc1 : 16 ≤ c) (hc2 : c < 147) :
    (univ.filter (Qc free c)).card = histAt (windows free) (c - 16) := by
  rw [histAt_eq free _ (by unfold winLen; omega), show 16 + (c - 16) = c by omega,
    ← List.sum_toFinset _ pairsL_nodup]
  rw [fiber_card_filter (Qc free c) (fun w => (153 - weight w, zeros w)) pairsL.toFinset
    (fun w hq => List.mem_toFinset.mpr (key_mem c w hq.2))]
  apply Finset.sum_congr rfl
  intro pr hpr
  obtain ⟨d, z⟩ := pr
  obtain ⟨hd8, hz8, hz7⟩ := (mem_pairsL d z).mp (List.mem_toFinset.mp hpr)
  rw [cnt, Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  exact fiber_eq free c hc2 d z hd8 hz8 hz7 w

theorem model_count_of_check (counts : List (Nat × Nat)) (free : Bool) (h : histCheck counts free = true)
    (c : Nat) (hc1 : 16 ≤ c) (hc2 : c < 147) :
    (univ.filter (Qc free c)).card = histW counts c := by
  rw [model_count free c hc1 hc2]
  unfold histCheck at h
  rw [List.all_eq_true] at h
  have := h (c - 16) (List.mem_range.mpr (by unfold winLen; omega))
  rw [beq_iff_eq, show 16 + (c - 16) = c by omega] at this
  exact this.symm

end SigGolfResearch.R6Top

/-! Campaign R6 + RC (COUNT): the exact R6 top credit histograms (no path bonus, credit `≥ 16`), checked against the
truncated generating polynomial (`gate1/packets/packet_R6_RC804_gate.json` topCounts / freeCount). -/
namespace SigGolfResearch.R6Top
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Accepted top words (digit sum 153, zeros `≤ 7`) by credit `c ≥ 16` (= reward - penalty, no path bonus). -/
def topCountsR6 : List (Nat × Nat) := [(16,1055271344712028874855706085773057),(17,1431394806358305750230964024093190),(18,1861506135052255195069337198448211),(19,2328484656249458266306294159987320),(20,2809138610239399808534757779883508),(21,3276407207471934437876940108361949),(22,3701735155703427852366406313458901),(23,4057862484747768159549307923449114),(24,4322092110172363288985628122431627),(25,4478751923451393617871909831580067),(26,4520151429684796184262791717352673),(27,4446961825731730493946411264607020),(28,4268181126992254959863896694154786),(29,3999637481938741765679436623441856),(30,3661472660490144701853606673822336),(31,3276090482502513604521961422630340),(32,2866369160165258647809727770262165),(33,2453443819452698133895417574388811),(34,2054998817984213566980917215766449),(35,1684760317999628240903539764312583),(36,1352321576840020319655743468599169),(37,1062984188160293156078186685592744),(38,818271915998022544148659406832867),(39,616912859391333751514497480432934),(40,455583927174679453199753566978220),(41,329551181599735296594557736186068),(42,233464020440045092389791955300422),(43,161978170890148741918676296625363),(44,110061559417835103637610951951692),(45,73221240280448003563458459763644),(46,47680267151996678284575347271559),(47,30390253711942584242731941526768),(48,18955419292811041276575590706563),(49,11563565316701781326479449596470),(50,6897626147611620658918397969706),(51,4023006107800223682613550993147),(52,2292861460758258255886317727083),(53,1276012229355874817129476351681),(54,693412856022607334096199748822),(55,367859929976729624484210775920),(56,190273117605399557424209043601),(57,95909357225700614649881806042),(58,47132901347992516628453450555),(59,22555036916332287294462707501),(60,10491664746009539916606393248),(61,4747406517902198866989173999),(62,2089928465206444829602118276),(63,892099079922439240661996562),(64,369010328827156239730752382),(65,148337101872770842060407280),(66,57751271898856420736361772),(67,21665351531003644560962873),(68,7874186850747501152454092),(69,2776161575026024626042350),(70,937447079657817004634114),(71,303977004148610475309902),(72,96055728772637751698091),(73,29033381372320812254372),(74,8266509764966057362421),(75,2301076620484508972859),(76,621486337837795199976),(77,152930213930829458893),(78,36169838131016641357),(79,8718383391814589025),(80,1852678442643925097),(81,351967753443054600),(82,75522776369235132),(83,14092008865395635),(84,1834903434896890),(85,325422019547555),(86,64627446275630),(87,6347752089343),(88,675675900928),(89,113331097845),(90,2863515564),(91,3271632),(92,149080260),(93,4009824)]
/-- The same restricted to words whose LOW half is not forced (r6 group 7 rank `≥ 128`). -/
def topFreeCountsR6 : List (Nat × Nat) := [(16,711765588436912263807281582392264),(17,962422143502962322924551010197446),(18,1247446577863424952728373061496812),(19,1554932591018351049079735973345263),(20,1869069477581705389171690162945178),(21,2171699666638903975306903404538291),(22,2443983078054210164570796074170739),(23,2668257238609935890486540651774089),(24,2830142771828857474206255361027173),(25,2920121128120808874019986096760430),(26,2934100799065429840199170560084639),(27,2873521486289056571855646807175438),(28,2745180116588259831000950427058930),(29,2560185755054247469631213703921776),(30,2332264057681356607286617127820265),(31,2076332934915653767348460691255680),(32,1807321253248693416229196108457036),(33,1538801467981760654512998186336035),(34,1281931737725886475591283580760590),(35,1045150654471849480929337409374736),(36,834145393255781604836870409662806),(37,651843420276549180501808724021275),(38,498775183310276569881335348128661),(39,373723388673608501051683272265807),(40,274242872931135972537141485240696),(41,197085963174918859412221930338835),(42,138689458302705729706286931020919),(43,95561245697938996319856265066595),(44,64471899335328131938138100904207),(45,42579210010465733074494136450593),(46,27518910917438074767569032353901),(47,17403896170883639472624329518997),(48,10768632362097810930699411064215),(49,6515330005076379996376011954141),(50,3853322909915740502596499793559),(51,2227602084484414447273799055036),(52,1258062347820008060895998948020),(53,693566667009050856596998259674),(54,373210941034165287583989546285),(55,195981039337420620923424531619),(56,100311713347620744625025374279),(57,50012159347427337162118246708),(58,24295981505199479920280567414),(59,11489394051860615554250512309),(60,5279085440100895355976701597),(61,2357684891768943942915387935),(62,1023801182374701302112764981),(63,430951638829795575609141598),(64,175628037093566366914053539),(65,69476990201439204072467834),(66,26612612268203060695378563),(67,9816744015501842781805301),(68,3501198591430152610529060),(69,1210461661308685779136138),(70,400975284372536011185176),(71,127211466220946593846422),(72,39227515560691661703838),(73,11593063019766963649025),(74,3221789693468841162608),(75,869430482427443072038),(76,228314562675943681265),(77,54788655347040440317),(78,12461705501051956829),(79,2886607090986084510),(80,598943138777784463),(81,109102128929602504),(82,22047538986692069),(83,4007239837584142),(84,499642414076127),(85,79776286232550),(86,15591198805889),(87,1546846157119),(88,139081231557),(89,21769679727),(90,578082960),(91,934752),(92,22190280),(93,763776)]

theorem histCheck_all : histCheck topCountsR6 false = true := by decide +kernel
theorem histCheck_free : histCheck topFreeCountsR6 true = true := by decide +kernel

end SigGolfResearch.R6Top
