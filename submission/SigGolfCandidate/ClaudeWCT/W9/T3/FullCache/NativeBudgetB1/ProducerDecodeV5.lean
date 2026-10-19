import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.Numerics.LowerZeroCreditCount
import SigGolfCandidate.ClaudeWCT.Numerics.TopCreditCount
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.CompletenessV5

/-! Campaign R6 + RC (COUNT): the R6 top digests and the counting model `R6Top.Word`.
`encode` packs the 17 ranks into the D1c word (r6 fields at 8g, r5 fields at 7q flipped, r6 group 7 at 119, spare
bit 127 zero); it is a bijection onto the words with `topRanksValid`. The decoded digit statistics (digit sum, zero
digits with the checksum, `wordCredit`, `savedCopies`, `topDispatchPenalty`) are the model statistics. -/
namespace SigGolfResearch.R6Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-! ### Bit-field packing -/
def packF : List (Nat × Nat) → Nat
  | [] => 0
  | p :: t => p.2 + 2 ^ p.1 * packF t
def offF : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | p :: t, k + 1 => p.1 + offF t k
def widthF : List (Nat × Nat) → Nat
  | [] => 0
  | p :: t => p.1 + widthF t

theorem packF_lt : ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.2 < 2 ^ p.1) → packF L < 2 ^ widthF L
  | [], _ => by simp [packF, widthF]
  | p :: t, h => by
    have hp := h p (by simp)
    have ht := packF_lt t (fun q hq => h q (by simp [hq]))
    simp only [packF, widthF, pow_add]
    have : packF t + 1 ≤ 2 ^ widthF t := ht
    nlinarith [Nat.one_le_two_pow (n := p.1)]

theorem packF_field : ∀ (L : List (Nat × Nat)) (k : Nat), (∀ p ∈ L, p.2 < 2 ^ p.1) → (hk : k < L.length) →
    packF L / 2 ^ offF L k % 2 ^ (L[k]'hk).1 = (L[k]'hk).2
  | [], k, _, hk => by simp at hk
  | p :: t, 0, h, _ => by
    have hp := h p (by simp)
    simp only [packF, offF, pow_zero, Nat.div_one, List.getElem_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  | p :: t, k + 1, h, hk => by
    have hp := h p (by simp)
    have ih := packF_field t k (fun q hq => h q (by simp [hq])) (by simpa using hk)
    simp only [packF, offF, List.getElem_cons_succ, pow_add, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hp, Nat.zero_add]
    exact ih

/-- The D1c fields of a model word (before the r5 flip). -/
def fields (w : R6Word) : List (Nat × Nat) :=
  [(8, (w.1 0).val + 40), (8, (w.1 1).val), (8, (w.1 2).val), (8, (w.1 3).val), (8, (w.1 4).val),
    (8, (w.1 5).val), (8, (w.1 6).val),
    (7, (w.2 0).val), (7, (w.2 1).val), (7, (w.2 2).val), (7, (w.2 3).val), (7, (w.2 4).val), (7, (w.2 5).val),
    (7, (w.2 6).val), (7, (w.2 7).val), (7, (w.2 8).val),
    (8, (w.1 7).val), (1, 0)]

theorem fields_bound (w : R6Word) : ∀ p ∈ fields w, p.2 < 2 ^ p.1 := by
  simp only [fields, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨by have := (w.1 0).isLt; norm_num; omega,
    by have := (w.1 1).isLt; norm_num; omega,
    by have := (w.1 2).isLt; norm_num; omega,
    by have := (w.1 3).isLt; norm_num; omega,
    by have := (w.1 4).isLt; norm_num; omega,
    by have := (w.1 5).isLt; norm_num; omega,
    by have := (w.1 6).isLt; norm_num; omega,
    by have := (w.2 0).isLt; norm_num; omega,
    by have := (w.2 1).isLt; norm_num; omega,
    by have := (w.2 2).isLt; norm_num; omega,
    by have := (w.2 3).isLt; norm_num; omega,
    by have := (w.2 4).isLt; norm_num; omega,
    by have := (w.2 5).isLt; norm_num; omega,
    by have := (w.2 6).isLt; norm_num; omega,
    by have := (w.2 7).isLt; norm_num; omega,
    by have := (w.2 8).isLt; norm_num; omega,
    by have := (w.1 7).isLt; norm_num; omega,
    by norm_num⟩

def code (w : R6Word) : Nat := packF (fields w)
theorem code_lt (w : R6Word) : code w < 2 ^ 128 := by
  have h := packF_lt _ (fields_bound w)
  have hw : widthF (fields w) = 128 := rfl
  rw [hw] at h
  exact h

/-- The digest of a model word. -/
def encode (w : R6Word) : Digest := topFlip (BitVec.ofNat 128 (code w))

theorem topCode_encode (w : R6Word) : topCode (encode w) = code w := by
  rw [encode, topCode_topFlip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (code_lt w)]

theorem code_field (w : R6Word) (k : Nat) (hk : k < 18) :
    code w / 2 ^ offF (fields w) k % 2 ^ ((fields w)[k]'(by simpa [fields] using hk)).1 =
      ((fields w)[k]'(by simpa [fields] using hk)).2 :=
  packF_field _ k (fields_bound w) _

theorem r6Raw_encode (w : R6Word) (g : Fin 8) :
    r6Raw (encode w) g.val = if g.val = 0 then (w.1 g).val + 40 else (w.1 g).val := by
  unfold r6Raw r6Shift
  rw [topCode_encode]
  fin_cases g
  · exact code_field w 0 (by decide)
  · exact code_field w 1 (by decide)
  · exact code_field w 2 (by decide)
  · exact code_field w 3 (by decide)
  · exact code_field w 4 (by decide)
  · exact code_field w 5 (by decide)
  · exact code_field w 6 (by decide)
  · exact code_field w 16 (by decide)

theorem r6Rank_encode (w : R6Word) (g : Fin 8) : r6Rank (encode w) g.val = (w.1 g).val := by
  by_cases h : g = 0
  · subst h
    have := r6Raw_encode w 0
    rw [Fin.val_zero, if_pos rfl] at this
    unfold r6Rank
    rw [Fin.val_zero, if_pos rfl, this, Nat.add_sub_cancel]
  · have hg : g.val ≠ 0 := fun e => h (Fin.ext e)
    have := r6Raw_encode w g
    rw [if_neg hg] at this
    unfold r6Rank
    rw [if_neg hg, this]

theorem r6Valid_encode (w : R6Word) (g : Fin 8) : r6Valid (encode w) g.val = true := by
  by_cases h : g = 0
  · subst h
    have := r6Raw_encode w 0
    rw [Fin.val_zero, if_pos rfl] at this
    unfold r6Valid
    rw [Fin.val_zero, if_pos rfl, this]
    simp
  · have hg : g.val ≠ 0 := fun e => h (Fin.ext e)
    have := r6Raw_encode w g
    rw [if_neg hg] at this
    unfold r6Valid
    rw [if_neg hg, this]
    simpa using (w.1 g).isLt

theorem r5Rank_encode (w : R6Word) (j : Fin 9) : r5Rank (encode w) (8 + j.val) = (w.2 j).val := by
  unfold r5Rank
  rw [topCode_encode]
  fin_cases j
  · exact code_field w 7 (by decide)
  · exact code_field w 8 (by decide)
  · exact code_field w 9 (by decide)
  · exact code_field w 10 (by decide)
  · exact code_field w 11 (by decide)
  · exact code_field w 12 (by decide)
  · exact code_field w 13 (by decide)
  · exact code_field w 14 (by decide)
  · exact code_field w 15 (by decide)

theorem topSpare_encode (w : R6Word) : topSpare (encode w) = 0 := by
  unfold topSpare
  rw [topCode_encode]
  exact code_field w 17 (by decide)

end SigGolfResearch.R6Top

namespace SigGolfResearch.R6Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

theorem topRanksValid_encode (w : R6Word) : topRanksValid (encode w) = true := by
  unfold topRanksValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1]
  refine ⟨⟨topSpare_encode w, fun g hg => r6Valid_encode w ⟨g, hg⟩⟩, fun q hq => ?_⟩
  have h := r5Rank_encode w ⟨q - 8, by omega⟩
  simp only [show 8 + (q - 8) = q by omega] at h
  rw [h]; exact (w.2 _).isLt

/-- The model word of a digest: its 17 ranks (reduced, so that `wordOf` is total). -/
def wordOf (v : Digest) : R6Word :=
  (fun g => ⟨r6Rank v g.val % 216, Nat.mod_lt _ (by decide)⟩,
    fun j => ⟨r5Rank v (8 + j.val) % 125, Nat.mod_lt _ (by decide)⟩)

theorem wordOf_encode (w : R6Word) : wordOf (encode w) = w := by
  refine Prod.ext (funext fun g => Fin.ext ?_) (funext fun j => Fin.ext ?_)
  · simp only [wordOf, r6Rank_encode]; exact Nat.mod_eq_of_lt (w.1 g).isLt
  · simp only [wordOf, r5Rank_encode]; exact Nat.mod_eq_of_lt (w.2 j).isLt

theorem dataDigits_encode_wordOf (v : Digest) (hv : topRanksValid v = true) :
    dataDigits 0 (encode (wordOf v)) = dataDigits 0 v := by
  obtain ⟨-, h6, h5⟩ := topRanksValid_parts hv
  unfold dataDigits
  apply List.map_congr_left
  intro i hi
  have hi : i < 51 := by simpa [dataCount] using hi
  unfold coreDigit
  simp only [if_true]
  split_ifs with h24
  · have hg : i / 3 < 8 := by omega
    have := r6Rank_encode (wordOf v) ⟨i / 3, hg⟩
    simp only [Fin.val_mk] at this
    rw [this]
    show r6Rank v (i / 3) % 216 / 6 ^ (i % 3) % 6 = _
    rw [Nat.mod_eq_of_lt (r6Rank_lt (h6 _ hg))]
  · have hq : i / 3 - 8 < 9 := by omega
    have := r5Rank_encode (wordOf v) ⟨i / 3 - 8, hq⟩
    simp only [Fin.val_mk, show 8 + (i / 3 - 8) = i / 3 by omega] at this
    rw [this]
    show r5Rank v (8 + (i / 3 - 8)) % 125 / 5 ^ (i % 3) % 5 = _
    rw [show 8 + (i / 3 - 8) = i / 3 by omega, Nat.mod_eq_of_lt (h5 _ (by omega) (by omega))]

theorem encode_wordOf (v : Digest) (hv : topRanksValid v = true) : encode (wordOf v) = v :=
  top_digest_injective (dataDigits_encode_wordOf v hv) (topRanksValid_encode _) hv

theorem card_bij_generic {α β : Type} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P]
    (Q : β → Prop) [DecidablePred Q] (e : β → α) (d : α → β) (h1 : ∀ b, Q b → P (e b))
    (h2 : ∀ a, P a → Q (d a)) (h3 : ∀ b, Q b → d (e b) = b) (h4 : ∀ a, P a → e (d a) = a) :
    (univ.filter P).card = (univ.filter Q).card := by
  symm
  apply Finset.card_bij' (fun b _ => e b) (fun a _ => d a)
  · intro b hb; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 b (Finset.mem_filter.mp hb).2⟩
  · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 a (Finset.mem_filter.mp ha).2⟩
  · intro b hb; exact h3 b (Finset.mem_filter.mp hb).2
  · intro a ha; exact h4 a (Finset.mem_filter.mp ha).2

/-- Counting valid digests is counting model words. -/
theorem card_encode (P : Digest → Prop) [DecidablePred P] (hP : ∀ v, P v → topRanksValid v = true) :
    (univ.filter P).card = (univ.filter fun w : R6Word => P (encode w)).card :=
  card_bij_generic P (fun w => P (encode w)) encode wordOf (fun _ h => h)
    (fun v h => by show P (encode (wordOf v)); rw [encode_wordOf v (hP v h)]; exact h)
    (fun w _ => wordOf_encode w) (fun v h => encode_wordOf v (hP v h))

/-! ### Digit statistics of `encode w` -/
theorem core_encode6 (w : R6Word) (g : Fin 8) (k : Nat) (hk : k < 3) :
    coreDigit 0 (encode w) (3 * g.val + k) = dg 6 (w.1 g).val k := by
  rw [top_core_r6 _ _ _ g.isLt hk, r6Rank_encode]; rfl

theorem core_encode5 (w : R6Word) (j : Fin 9) (k : Nat) (hk : k < 3) :
    coreDigit 0 (encode w) (3 * (8 + j.val) + k) = dg 5 (w.2 j).val k := by
  rw [top_core_r5 _ _ _ (by omega) (by omega) hk, r5Rank_encode]; rfl

theorem getD_digits (v : Digest) (chk i : Nat) :
    (dataDigits 0 v ++ [chk]).getD i 0 = if i < 51 then coreDigit 0 v i else if i = 51 then chk else 0 := by
  have hl : (dataDigits 0 v).length = 51 := by simp [dataDigits, dataCount]
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by omega)]
    simp [dataDigits, dataCount, List.getD_eq_getElem?_getD, h1]
  · subst h2; rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hl]
  · exact List.getD_eq_default _ _ (by simp [hl]; omega)

theorem filter_range_length (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ range n, ind (p i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h, ind]

theorem list_sum_range_map (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_blocks (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ range (3 * n), f i = ∑ g ∈ range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

/-- A chain sum over the 52 top chains splits into the 8 r6 triples, the 9 r5 triples and the checksum. -/
theorem sum_52 (f : Nat → Nat) :
    ∑ i ∈ range 52, f i = (∑ g : Fin 8, (f (3 * g.val) + f (3 * g.val + 1) + f (3 * g.val + 2))) +
      (∑ j : Fin 9, (f (3 * (8 + j.val)) + f (3 * (8 + j.val) + 1) + f (3 * (8 + j.val) + 2))) + f 51 := by
  rw [Finset.sum_range_succ, show 51 = 3 * 17 by rfl, sum_blocks, show 17 = 8 + 9 by rfl, Finset.sum_range_add,
    Finset.sum_range, Finset.sum_range]

theorem sum_51 (f : Nat → Nat) :
    ∑ i ∈ range 51, f i = (∑ g : Fin 8, (f (3 * g.val) + f (3 * g.val + 1) + f (3 * g.val + 2))) +
      (∑ j : Fin 9, (f (3 * (8 + j.val)) + f (3 * (8 + j.val) + 1) + f (3 * (8 + j.val) + 2))) := by
  rw [show 51 = 3 * 17 by rfl, sum_blocks, show 17 = 8 + 9 by rfl, Finset.sum_range_add,
    Finset.sum_range, Finset.sum_range]

end SigGolfResearch.R6Top

namespace SigGolfResearch.R6Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary ClaudeWCT.WCT9
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

theorem ind_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : ind p = ind q := by
  unfold ind; by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-! Digits of `encode w` followed by a checksum digit. -/
theorem getD6 (w : R6Word) (chk : Nat) (g : Fin 8) (k : Nat) (hk : k < 3) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + k) 0 = dg 6 (w.1 g).val k := by
  rw [getD_digits, if_pos (by omega), core_encode6 w g k hk]
theorem getD5 (w : R6Word) (chk : Nat) (j : Fin 9) (k : Nat) (hk : k < 3) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (8 + j.val) + k) 0 = dg 5 (w.2 j).val k := by
  rw [getD_digits, if_pos (by omega), core_encode5 w j k hk]
theorem getD51 (w : R6Word) (chk : Nat) : (dataDigits 0 (encode w) ++ [chk]).getD 51 0 = chk := by
  rw [getD_digits, if_neg (by omega), if_pos rfl]
theorem max6 (g : Fin 8) (k : Nat) (hk : k < 3) : maxDigit 0 (3 * g.val + k) = 5 := by
  have := g.isLt; unfold maxDigit; simp only [if_true]; rw [if_pos (by omega)]
theorem max5 (j : Fin 9) (k : Nat) (hk : k < 3) : maxDigit 0 (3 * (8 + j.val) + k) = 4 := by
  have := j.isLt; unfold maxDigit; simp only [if_true]; rw [if_neg (by omega), if_pos (by omega)]

/-- The three digits of block `g` (r6) and `j` (r5) of `encode w`, in the shape the chain sums use. -/
theorem blk6 (w : R6Word) (chk : Nat) (g : Fin 8) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val) 0 = dg 6 (w.1 g).val 0 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 1) 0 = dg 6 (w.1 g).val 1 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 2) 0 = dg 6 (w.1 g).val 2 ∧
    maxDigit 0 (3 * g.val) = 5 ∧ maxDigit 0 (3 * g.val + 1) = 5 ∧ maxDigit 0 (3 * g.val + 2) = 5 :=
  ⟨by simpa using getD6 w chk g 0 (by decide), getD6 w chk g 1 (by decide), getD6 w chk g 2 (by decide),
    by simpa using max6 g 0 (by decide), max6 g 1 (by decide), max6 g 2 (by decide)⟩
theorem blk5 (w : R6Word) (chk : Nat) (j : Fin 9) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (8 + j.val)) 0 = dg 5 (w.2 j).val 0 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (8 + j.val) + 1) 0 = dg 5 (w.2 j).val 1 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (8 + j.val) + 2) 0 = dg 5 (w.2 j).val 2 ∧
    maxDigit 0 (3 * (8 + j.val)) = 4 ∧ maxDigit 0 (3 * (8 + j.val) + 1) = 4 ∧ maxDigit 0 (3 * (8 + j.val) + 2) = 4 :=
  ⟨by simpa using getD5 w chk j 0 (by decide), getD5 w chk j 1 (by decide), getD5 w chk j 2 (by decide),
    by simpa using max5 j 0 (by decide), max5 j 1 (by decide), max5 j 2 (by decide)⟩

def credits (w : R6Word) : Nat := (∑ g : Fin 8, tcredit 6 (w.1 g).val) + ∑ j : Fin 9, tcredit 5 (w.2 j).val
def copies (w : R6Word) : Nat :=
  (∑ g : Fin 8, tcopies 6 (decide (g.val = 0)) (w.1 g).val) + ∑ j : Fin 9, tcopies 5 false (w.2 j).val
def penalty (w : R6Word) : Nat := ∑ j : Fin 9, ind (pen j = true ∧ tsum 5 (w.2 j).val < 3)

theorem wordCredit_encode (w : R6Word) (chk : Nat) :
    wordCredit 0 (dataDigits 0 (encode w) ++ [chk]) = credits w + ind (chk + 1 = 7) := by
  unfold wordCredit
  rw [show chainCount 0 = 52 from rfl, filter_range_length, sum_52, getD51, show maxDigit 0 51 = 7 from rfl]
  unfold credits
  congr 2
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    rw [a0, a1, a2, m0, m1, m2]; rfl
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    rw [a0, a1, a2, m0, m1, m2]; rfl

theorem savedCopies_encode (w : R6Word) (chk : Nat) :
    savedCopies 0 (dataDigits 0 (encode w) ++ [chk]) = copies w := by
  unfold savedCopies
  rw [show chainCount 0 = 52 from rfl, filter_range_length, sum_52]
  have h51 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 51) = 0 := by
    apply ind_neg; unfold safeZeroCopy; omega
  rw [h51, Nat.add_zero]
  unfold copies
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · exact ⟨by simp; omega, h1⟩
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl (by simp at h1; omega)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * g.val + 1 - 1 = 3 * g.val by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * g.val + 2 - 1 = 3 * g.val + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, h2⟩)⟩
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · omega
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, _⟩; exact absurd h1 (by simp)
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * (8 + j.val) + 1 - 1 = 3 * (8 + j.val) by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * (8 + j.val) + 2 - 1 = 3 * (8 + j.val) + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, h2⟩)⟩

theorem penalty_encode (w : R6Word) (chk : Nat) :
    topDispatchPenalty (dataDigits 0 (encode w) ++ [chk]) = penalty w := by
  unfold topDispatchPenalty
  rw [filter_range_length, show 17 = 8 + 9 by rfl, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  have h0 : (∑ g : Fin 8, ind ((g.val = 8 ∨ g.val = 10 ∨ g.val = 11 ∨ g.val = 12) ∧
      (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val) 0 + (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 1) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 2) 0 < 3)) = 0 := by
    apply Finset.sum_eq_zero; intro g _; apply ind_neg; have := g.isLt; omega
  rw [h0, Nat.zero_add]
  unfold penalty
  apply Finset.sum_congr rfl; intro j _
  obtain ⟨a0, a1, a2, -, -, -⟩ := blk5 w chk j
  rw [a0, a1, a2]
  apply ind_congr
  unfold pen tsum
  have := j.isLt
  simp only [decide_eq_true_eq]
  omega

theorem sum_encode (w : R6Word) : (dataDigits 0 (encode w)).sum = weight w := by
  unfold dataDigits
  rw [show dataCount 0 = 51 from rfl, list_sum_range_map, sum_51]
  unfold weight
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    rw [show 3 * g.val = 3 * g.val + 0 by rfl, core_encode6 w g 0 (by decide), core_encode6 w g 1 (by decide),
      core_encode6 w g 2 (by decide)]; rfl
  · apply Finset.sum_congr rfl; intro j _
    rw [show 3 * (8 + j.val) = 3 * (8 + j.val) + 0 by rfl, core_encode5 w j 0 (by decide),
      core_encode5 w j 1 (by decide), core_encode5 w j 2 (by decide)]; rfl

theorem zeros_encode (w : R6Word) (chk : Nat) :
    ((dataDigits 0 (encode w) ++ [chk]).filter (· = 0)).length = zeros w + ind (chk = 0) := by
  rw [List.filter_append, List.length_append]
  congr 1
  · unfold dataDigits
    rw [show dataCount 0 = 51 from rfl, List.filter_map, List.length_map]
    rw [show ((List.range 51).filter ((fun x => decide (x = 0)) ∘ coreDigit 0 (encode w))) =
      (List.range 51).filter (fun i => decide (coreDigit 0 (encode w) i = 0)) from rfl, filter_range_length, sum_51]
    unfold zeros
    congr 1
    · apply Finset.sum_congr rfl; intro g _
      rw [show 3 * g.val = 3 * g.val + 0 by rfl, core_encode6 w g 0 (by decide), core_encode6 w g 1 (by decide),
        core_encode6 w g 2 (by decide)]; rfl
    · apply Finset.sum_congr rfl; intro j _
      rw [show 3 * (8 + j.val) = 3 * (8 + j.val) + 0 by rfl, core_encode5 w j 0 (by decide),
        core_encode5 w j 1 (by decide), core_encode5 w j 2 (by decide)]; rfl
  · unfold ind; by_cases h : chk = 0 <;> simp [h]

theorem score_penalty (w : R6Word) : score w + penalty w = credits w + 4 * copies w + 4 := by
  have hb (j : Fin 9) : (if pen j = true then ind (3 ≤ tsum 5 (w.2 j).val) else 0) +
      ind (pen j = true ∧ tsum 5 (w.2 j).val < 3) = ind (pen j = true) := by
    unfold ind; by_cases hp : pen j = true <;> by_cases ht : 3 ≤ tsum 5 (w.2 j).val <;> simp [hp, ht] <;> omega
  have h4 : (∑ j : Fin 9, ind (pen j = true)) = 4 := by decide
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 9))) => hb j)
  rw [Finset.sum_add_distrib, h4] at hs
  unfold score credits copies penalty tscore
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Finset.sum_const_zero] at hs ⊢
  omega

end SigGolfResearch.R6Top

/-! Campaign R6 + RC (COUNT): exact counts of the canonical top producer (no path bonus) by credit. -/
namespace SigGolfResearch.R6Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary ClaudeWCT.WCT9
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-- The canonical top producer accepts `v` at floor 0 without the path bonus, with credit `c`. -/
def acc (c : Nat) (v : Digest) : Prop :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => False
  | some ds => CanonicalPolicy.credit 0 false ds = c
instance (c : Nat) : DecidablePred (acc c) := fun v => by
  unfold acc; split <;> infer_instance

theorem acc_iff (c : Nat) (v : Digest) :
    acc c v ↔ ∃ ds, CanonicalPolicy.producerDecodeAt 0 0 false v = some ds ∧ CanonicalPolicy.credit 0 false ds = c := by
  unfold acc; cases CanonicalPolicy.producerDecodeAt 0 0 false v <;> simp

theorem decode_canonical_top (v : Digest) : CanonicalPolicy.decode 0 v = decode 0 v := by
  simp [CanonicalPolicy.decode, CanonicalPolicy.normalLayer]

theorem acc_valid (c : Nat) (v : Digest) (h : acc c v) : topRanksValid v = true := by
  obtain ⟨ds, hd, -⟩ := (acc_iff c v).mp h
  have hs := (CanonicalPolicy.producerDecodeAt_spec hd).1
  rw [decode_canonical_top] at hs
  exact (decode_top_some hs).2.1

theorem acc_encode_iff (c : Nat) (w : R6Word) : acc c (encode w) ↔ accepts c w := by
  rw [acc_iff]
  have hv := topRanksValid_encode w
  have hS := sum_encode w
  unfold accepts
  by_cases hdec : weight w ≤ 153 ∧ 153 - weight w < 8
  · have hd := decode_top_of (encode w).isLt hv (by rw [hS]; exact hdec.1) (by rw [hS]; exact hdec.2)
    rw [show target 0 = 153 from rfl, hS] at hd
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd]
    simp only
    set chk := 153 - weight w with hchk
    have hz := zeros_encode w chk
    have hc := wordCredit_encode w chk
    have hp := penalty_encode w chk
    have hcp := savedCopies_encode w chk
    have hsp := score_penalty w
    have hpl : penalty w ≤ 4 := by
      unfold penalty
      calc (∑ j : Fin 9, ind (pen j = true ∧ tsum 5 (w.2 j).val < 3)) ≤ ∑ j : Fin 9, ind (pen j = true) :=
            Finset.sum_le_sum fun j _ => by unfold ind; split_ifs <;> simp_all
        _ = 4 := by decide
    have e1 : ind (chk + 1 = 7) = ind (weight w = 147) := ind_congr (by omega)
    have e2 : ind (chk = 0) = ind (weight w = 153) := ind_congr (by omega)
    have i1 := ind_le (weight w = 147)
    simp only [CanonicalPolicy.pathReward, CanonicalPolicy.reward, CanonicalPolicy.pathBonus_false, Nat.add_zero,
      CanonicalPolicy.credit, dispatchPenalty, if_true, producerZeroBound, producerZeroMax, producerRankBound,
      true_or, and_true]
    rw [hz, hc, hp, hcp, e1, e2]
    constructor
    · rintro ⟨ds, hds, hcr⟩
      split_ifs at hds with hcond
      · cases hds
        refine ⟨by omega, hdec.1, hcond.2, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨_, if_pos ⟨by omega, h3⟩, by omega⟩
  · have hd : decode 0 (encode w) = none := by
      cases h : decode 0 (encode w) with
      | none => rfl
      | some ds =>
        obtain ⟨-, -, ⟨h1, h2⟩, -⟩ := decode_top_some h
        rw [hS] at h1 h2
        exact absurd ⟨h1, h2⟩ hdec
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd]
    simp only [reduceCtorEq, false_and, exists_false, false_iff, not_and]
    intro h1 h2
    exact absurd ⟨h2, by omega⟩ hdec

theorem high_bits (X r : Nat) (h7 : X / 2 ^ 119 % 256 = r) (hs : X / 2 ^ 127 % 2 = 0) (hlt : X < 2 ^ 128) :
    X < 2 ^ 126 ↔ r < 128 := by
  simp only [Nat.reducePow] at *
  omega

theorem blocked_encode (w : R6Word) : TopChoice.blocked (encode w) ↔ ¬ isFree w := by
  have h7 : r6Raw (encode w) 7 = (w.1 7).val := by
    have := r6Raw_encode w 7
    rw [if_neg (by decide)] at this
    exact this
  unfold r6Raw r6Shift at h7
  rw [if_pos rfl] at h7
  have hs := topSpare_encode w
  unfold topSpare at hs
  have hlt : topCode (encode w) < 2 ^ 128 := by rw [topCode_encode]; exact code_lt w
  have key := high_bits _ _ h7 hs hlt
  unfold TopChoice.blocked isFree
  rw [← topCode_lt_iff _ 126 (by decide), key]
  omega

/-- Exact count of the top words of credit `c` accepted by the canonical producer (no path bonus). -/
theorem card_acc (c : Nat) (hc1 : 16 ≤ c) (hc2 : c < 147) :
    (univ.filter (acc c)).card = histW topCountsR6 c := by
  rw [card_encode (acc c) (acc_valid c), ← model_count_of_check topCountsR6 false histCheck_all c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff]
  unfold Qc
  simp

/-- Exact count of those whose LOW half is not forced. -/
theorem card_acc_free (c : Nat) (hc1 : 16 ≤ c) (hc2 : c < 147) :
    (univ.filter fun v => acc c v ∧ ¬ TopChoice.blocked v).card = histW topFreeCountsR6 c := by
  rw [card_encode (fun v => acc c v ∧ ¬ TopChoice.blocked v) (fun v h => acc_valid c v h.1),
    ← model_count_of_check topFreeCountsR6 true histCheck_free c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff, blocked_encode]
  unfold Qc
  simp only [not_not, forall_const]
  exact And.comm

end SigGolfResearch.R6Top

namespace SigGolfResearch.R6Top
open Finset SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option linter.constructorNameAsVariable false

theorem acc_le (c : Nat) (v : Digest) (h : acc c v) : c ≤ 146 := by
  have hv := acc_valid c v h
  rw [← encode_wordOf v hv] at h
  have ha := (acc_encode_iff c _).mp h
  have hs := score_le (wordOf v)
  have hi := ind_le (weight (wordOf v) = 147)
  unfold accepts at ha
  omega

theorem histW_eq_zero (l : List (Nat × Nat)) (c : Nat) (h : ∀ e ∈ l, e.1 ≠ c) : histW l c = 0 := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    unfold histW at ih ⊢
    rw [List.map_cons, List.sum_cons, if_neg (h e (by simp)), ih (fun e' he' => h e' (by simp [he']))]

theorem topCountsR6_lt : ∀ e ∈ topCountsR6, e.1 < 94 := by decide
theorem topFreeCountsR6_lt : ∀ e ∈ topFreeCountsR6, e.1 < 94 := by decide

/-- Campaign R6 + RC: the LOW-good (credit `≥ 16` without the bonus, i.e. top floor 19 with the LOW bonus 3) top words
whose LOW half is not forced. Equals the packet's `freeCount`. -/
def freeCountR6 : Nat := (topFreeCountsR6.map Prod.snd).sum
theorem freeCountR6_value : freeCountR6 = 43816752562692919204629932487685850 := by decide
theorem freeCountR6_hist : ((List.range' 16 131).map (histW topFreeCountsR6)).sum = freeCountR6 := by decide +kernel

end SigGolfResearch.R6Top


namespace SigGolfResearch.LowerEffectiveCounting
open scoped BigOperators
open Finset NonbinaryTop.Codec NonbinaryTop.Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
set_option Elab.async false
set_option linter.constructorNameAsVariable false

def rank (d : Triple8) : Nat := (d 0).val + 8 * (d 1).val + 64 * (d 2).val
def rankFloor (q : Fin 14) : Nat := if q.val = 1 ∨ q.val = 8 then 5 else 3
abbrev Atom (k : Nat) := {d : Triple8 // k ≤ rank d}
abbrev «Word» := (∀ q : Fin 14, Atom (rankFloor q)) × Fin 8

def copies (first : Bool) (d : Triple8) : Nat :=
  (if first && decide ((d 0).val = 7) then 1 else 0) +
  (if (d 1).val = 7 ∧ (first = true ∨ (d 0).val = 7) then 1 else 0) +
  (if (d 1).val = 7 ∧ (d 2).val = 7 then 1 else 0)
def score3 (first : Bool) (d : Triple8) : Nat :=
  NonbinaryTop.CreditCounting.credit8 d + 4 * copies first d
def zeros3 (d : Triple8) : Nat := ∑ i : Fin 3, if (d i).val = 0 then 1 else 0
def weight (w : «Word») : Nat := (∑ q : Fin 14, tripleSum8 (w.1 q).val) + w.2.val
def score (w : «Word») : Nat :=
  (∑ q : Fin 14, score3 (decide (q.val = 0)) (w.1 q).val) + if w.2.val = 6 then 1 else 0
def zeros (w : «Word») : Nat :=
  (∑ q : Fin 14, zeros3 (w.1 q).val) + if w.2.val = 0 then 1 else 0
def stat3 (first : Bool) (d : Triple8) : Nat :=
  65536 * zeros3 d + 128 * tripleSum8 d + score3 first d
def stat1 (d : Fin 8) : Nat :=
  65536 * (if d.val = 0 then 1 else 0) + 128 * d.val + if d.val = 6 then 1 else 0
def stat (w : «Word») : Nat :=
  (∑ q : Fin 14, stat3 (decide (q.val = 0)) (w.1 q).val) + stat1 w.2

theorem stat_eq (w : «Word») : stat w = 65536 * zeros w + 128 * weight w + score w := by
  simp only [stat, stat3, stat1, zeros, weight, score, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem score3_le (first : Bool) (d : Triple8) :
    score3 first d ≤ 8 + if first then 4 else 0 := by
  revert first d
  decide +kernel

theorem score_le (w : «Word») : score w ≤ 117 := by
  have hs : (∑ q : Fin 14, score3 (decide (q.val = 0)) (w.1 q).val) ≤
      ∑ q : Fin 14, (8 + if q.val = 0 then 4 else 0) := by
    apply Finset.sum_le_sum
    intro q _
    simpa using score3_le (decide (q.val = 0)) (w.1 q).val
  have hb : (∑ q : Fin 14, (8 + if q.val = 0 then 4 else 0)) = 116 := by decide +kernel
  rw [hb] at hs
  unfold score
  split_ifs <;> omega

theorem weight_le (w : «Word») : weight w ≤ 301 := by
  have ht (d : Triple8) : tripleSum8 d ≤ 21 := by
    unfold tripleSum8
    have h : (∑ i : Fin 3, (d i).val) ≤ ∑ _i : Fin 3, 7 :=
      sum_le_sum fun i _ => by have := (d i).isLt; omega
    simpa using h
  have hs : (∑ q : Fin 14, tripleSum8 (w.1 q).val) ≤ ∑ _q : Fin 14, 21 :=
    sum_le_sum fun q _ => ht (w.1 q).val
  have hd := w.2.isLt
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hs
  unfold weight
  omega

def radix : Nat := 2^132

theorem word_card_small : Fintype.card «Word» < radix - 1 := by
  let forget : «Word» → (Fin 14 → Triple8) × Fin 8 := fun w => (fun q => (w.1 q).val, w.2)
  have hi : Function.Injective forget := by
    intro a b hab
    apply Prod.ext
    · funext q
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst hab) q
    · change (forget a).2 = (forget b).2
      exact congrArg Prod.snd hab
  have hc := Fintype.card_le_of_injective forget hi
  norm_num [Fintype.card_prod, Fintype.card_fun, radix, Triple8] at hc ⊢
  omega

def group (y : Nat) (first : Bool) (k : Nat) : Nat :=
  ∑ d : Atom k, y ^ stat3 first d.val
def tail (y : Nat) : Nat := ∑ d : Fin 8, y ^ stat1 d

theorem weighted_words (y : Nat) :
    (∑ w : «Word», y ^ stat w) =
      group y true 3 * group y false 5 ^ 2 * group y false 3 ^ 11 * tail y := by
  rw [Fintype.sum_prod_type]
  simp only [stat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : ∀ q : Fin 14, Atom (rankFloor q),
      y ^ (∑ q : Fin 14, stat3 (decide (q.val = 0)) (f q).val)) =
      ∏ q : Fin 14, group y (decide (q.val = 0)) (rankFloor q) := by
    simpa only [group, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 14) (d : Atom (rankFloor q)) =>
        y ^ stat3 (decide (q.val = 0)) d.val).symm
  rw [h]
  change (∏ q : Fin 14, group y (decide (q.val = 0)) (rankFloor q)) * tail y = _
  norm_num [Fin.prod_univ_succ, rankFloor]
  ring_nf
  simp

def packedAt (y : Nat) : Nat :=
  group y true 3 * group y false 5 ^ 2 * group y false 3 ^ 11 * tail y

theorem weighted_words_at (y : Nat) :
    (∑ w : «Word», y^stat w) = packedAt y := weighted_words y

def packed : Nat := packedAt radix

theorem truncated_card (cut : Nat) (hc : 0 < cut) :
    (univ.filter fun w : «Word» => stat w < cut).card =
      (packed % radix ^ cut) % (radix - 1) := by
  classical
  unfold packed
  rw [← weighted_words_at radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ stat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

def windowCount (T f z : Nat) : Nat :=
  (packed % radix ^ (65536*z+128*T+128)) % (radix - 1) -
  (packed % radix ^ (65536*z+128*T+f)) % (radix - 1)
def count (T f : Nat) : Nat := ∑ z ∈ range 6, windowCount T f z

theorem window_card (T f z : Nat) (hT : 0 < T ∧ T ≤ 301) (hf : f ≤ 128) :
    (univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w = z).card =
      windowCount T f z := by
  classical
  have heq : (univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w = z) =
      (univ.filter fun w : «Word» => stat w < 65536*z+128*T+128) \
        (univ.filter fun w : «Word» => stat w < 65536*z+128*T+f) := by
    ext w
    have hc := score_le w
    have hw := weight_le w
    have he := stat_eq w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    omega
  rw [heq, card_sdiff_of_subset]
  · exact congrArg₂ Nat.sub (truncated_card _ (by omega)) (truncated_card _ (by omega))
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega

theorem card_model (T f : Nat) (hT : 0 < T ∧ T ≤ 301) (hf : f ≤ 128) :
    (univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w ≤ 5).card = count T f := by
  classical
  rw [card_eq_sum_card_fiberwise (f := zeros)
      (s := univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w ≤ 5)
      (t := range 6) (by
    intro w hw
    change w ∈ (univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w ≤ 5) at hw
    change zeros w ∈ range 6
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [mem_range]
    omega)]
  unfold count
  apply sum_congr rfl
  intro z hz
  have he : ((univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w ≤ 5).filter
      fun w => zeros w = z) = (univ.filter fun w : «Word» => weight w = T ∧ f ≤ score w ∧ zeros w = z) := by
    ext w
    simp only [mem_filter, mem_univ, true_and]
    have := mem_range.mp hz
    omega
  rw [he, window_card T f z hT hf]

end SigGolfResearch.LowerEffectiveCounting

namespace SigGolfResearch.LowerEffectiveCounting
open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option Elab.async false

def count201 : Nat := 54408112790925688753987891000775297
def count202 : Nat := 44444210514614632453013305786840214

theorem exact_201 : count 201 10 = count201 := by decide +kernel
theorem card_201 :
    (univ.filter fun w : «Word» => weight w = 201 ∧ 10 ≤ score w ∧ zeros w ≤ 5).card = count201 :=
  (card_model 201 10 (by decide) (by decide)).trans exact_201

theorem exact_202 : count 202 9 = count202 := by decide +kernel
theorem card_202 :
    (univ.filter fun w : «Word» => weight w = 202 ∧ 9 ≤ score w ∧ zeros w ≤ 5).card = count202 :=
  (card_model 202 9 (by decide) (by decide)).trans exact_202

theorem count201_rate : 4 * 2^128 ≤ 7 * count201 * 8192 := by decide +kernel
theorem count202_rate : 4 * 2^128 ≤ 7 * count202 * 8192 := by decide +kernel

end SigGolfResearch.LowerEffectiveCounting

namespace ClaudeWCT.W9.T3.ProducerV5
open OracleComp OracleSpec ENNReal Finset
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfResearch.NonbinaryTop
open ClaudeWCT.WCT9 (producerDecode producerFloor wordCredit searchLimit producerZeroBound producerRankBound)
open ClaudeWCT.W9.T3.BaseAudit
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
def producerEncodingDecode (lay : Layer) (answer : HashOutput) : Option (List Nat) :=
  producerDecode lay (ClaudeWCT.WCT9.encodingAnswer lay answer)
theorem filter_range_getD (l : List ℕ) :
    ((List.range l.length).filter fun i => l.getD i 0 + 1 = 7).length = l.count 6 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hf : ((fun i => decide ((a :: l).getD i 0 + 1 = 7)) ∘ Nat.succ) = fun i => decide (l.getD i 0 + 1 = 7) := by
      funext i; simp
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, List.count_cons, hf]
    by_cases ha : a = 6
    · subst ha
      rw [if_pos (by simp), List.length_cons, List.length_map, ih]
      simp
    · rw [if_neg (by simp; omega), List.length_map, ih]
      simp [ha]
theorem dataDigits_lower (lay : Layer) (hl : lay ≠ 0) (v : Digest) :
    dataDigits lay v = ClaudeWCT.Numerics.LowerCredit.lowerDigitsS1 v.toNat := by
  simp [dataDigits, dataCount, hl, coreDigit, lowerShift, ClaudeWCT.Numerics.LowerCredit.lowerDigitsS1,
    ClaudeWCT.Numerics.LowerCredit.shiftS1]
theorem wordCredit_lower (lay : Layer) (hl : lay ≠ 0) (ds : List ℕ) (hlen : ds.length = 43) :
    wordCredit lay ds = ds.count 6 := by
  have hc : chainCount lay = 43 := by fin_cases lay <;> simp_all [chainCount]
  have hm : ∀ i, maxDigit lay i = 7 := by intro i; simp [maxDigit, hl]
  unfold wordCredit
  rw [hc, ← hlen]
  simp only [hm]
  exact filter_range_getD ds
theorem filter_zero_count (l : List ℕ) : (l.filter (· = 0)).length = l.count 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : a = 0
      · subst a; simp [ih]
      · simp [ha, ih]
theorem lowerWord_eq_ofS1 (v : Digest) : lowerWord v = ClaudeWCT.Numerics.LowerCredit.ofS1 v.toNat := by
  unfold lowerWord ClaudeWCT.Numerics.LowerCredit.ofS1
  ring
def lowerProducerDigits (lay : Layer) (n : Nat) : List Nat :=
  let ds := ClaudeWCT.Numerics.LowerCredit.lowerDigitsS1 n
  ds ++ [target lay - ds.sum]

def lowerProducerAccept (lay : Layer) (n : Nat) : Prop :=
  ClaudeWCT.Numerics.LowerRank.LowerAcceptS1Rank (target lay) 0 n ∧
    producerFloor lay ≤ (lowerProducerDigits lay n).count 6 +
      4 * ClaudeWCT.WCT9.savedCopies lay (lowerProducerDigits lay n)

instance (lay : Layer) (n : Nat) : Decidable (lowerProducerAccept lay n) := by
  unfold lowerProducerAccept; infer_instance

theorem producerDecode_lower_isSome_iff (lay : Layer) (hl : lay ≠ 0) (v : Digest) :
    (producerDecode lay v).isSome ↔ lowerProducerAccept lay v.toNat := by
  set L := ClaudeWCT.Numerics.LowerCredit.lowerDigitsS1 v.toNat with hL
  have hlen : (L ++ [target lay - L.sum]).length = 43 := by
    simp [hL, ClaudeWCT.Numerics.LowerCredit.lowerDigitsS1]
  have hdec : decode lay v = if ClaudeWCT.Numerics.LowerCredit.SpareS1 v.toNat ∧ L.sum ≤ target lay ∧
      target lay - L.sum < 8 then some (L ++ [target lay - L.sum]) else none := by
    have hb : ¬ 2 ^ encodedBits lay ≤ v.toNat := by
      simp only [encodedBits, not_le]; exact v.isLt
    simp only [decode, hb, if_false, hl, dataDigits_lower lay hl, hL]
    rfl
  unfold producerDecode lowerProducerAccept lowerProducerDigits
    ClaudeWCT.Numerics.LowerRank.LowerAcceptS1Rank
    ClaudeWCT.Numerics.LowerZeroCredit.LowerAcceptS1Z
    ClaudeWCT.Numerics.LowerCredit.LowerAcceptS1
  rw [hdec, ← hL]
  by_cases h2 : ClaudeWCT.Numerics.LowerCredit.SpareS1 v.toNat ∧ L.sum ≤ target lay ∧ target lay - L.sum < 8
  · rw [if_pos h2]
    simp only
    rw [wordCredit_lower lay hl _ hlen]
    simp only [ClaudeWCT.WCT9.dispatchPenalty, hl, if_false, Nat.add_zero,
      ClaudeWCT.WCT9.producerZeroBound, ClaudeWCT.WCT9.producerZeroMax, producerRankBound, false_or, filter_zero_count,
      lowerWord_eq_ofS1, ClaudeWCT.Numerics.LowerRank.RankGood]
    constructor
    · intro h
      split_ifs at h with h3
      · exact ⟨⟨⟨⟨v.isLt, h2.1, h2.2.1, h2.2.2, Nat.zero_le _⟩, h3.2.1⟩, h3.2.2⟩, h3.1⟩
      · simp at h
    · intro h
      rw [if_pos ⟨h.2, h.1.1.2, h.1.2⟩]
      rfl
  · rw [if_neg h2]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨⟨⟨⟨-, h1, h3, h4, -⟩, -⟩, -⟩, -⟩
    exact h2 ⟨h1, h3, h4⟩

theorem producerDecode_lower_isSome_iff_word (lay : Layer) (hl : lay ≠ 0) (v : Digest) :
    (producerDecode lay v).isSome ↔
      lowerSpare v ∧ ClaudeWCT.Numerics.LowerRank.LowerAcceptRank (target lay) 0 (lowerWord v) ∧
        producerFloor lay ≤ (lowerProducerDigits lay v.toNat).count 6 +
          4 * ClaudeWCT.WCT9.savedCopies lay (lowerProducerDigits lay v.toNat) := by
  rw [producerDecode_lower_isSome_iff lay hl]
  unfold lowerProducerAccept
  rw [lowerWord_eq_ofS1]
  constructor
  · intro h
    exact ⟨h.1.1.1.2.1,
      (ClaudeWCT.Numerics.LowerRank.lowerAcceptS1Rank_iff v.isLt h.1.1.1.2.1 _ _).mp h.1, h.2⟩
  · intro h
    exact ⟨(ClaudeWCT.Numerics.LowerRank.lowerAcceptS1Rank_iff v.isLt h.1 _ _).mpr h.2.1, h.2.2⟩

theorem card_producer_lower (lay : Layer) (hl : lay ≠ 0) (n : ℕ)
    (hn : n ≤ (univ.filter fun v : BitVec 128 => lowerProducerAccept lay v.toNat).card) :
    n ≤ (univ.filter fun v : Digest => (producerDecode lay v).isSome).card := by
  convert hn using 1
  exact congrArg Finset.card (filter_congr fun v _ => by rw [producerDecode_lower_isSome_iff lay hl])
theorem filter_length_eq_sum (l : List ℕ) (p : ℕ → Bool) :
    (l.filter p).length = (l.map fun i => if p i then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    split <;> simp_all
    omega
noncomputable def producerCount (lay : Layer) : ℕ :=
  (univ.filter fun v : Digest => (producerDecode lay v).isSome).card

theorem producerDecode_lowerSpare (lay : Layer) (hl : lay ≠ 0) (v : Digest)
    (hv : (producerDecode lay v).isSome) : lowerSpare v := by
  obtain ⟨ds, hd⟩ := Option.isSome_iff_exists.mp hv
  exact decode_lowerSpare hl (ClaudeWCT.WCT9.producerDecode_decode hd)

section SelectedCardinality

theorem selected_top_arithmetic (n g : Nat) :
    g * 2^128 + 2^127 * n = (n + 2 * g) * 2^127 := by
  rw [show (2 : ℕ)^128 = 2 * 2^127 by norm_num]
  ring

theorem selected_top_count_transport (p : Digest → Prop) [DecidablePred p]
    (n g : Nat) (hn : (univ.filter p).card = n)
    (hg : (univ.filter fun d => p d ∧ TopDualHalf.gate d).card = g) :
    (univ.filter fun a : HashOutput => p (TopDualHalf.select a)).card = (n + 2*g)*2^127 := by
  have hc := TopDualHalf.card_select_pred p
  have hcounts := congrArg₂ (fun g n : Nat => g * 2^128 + 2^127 * n) hg hn
  exact (hc.trans hcounts).trans (selected_top_arithmetic n g)

theorem selected_lower_count_transport (p : Digest → Prop) [DecidablePred p]
    (n : Nat) (hn : (univ.filter p).card = n) (hp : ∀ d, p d → lowerSpare d) :
    (univ.filter fun a : HashOutput => p (DualHalf.select a)).card = n * (7*2^126) := by
  have hc := DualHalf.card_select_pred p hp
  exact hc.trans (congrArg (fun n : Nat => n * (7 * 2^126)) hn)

end SelectedCardinality

end ClaudeWCT.W9.T3.ProducerV5

namespace SigGolfResearch.LowerEffectiveCounting
open scoped BigOperators
open Finset NonbinaryTop.Codec NonbinaryTop.Counting SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

def dataDigit (w : «Word») (i : Fin 42) : Fin 8 :=
  (w.1 ⟨i.val / 3, by omega⟩).val ⟨i.val % 3, by omega⟩
def digits (w : «Word») : List Nat :=
  List.ofFn (fun i : Fin 42 => (dataDigit w i).val) ++ [w.2.val]

theorem digits_length (w : «Word») : (digits w).length = 43 := by simp [digits]
theorem digits_blocks (w : «Word») : digits w =
    (List.ofFn fun q : Fin 14 => [(w.1 q).val 0 |>.val, (w.1 q).val 1 |>.val,
      (w.1 q).val 2 |>.val]).flatten ++ [w.2.val] := by rfl

theorem digits_getD (w : «Word») (i : Nat) (hi : i < 43) :
    (digits w).getD i 0 =
      if h : i < 42 then (dataDigit w ⟨i, h⟩).val else w.2.val := by
  interval_cases i <;> rfl

attribute [local irreducible] digits

theorem digits_sum (w : «Word») : (digits w).sum = weight w := by
  rw [digits_blocks, List.sum_append, List.sum_flatten]
  simp [weight, tripleSum8, Fin.sum_univ_succ, List.map_ofFn, List.sum_ofFn, Nat.add_assoc]

theorem digits_count (w : «Word») (v : Nat) :
    (digits w).count v =
      (∑ q : Fin 14, ∑ i : Fin 3, if ((w.1 q).val i).val = v then 1 else 0) +
      if w.2.val = v then 1 else 0 := by
  have ht (d : Triple8) : [((d 0).val), ((d 1).val), ((d 2).val)].count v =
      ∑ i : Fin 3, if (d i).val = v then 1 else 0 := by
    simp only [List.count_cons, List.count_nil, beq_iff_eq, Fin.sum_univ_succ,
      Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    omega
  rw [digits_blocks, List.count_append, List.count_flatten]
  simp only [List.map_ofFn, Function.comp_def, ht, List.sum_ofFn, List.count_cons, List.count_nil, beq_iff_eq]
  omega

theorem digits_zeros (w : «Word») : (digits w).count 0 = zeros w := by
  exact digits_count w 0

def copyFlag (lay : Layer) (w : «Word») (i : Nat) : Nat :=
  if ClaudeWCT.WCT9.safeZeroCopy lay (digits w) i then 1 else 0

theorem copyFlag_block (lay : Layer) (hl : lay ≠ 0) (w : «Word») (q : Fin 14) :
    ([3*q.val, 3*q.val+1, 3*q.val+2].map (copyFlag lay w)).sum =
      copies (decide (q.val = 0)) (w.1 q).val := by
  fin_cases q <;>
    simp [copyFlag, ClaudeWCT.WCT9.safeZeroCopy, maxDigit, hl, digits_getD,
      dataDigit, copies, and_comm, -List.getD_eq_getElem?_getD]
  all_goals split_ifs <;> omega

theorem filter_length_eq_sum (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length = (l.map fun i => if p i then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    split <;> simp_all
    omega

theorem savedCopies_digits (lay : Layer) (hl : lay ≠ 0) (w : «Word») :
    ClaudeWCT.WCT9.savedCopies lay (digits w) =
      ∑ q : Fin 14, copies (decide (q.val = 0)) (w.1 q).val := by
  have hc : chainCount lay = 43 := by fin_cases lay <;> simp_all [chainCount]
  unfold ClaudeWCT.WCT9.savedCopies
  rw [filter_length_eq_sum, hc]
  simp only [decide_eq_true_eq]
  rw [show (fun i => if ClaudeWCT.WCT9.safeZeroCopy lay (digits w) i then (1 : Nat) else 0) =
      copyFlag lay w from rfl]
  have hi : List.range 43 =
      (List.ofFn fun q : Fin 14 => [3*q.val, 3*q.val+1, 3*q.val+2]).flatten ++ [42] := by
    decide +kernel
  rw [hi, List.map_append, List.sum_append]
  have ht : ([42].map (copyFlag lay w)).sum = 0 := by
    simp [copyFlag, ClaudeWCT.WCT9.safeZeroCopy, hl]
  rw [ht, Nat.add_zero, List.map_flatten, List.sum_flatten]
  simp only [List.map_map, List.map_ofFn, Function.comp_def, copyFlag_block lay hl, List.sum_ofFn]

theorem digits_effectiveScore (lay : Layer) (hl : lay ≠ 0) (w : «Word») :
    (digits w).count 6 + 4 * ClaudeWCT.WCT9.savedCopies lay (digits w) = score w := by
  rw [digits_count, savedCopies_digits lay hl]
  unfold score score3 NonbinaryTop.CreditCounting.credit8
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

end SigGolfResearch.LowerEffectiveCounting

namespace SigGolfResearch.LowerEffectiveCounting
open scoped BigOperators
open Finset
open SigGolfCandidate.T3 (Digest Layer lowerPack lowerWord lowerWord_lowerPack lowerSpare_lowerPack target)
open ClaudeWCT.Numerics.LowerCredit
open ClaudeWCT.W9.T3.ProducerV5
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.constructorNameAsVariable false

theorem dataDigit_slot (w : «Word») (q : Fin 14) (i : Fin 3) :
    dataDigit w (ClaudeWCT.Numerics.LowerRank.slot q i) = (w.1 q).val i := by
  unfold dataDigit ClaudeWCT.Numerics.LowerRank.slot
  have hq : (3 * q.val + i.val) / 3 = q.val := by omega
  have hi : (3 * q.val + i.val) % 3 = i.val := by omega
  have hq' : (⟨(3 * q.val + i.val) / 3, by omega⟩ : Fin 14) = q := Fin.ext hq
  have hi' : (⟨(3 * q.val + i.val) % 3, by omega⟩ : Fin 3) = i := Fin.ext hi
  rw [hq', hi']

def encode (w : «Word») : Digest := lowerPack (finFunctionFinEquiv (dataDigit w))

theorem encode_injective_weight (T : Nat) (a b : «Word»)
    (ha : weight a = T) (hb : weight b = T) (he : encode a = encode b) : a = b := by
  have hn := congrArg lowerWord he
  simp only [encode, lowerWord_lowerPack (equiv_lt _)] at hn
  have hf : dataDigit a = dataDigit b := finFunctionFinEquiv.injective (Fin.ext hn)
  have hfst : a.1 = b.1 := by
    funext q
    apply Subtype.ext
    funext i
    simpa only [dataDigit_slot] using congrFun hf (ClaudeWCT.Numerics.LowerRank.slot q i)
  apply Prod.ext hfst
  apply Fin.ext
  unfold weight at ha hb
  rw [hfst] at ha
  omega

theorem rankGood_encode (w : «Word») :
    ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv (dataDigit w)) := by
  intro q
  by_contra hn
  have hbad := (ClaudeWCT.Numerics.LowerRank.mem_badWords q (dataDigit w)).mp
    ((ClaudeWCT.Numerics.LowerRank.rank_bad_iff (dataDigit w) q).mp hn)
  simp only [dataDigit_slot] at hbad
  have h1 := congrArg Fin.val hbad.2.1
  have h2 := congrArg Fin.val hbad.2.2
  have hr := (w.1 q).property
  change rankFloor q ≤ ((w.1 q).val 0).val + 8 * ((w.1 q).val 1).val + 64 * ((w.1 q).val 2).val at hr
  have h0 : ((w.1 q).val 0).val < rankFloor q := hbad.1
  simp only [Fin.val_zero] at h1 h2
  omega

theorem lowerDigitsS1_encode (w : «Word») :
    lowerDigitsS1 (encode w).toNat = List.ofFn (fun i : Fin 42 => (dataDigit w i).val) := by
  rw [lowerDigitsS1_eq (encode w).isLt (lowerSpare_lowerPack _)]
  rw [← lowerWord_eq_ofS1]
  unfold encode
  rw [lowerWord_lowerPack (equiv_lt _)]
  exact lowerDigits_equiv (dataDigit w)

theorem lowerProducerAccept_encode_aux (lay : Layer) (w : «Word»)
    (hw : weight w = target lay) (hz : zeros w ≤ 5)
    (hc : ClaudeWCT.WCT9.producerFloor lay ≤ score w)
    (hsum : (digits w).sum = weight w)
    (hzero : (digits w).count 0 = zeros w)
    (hscore : (digits w).count 6 + 4 * ClaudeWCT.WCT9.savedCopies lay (digits w) = score w) :
    lowerProducerAccept lay (encode w).toNat := by
  have hsum' : (List.ofFn (fun i : Fin 42 => (dataDigit w i).val)).sum + w.2.val = target lay := by
    simpa only [digits, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] using hsum.trans hw
  have hcheck : target lay - (List.ofFn (fun i : Fin 42 => (dataDigit w i).val)).sum = w.2.val := by omega
  have hd : lowerProducerDigits lay (encode w).toNat = digits w := by
    simp only [lowerProducerDigits, lowerDigitsS1_encode, hcheck, digits]
  unfold lowerProducerAccept
  constructor
  · apply (ClaudeWCT.Numerics.LowerRank.lowerAcceptS1Rank_iff (encode w).isLt
      (lowerSpare_lowerPack _) (target lay) 0).mpr
    rw [← lowerWord_eq_ofS1]
    unfold encode
    rw [lowerWord_lowerPack (equiv_lt _)]
    refine ⟨⟨⟨equiv_lt _, ?_, ?_, Nat.zero_le _⟩, ?_⟩, rankGood_encode w⟩
    · rw [lowerDigits_equiv]
      omega
    · rw [lowerDigits_equiv, hcheck]
      exact w.2.isLt
    · rw [lowerDigits_equiv, hcheck]
      change (digits w).count 0 ≤ 5
      rw [hzero]
      exact hz
  · rw [hd, hscore]
    exact hc

theorem lowerProducerAccept_encode (lay : Layer) (hl : lay ≠ 0) (w : «Word»)
    (hw : weight w = target lay) (hz : zeros w ≤ 5)
    (hc : ClaudeWCT.WCT9.producerFloor lay ≤ score w) :
    lowerProducerAccept lay (encode w).toNat :=
  lowerProducerAccept_encode_aux lay w hw hz hc (digits_sum w) (digits_zeros w)
    (digits_effectiveScore lay hl w)

theorem card_lowerProducerAccept_model (lay : Layer) (hl : lay ≠ 0) :
    count (target lay) (ClaudeWCT.WCT9.producerFloor lay) ≤
      (Finset.univ.filter fun v : BitVec 128 => lowerProducerAccept lay v.toNat).card := by
  classical
  have hT : 0 < target lay ∧ target lay ≤ 301 := by fin_cases lay <;> decide +kernel
  have hf : ClaudeWCT.WCT9.producerFloor lay ≤ 128 := by fin_cases lay <;> decide +kernel
  rw [← card_model (target lay) (ClaudeWCT.WCT9.producerFloor lay) hT hf]
  apply Finset.card_le_card_of_injOn encode
  · intro w hw
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
    exact lowerProducerAccept_encode lay hl w hw.1 hw.2.2 hw.2.1
  · intro a ha b hb he
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha hb
    exact encode_injective_weight (target lay) a b ha.1 hb.1 he

end SigGolfResearch.LowerEffectiveCounting

namespace ClaudeWCT.W9.T3.ProducerV5
open OracleComp OracleSpec ENNReal Finset SigGolfCandidate.T3
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (searchLimit)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section SelectedLowerBounds

end SelectedLowerBounds

end ClaudeWCT.W9.T3.ProducerV5

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3
open ClaudeWCT.WCT9
/-- The canonical producer at floor `floor` without the path bonus (`low = false`): the word reward reaches the
floor. Path-aware acceptance is expressed by shifting the floor (`producerDecodeAt_lower_true`). -/
def accepted (lay : Layer) (floor : Nat) (P : List Nat → Prop) (value : Digest) : Prop :=
  match CanonicalPolicy.producerDecodeAt lay floor false value with
  | none => False
  | some digits => P digits
instance (lay : Layer) (floor : Nat) (P : List Nat → Prop) [DecidablePred P] :
    DecidablePred (accepted lay floor P) := fun value => by
  unfold accepted
  split <;> infer_instance

theorem accepted_iff (lay : Layer) (floor : Nat) (P : List Nat → Prop) (value : Digest) :
    accepted lay floor P value ↔
      ∃ digits, CanonicalPolicy.producerDecodeAt lay floor false value = some digits ∧ P digits := by
  unfold accepted
  cases hd : CanonicalPolicy.producerDecodeAt lay floor false value <;> simp

theorem accepted_lowerSpare (lay : Layer) (hl : lay ≠ 0) (floor : Nat)
    (P : List Nat → Prop) (value : Digest) (h : accepted lay floor P value) : lowerSpare value := by
  obtain ⟨digits, hd, _⟩ := (accepted_iff lay floor P value).mp h
  have hs := (CanonicalPolicy.producerDecodeAt_spec hd).1
  have hd' : decode (1 : Layer) value = some digits := by
    simpa only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] using hs
  exact decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hd'

/-- The canonical top predicate (floor 19 with the LOW bonus 3) holds for every word whose reward reaches a floor
`≥ 16`. -/
theorem accepted_topGood {floor : Nat} (hf : 16 ≤ floor) {P : List Nat → Prop} {value : Digest}
    (h : accepted 0 floor P value) : topGood value := by
  obtain ⟨ds, hd, _⟩ := (accepted_iff 0 floor P value).mp h
  have hs := CanonicalPolicy.producerDecodeAt_spec hd
  have hd' : CanonicalPolicy.producerDecodeAt 0 CanonicalPolicy.topFloor true value = some ds := by
    unfold CanonicalPolicy.producerDecodeAt
    simp only [hs.1]
    have hc : CanonicalPolicy.topFloor + dispatchPenalty 0 ds ≤ CanonicalPolicy.pathReward 0 true ds := by
      have := hs.2.1
      simp only [CanonicalPolicy.pathReward_top, if_true, if_false, Bool.false_eq_true] at this ⊢
      unfold CanonicalPolicy.topFloor
      omega
    rw [if_pos ⟨hc, hs.2.2.1, hs.2.2.2⟩]
  unfold topGood
  rw [hd']
  rfl

/-- The number of LOW words letting HIGH through is `3 * 2^126 - topFreeCount`. -/
noncomputable def topFreeCount : Nat :=
  (univ.filter fun v : Digest => topGood v ∧ ¬ TopChoice.blocked v).card

/-- The restricted choice: a producer-accepted top word is selected with weight `2^128 + 3*2^126 - topFreeCount`
(over `2^256`). -/
theorem selected_top_card (floor : Nat) (hf : 16 ≤ floor) (P : List Nat → Prop) [DecidablePred P]
    (n : Nat) (hn : (univ.filter (accepted 0 floor P)).card = n) :
    (univ.filter fun answer : HashOutput => accepted 0 floor P (encodingAnswer 0 answer)).card =
      n * (2^128 + 3*2^126 - topFreeCount) := by
  rw [← hn]
  exact TopChoice.card_choose_pred_eq topGood (accepted 0 floor P) (fun _ h => accepted_topGood hf h)
    topFreeCount rfl

theorem selected_lower_card (lay : Layer) (hl : lay ≠ 0) (floor : Nat)
    (P : List Nat → Prop) [DecidablePred P] (n : Nat)
    (hn : (univ.filter (accepted lay floor P)).card = n) :
    (univ.filter fun answer : HashOutput => accepted lay floor P (encodingAnswer lay answer)).card =
      n*(7*2^126) := by
  simpa only [encodingAnswer, if_neg hl] using
    selected_lower_count_transport (accepted lay floor P) n hn (accepted_lowerSpare lay hl floor P)

theorem selected_uniform_probability (lay : Layer) (floor : Nat) (P : List Nat → Prop) [DecidablePred P]
    (n : Nat)
    (hn : (univ.filter fun answer : HashOutput => accepted lay floor P (encodingAnswer lay answer)).card = n) :
    Pr[fun answer => accepted lay floor P (encodingAnswer lay answer) |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (n : ENNReal) / 2^256 := by
  rw [probEvent_uniformSample, hn]
  simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3
open ClaudeWCT.WCT9

theorem accepted_decode_iff (lay : Layer) (floor : Nat) (P : List Nat → Prop) (value : Digest) :
    accepted lay floor P value ↔ ∃ digits,
      CanonicalPolicy.decode lay value = some digits ∧
      floor + dispatchPenalty lay digits ≤ CanonicalPolicy.reward lay digits ∧
      producerZeroBound lay digits ∧ producerRankBound lay value ∧ P digits := by
  unfold accepted CanonicalPolicy.producerDecodeAt
  simp only [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false, Nat.add_zero]
  cases hd : CanonicalPolicy.decode lay value with
  | none => simp
  | some digits =>
      simp only [Option.some.injEq, exists_eq_left']
      split_ifs with hc
      · exact ⟨fun hp => ⟨hc.1, hc.2.1, hc.2.2, hp⟩,
          fun h => h.2.2.2⟩
      · simp only [false_iff]
        rintro ⟨hfloor, hzero, hrank, _⟩
        exact hc ⟨hfloor, hzero, hrank⟩

theorem accepted_lower_eq_one (lay : Layer) (hl : lay ≠ 0) (floor : Nat)
    (P : List Nat → Prop) (value : Digest) :
    accepted lay floor P value ↔ accepted 1 floor P value := by
  simp only [accepted_decode_iff]
  fin_cases lay <;>
    simp_all [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, CanonicalPolicy.reward,
      dispatchPenalty, wordCredit, savedCopies, safeZeroCopy, producerZeroBound, producerZeroMax, producerRankBound,
      chainCount, maxDigit]

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

theorem accepted_credit_floor {lay : Layer} {floor credit : Nat} {v : Digest}
    (h : accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = credit) v) :
    floor ≤ credit := by
  obtain ⟨ds, hd, hc⟩ := (accepted_iff lay floor _ v).mp h
  exact hc ▸ CanonicalPolicy.producerDecodeAt_credit hd

/-- Campaign R6: dropping the floor keeps a producer-accepted top word (no path bonus). -/
theorem pda_zero_of {floor : Nat} {v : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor false v = some ds) :
    CanonicalPolicy.producerDecodeAt 0 0 false v = some ds := by
  have hs := CanonicalPolicy.producerDecodeAt_spec h
  unfold CanonicalPolicy.producerDecodeAt
  rw [hs.1]
  dsimp only
  rw [if_pos ⟨by have := hs.2.1; omega, hs.2.2⟩]

/-- Campaign R6: a top credit (no path bonus) is at most 146 (model score `≤ 149`). -/
theorem accepted_top_credit_le {floor credit : Nat} {v : Digest}
    (h : accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit) v) : credit ≤ 146 := by
  obtain ⟨ds, hd, hc⟩ := (accepted_iff 0 floor _ v).mp h
  exact SigGolfResearch.R6Top.acc_le credit v
    ((SigGolfResearch.R6Top.acc_iff credit v).mpr ⟨ds, pda_zero_of hd, hc⟩)

theorem selected_credit_card_zero_of_lt (lay : Layer) (floor credit : Nat) (hf : credit < floor) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay false ds = credit) (encodingAnswer lay answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_credit_floor h
  omega

theorem selected_top_credit_card_zero_of_gt (floor credit : Nat) (hc : 146 < credit) :
    (univ.filter fun answer : HashOutput => accepted 0 floor
      (fun ds => CanonicalPolicy.credit 0 false ds = credit) (encodingAnswer 0 answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_top_credit_le h
  omega
end ClaudeWCT.W9.T3.ProducerV5.Canonical
namespace SigGolfResearch.LowerEffectiveCounting
open scoped BigOperators
open Finset NonbinaryTop.Codec
open SigGolfCandidate.T3
open ClaudeWCT.Numerics.LowerCredit

def tripleOf (f : Fin 42 → Fin 8) (q : Fin 14) : Triple8 :=
  fun i => f (ClaudeWCT.Numerics.LowerRank.slot q i)

theorem rank_tripleOf (f : Fin 42 → Fin 8)
    (h : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f)) (q : Fin 14) :
    rankFloor q ≤ rank (tripleOf f q) := by
  by_contra hn
  have hb : rankFloor q ≤ 5 := by unfold rankFloor; split <;> omega
  have hr : rank (tripleOf f q) < rankFloor q := by omega
  simp only [rank, tripleOf] at hr
  have h1 : f (ClaudeWCT.Numerics.LowerRank.slot q 1) = 0 := Fin.ext (by omega)
  have h2 : f (ClaudeWCT.Numerics.LowerRank.slot q 2) = 0 := Fin.ext (by omega)
  have h0 : (f (ClaudeWCT.Numerics.LowerRank.slot q 0)).val <
      ClaudeWCT.Numerics.LowerRank.rankFloor q.val := by
    change (f (ClaudeWCT.Numerics.LowerRank.slot q 0)).val < rankFloor q
    omega
  exact ((ClaudeWCT.Numerics.LowerRank.rank_bad_iff f q).mpr
    ((ClaudeWCT.Numerics.LowerRank.mem_badWords q f).mpr ⟨h0,h1,h2⟩)) (h q)

def fromDigits (f : Fin 42 → Fin 8)
    (h : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f)) (last : Fin 8) : «Word» :=
  (fun q => ⟨tripleOf f q, rank_tripleOf f h q⟩, last)

theorem dataDigit_fromDigits (f : Fin 42 → Fin 8)
    (h : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f)) (last : Fin 8) :
    dataDigit (fromDigits f h last) = f := by
  funext i
  change f ⟨3*(i.val/3)+i.val%3, _⟩ = f i
  congr 1
  apply Fin.ext
  change 3*(i.val/3)+i.val%3 = i.val
  omega

theorem encode_fromDigits (f : Fin 42 → Fin 8)
    (h : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f)) (last : Fin 8) :
    encode (fromDigits f h last) = lowerPack (finFunctionFinEquiv f) := by
  simp only [encode, dataDigit_fromDigits]

theorem digits_fromDigits (f : Fin 42 → Fin 8)
    (h : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f)) (last : Fin 8) :
    digits (fromDigits f h last) = List.ofFn (fun i => (f i).val) ++ [last.val] := by
  unfold digits
  rw [dataDigit_fromDigits]
  rfl

end SigGolfResearch.LowerEffectiveCounting

namespace SigGolfResearch.LowerEffectiveCounting
open SigGolfCandidate.T3
open ClaudeWCT.Numerics.LowerCredit

theorem decode_lower_model {v : Digest} {ds : List Nat}
    (hd : decode (1 : Layer) v = some ds)
    (hr : ClaudeWCT.Numerics.LowerRank.RankGood (lowerWord v)) :
    ∃ w : «Word», encode w = v ∧ digits w = ds ∧ weight w = 201 := by
  have hsum : ds.sum = 201 := (decode_length_sum hd).2
  rw [decode_lowerWord (by decide : (1 : Layer) ≠ 0)] at hd
  let D := lowerDigits (lowerWord v)
  change (if lowerSpare v ∧ D.sum ≤ 201 ∧ 201-D.sum < 8 then
    some (D ++ [201-D.sum]) else none) = some ds at hd
  by_cases hc : lowerSpare v ∧ D.sum ≤ 201 ∧ 201-D.sum < 8
  · rw [if_pos hc] at hd
    have hds : D ++ [201-D.sum] = ds := Option.some.inj hd
    let n : Fin (8^42) := ⟨lowerWord v, by simpa using lowerWord_lt v⟩
    let f : Fin 42 → Fin 8 := finFunctionFinEquiv.symm n
    have hf : (finFunctionFinEquiv f).val = lowerWord v :=
      congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply n)
    have hr' : ClaudeWCT.Numerics.LowerRank.RankGood (finFunctionFinEquiv f) := by
      rw [hf]
      exact hr
    let last : Fin 8 := ⟨201-D.sum, hc.2.2⟩
    let w := fromDigits f hr' last
    have hD : D = List.ofFn (fun i => (f i).val) := by
      have h := lowerDigits_equiv f
      rw [hf] at h
      exact h
    have hdigits : digits w = ds := by
      rw [digits_fromDigits, ← hD]
      exact hds
    refine ⟨w, ?_, hdigits, ?_⟩
    · rw [encode_fromDigits, hf]
      exact lowerPack_lowerWord hc.1
    · rw [← digits_sum, hdigits]
      exact hsum
  · rw [if_neg hc] at hd
    cases hd
end SigGolfResearch.LowerEffectiveCounting

namespace SigGolfResearch.LowerEffectiveCounting
open SigGolfCandidate.T3
open ClaudeWCT.Numerics.LowerCredit

theorem decode_encode_201 (w : «Word») (hw : weight w = 201) :
    decode (1 : Layer) (encode w) = some (digits w) := by
  let D := List.ofFn (fun i : Fin 42 => (dataDigit w i).val)
  have hsum : D.sum+w.2.val = 201 := by
    have h := (digits_sum w).trans hw
    simpa only [digits, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] using h
  have hd : lowerDigits (lowerWord (encode w)) = D := by
    rw [encode, lowerWord_lowerPack (equiv_lt _)]
    exact lowerDigits_equiv (dataDigit w)
  have hs : lowerSpare (encode w) := lowerSpare_lowerPack _
  have hc : 201-D.sum = w.2.val := by omega
  rw [decode_lowerWord (by decide : (1 : Layer) ≠ 0)]
  change (if lowerSpare (encode w) ∧ (lowerDigits (lowerWord (encode w))).sum ≤ 201 ∧
      201-(lowerDigits (lowerWord (encode w))).sum < 8 then
      some (lowerDigits (lowerWord (encode w)) ++ [201-(lowerDigits (lowerWord (encode w))).sum])
    else none) = _
  rw [hd, hc, if_pos ⟨hs, by omega, w.2.isLt⟩]
  rfl
end SigGolfResearch.LowerEffectiveCounting

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.LowerEffectiveCounting
set_option maxRecDepth 100000

theorem reward_lower_model (w : SigGolfResearch.LowerEffectiveCounting.«Word») :
    CanonicalPolicy.reward 1 (digits w) = score w := by
  unfold CanonicalPolicy.reward
  rw [wordCredit_lower _ (by decide) _ (digits_length w)]
  exact digits_effectiveScore _ (by decide) w

theorem credit_lower_model (w : SigGolfResearch.LowerEffectiveCounting.«Word») :
    CanonicalPolicy.credit 1 false (digits w) = score w := by
  simp only [CanonicalPolicy.credit, CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false, Nat.add_zero,
    reward_lower_model, dispatchPenalty,
    show (1 : Layer) ≠ 0 by decide, if_false, Nat.sub_zero]

theorem accepted_lower_model (floor : Nat) (P : List Nat → Prop) (v : Digest) :
    accepted 1 floor P v ↔ ∃ w : SigGolfResearch.LowerEffectiveCounting.«Word»,
      SigGolfResearch.LowerEffectiveCounting.encode w = v ∧ weight w = 201 ∧ floor ≤ score w ∧ zeros w ≤ 5 ∧ P (digits w) := by
  rw [accepted_decode_iff]
  constructor
  · rintro ⟨ds, hd, hf, hz, hr, hP⟩
    have hd' : decode (1 : Layer) v = some ds := hd
    have hr' : ClaudeWCT.Numerics.LowerRank.RankGood (lowerWord v) := by
      simpa only [producerRankBound, show (1 : Layer) ≠ 0 by decide, false_or,
        ClaudeWCT.Numerics.LowerRank.RankGood, producerRankFloor,
        ClaudeWCT.Numerics.LowerRank.rankFloor] using hr
    obtain ⟨w, he, hds, hw⟩ := decode_lower_model hd' hr'
    rw [← hds] at hf hz hP
    simp only [dispatchPenalty, show (1 : Layer) ≠ 0 by decide, if_false, Nat.add_zero,
      reward_lower_model] at hf
    simp only [producerZeroBound, producerZeroMax, show (1 : Layer) ≠ 0 by decide, if_false, false_or,
      filter_zero_count, digits_zeros] at hz
    exact ⟨w, he, hw, hf, hz, hP⟩
  · rintro ⟨w, he, hw, hf, hz, hP⟩
    subst v
    refine ⟨digits w, decode_encode_201 w hw, ?_, ?_, ?_, hP⟩
    · simpa only [dispatchPenalty, show (1 : Layer) ≠ 0 by decide, if_false,
        Nat.add_zero, reward_lower_model] using hf
    · simpa only [producerZeroBound, producerZeroMax, show (1 : Layer) ≠ 0 by decide, if_false, false_or,
        filter_zero_count, digits_zeros] using hz
    · simpa only [producerRankBound, show (1 : Layer) ≠ 0 by decide, false_or,
        SigGolfResearch.LowerEffectiveCounting.encode, lowerWord_lowerPack (ClaudeWCT.Numerics.LowerCredit.equiv_lt _),
        ClaudeWCT.Numerics.LowerRank.RankGood, producerRankFloor,
        ClaudeWCT.Numerics.LowerRank.rankFloor]
        using rankGood_encode w

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.LowerEffectiveCounting
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
attribute [local irreducible] accepted SigGolfResearch.LowerEffectiveCounting.encode

theorem accepted_lower_card (floor : Nat) (P : List Nat → Prop) [DecidablePred P] :
    (univ.filter (accepted 1 floor P)).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        weight w = 201 ∧ floor ≤ score w ∧ zeros w ≤ 5 ∧ P (digits w)).card := by
  symm
  apply Finset.card_bij (fun w _ => SigGolfResearch.LowerEffectiveCounting.encode w)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact (accepted_lower_model floor P (SigGolfResearch.LowerEffectiveCounting.encode w)).mpr ⟨w, rfl, hw⟩
  · intro a ha b hb he
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact encode_injective_weight 201 a b ha.1 hb.1 he
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    obtain ⟨w, he, hw⟩ := (accepted_lower_model floor P v).mp hv
    exact ⟨w, by simpa only [mem_filter, mem_univ, true_and] using hw, he⟩

theorem accepted_lower_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter (accepted 1 floor (fun ds => CanonicalPolicy.credit 1 false ds = credit))).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        zeros w ≤ 5 ∧ weight w = 201 ∧ score w = credit).card := by
  rw [accepted_lower_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [credit_lower_model]
  constructor
  · rintro ⟨hw, _, hz, hc⟩
    exact ⟨hz, hw, hc⟩
  · rintro ⟨hz, hw, hc⟩
    exact ⟨hw, by omega, hz, hc⟩
end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.LowerEffectiveCounting
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

theorem credit_lower_eq_one (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) :
    CanonicalPolicy.credit lay false ds = CanonicalPolicy.credit 1 false ds := by
  fin_cases lay <;> simp_all [CanonicalPolicy.credit, CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false,
    CanonicalPolicy.reward,
    dispatchPenalty, wordCredit, savedCopies, safeZeroCopy, chainCount, maxDigit]

theorem accepted_lower_credit_eq_one (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat) (v : Digest) :
    accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = credit) v ↔
      accepted 1 floor (fun ds => CanonicalPolicy.credit 1 false ds = credit) v := by
  rw [accepted_lower_eq_one lay hl]
  simp only [credit_lower_eq_one lay hl]

theorem accepted_lower_credit_card_all (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat)
    (hf : floor ≤ credit) :
    (univ.filter (accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = credit))).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        zeros w ≤ 5 ∧ weight w = 201 ∧ score w = credit).card := by
  rw [show (univ.filter (accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = credit))) =
      (univ.filter (accepted 1 floor (fun ds => CanonicalPolicy.credit 1 false ds = credit))) by
        exact Finset.filter_congr fun v _ => accepted_lower_credit_eq_one lay hl floor credit v]
  exact accepted_lower_credit_card floor credit hf

theorem selected_lower_credit_card (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat)
    (hf : floor ≤ credit) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay false ds = credit) (encodingAnswer lay answer)).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        zeros w ≤ 5 ∧ weight w = 201 ∧ score w = credit).card * (7*2^126) := by
  exact selected_lower_card lay hl floor _ _ (accepted_lower_credit_card_all lay hl floor credit hf)

theorem accepted_lower_credit_le (lay : Layer) (hl : lay ≠ 0) {floor credit : Nat} {v : Digest}
    (h : accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = credit) v) : credit ≤ 117 := by
  have h1 := (accepted_lower_credit_eq_one lay hl floor credit v).mp h
  obtain ⟨w, _, _, _, _, hc⟩ := (accepted_lower_model floor _ v).mp h1
  rw [credit_lower_model] at hc
  exact hc ▸ SigGolfResearch.LowerEffectiveCounting.score_le w

theorem selected_lower_credit_card_zero_of_gt (lay : Layer) (hl : lay ≠ 0)
    (floor credit : Nat) (hc : 117 < credit) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay false ds = credit) (encodingAnswer lay answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_lower_credit_le lay hl h
  omega

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem producerDecodeAt_floor_zero {lay : Layer} {floor : Nat} {low : Bool} {value : Digest} {ds : List Nat}
    (htop : lay = 0 → low = true → 3 ≤ floor)
    (h : CanonicalPolicy.producerDecodeAt lay floor low value = some ds) :
    CanonicalPolicy.producerDecodeAt lay 0 false value = some ds := by
  have hs := CanonicalPolicy.producerDecodeAt_spec h
  unfold CanonicalPolicy.producerDecodeAt
  simp only [hs.1]
  have hp : dispatchPenalty lay ds ≤ CanonicalPolicy.reward lay ds := by
    have h1 := hs.2.1
    by_cases hl : lay = 0
    · subst hl
      rw [CanonicalPolicy.pathReward_top] at h1
      cases low
      · simp at h1; omega
      · have := htop rfl rfl
        simp at h1; omega
    · simp only [dispatchPenalty, if_neg hl]; omega
  rw [if_pos ⟨by simpa [CanonicalPolicy.pathReward] using hp, hs.2.2.1, hs.2.2.2⟩]

theorem producerDecodeAt_top_credit_lt {floor : Nat} (hf : 3 ≤ floor) {low : Bool} {value : Digest}
    {ds : List Nat} (h : CanonicalPolicy.producerDecodeAt 0 floor low value = some ds) :
    CanonicalPolicy.credit 0 low ds < 220 := by
  have ha : accepted 0 0 (fun digits => CanonicalPolicy.credit 0 false digits =
      CanonicalPolicy.credit 0 false ds) value :=
    (accepted_iff 0 0 _ value).mpr ⟨ds, producerDecodeAt_floor_zero (fun _ _ => hf) h, rfl⟩
  have hb := accepted_top_credit_le ha
  rw [CanonicalPolicy.credit_top] at hb ⊢
  cases low <;> simp at hb ⊢ <;> omega

theorem producerDecodeAt_lower_credit_lt (lay : Layer) (hl : lay ≠ 0)
    {floor : Nat} {low : Bool} {value : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt lay floor low value = some ds) :
    CanonicalPolicy.credit lay low ds < 128 := by
  have ha : accepted lay 0 (fun digits => CanonicalPolicy.credit lay false digits =
      CanonicalPolicy.credit lay false ds) value :=
    (accepted_iff lay 0 _ value).mpr ⟨ds, producerDecodeAt_floor_zero (fun h0 => absurd h0 hl) h, rfl⟩
  have hb := accepted_lower_credit_le lay hl ha
  rw [CanonicalPolicy.credit_lower hl] at hb ⊢
  cases low <;> simp at hb ⊢ <;> omega

#print axioms producerDecodeAt_top_credit_lt
#print axioms producerDecodeAt_lower_credit_lt
end ClaudeWCT.W9.T3.ProducerV5.Canonical

/-! ### Path-aware decoder events (configuration (1)+(2))
The canonical decoder of a complete answer (`producerDecodeOut`) returns the digits and the selected half; its
credit is `credit lay low digits`. On the top layer the half carries no bonus and the word is the restricted
choice; on a lower layer the LOW path is the producer at floor `floor - 4` and adds 4 to the credit. -/
namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option maxRecDepth 100000

theorem producerDecodeAt_eq_some_iff (lay : Layer) (floor : Nat) (low : Bool) (v : Digest) (ds : List Nat) :
    CanonicalPolicy.producerDecodeAt lay floor low v = some ds ↔
      CanonicalPolicy.decode lay v = some ds ∧
      floor + dispatchPenalty lay ds ≤ CanonicalPolicy.pathReward lay low ds ∧
      producerZeroBound lay ds ∧ producerRankBound lay v := by
  constructor
  · exact CanonicalPolicy.producerDecodeAt_spec
  · rintro ⟨hd, hc⟩
    unfold CanonicalPolicy.producerDecodeAt
    simp only [hd]
    rw [if_pos hc]

theorem producerDecodeAt_lower_true (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (v : Digest) :
    CanonicalPolicy.producerDecodeAt lay floor true v =
      CanonicalPolicy.producerDecodeAt lay (floor - 4) false v := by
  have e1 (ds : List Nat) : CanonicalPolicy.pathReward lay true ds = CanonicalPolicy.reward lay ds + 4 := by
    simp [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus, hl]
  have e2 (ds : List Nat) : CanonicalPolicy.pathReward lay false ds = CanonicalPolicy.reward lay ds := by
    simp [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus]
  have e3 (ds : List Nat) : dispatchPenalty lay ds = 0 := by simp [dispatchPenalty, hl]
  cases h : CanonicalPolicy.producerDecodeAt lay (floor - 4) false v with
  | some ds =>
      have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h
      apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
      refine ⟨hs.1, ?_, hs.2.2⟩
      have h1 := hs.2.1
      rw [e1, e3]; rw [e2, e3] at h1
      omega
  | none =>
      cases h' : CanonicalPolicy.producerDecodeAt lay floor true v with
      | none => rfl
      | some ds =>
          have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h'
          have hc : CanonicalPolicy.producerDecodeAt lay (floor - 4) false v = some ds := by
            apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
            refine ⟨hs.1, ?_, hs.2.2⟩
            have h1 := hs.2.1
            rw [e1, e3] at h1; rw [e2, e3]
            omega
          rw [hc] at h
          cases h

theorem credit_lower_true (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) :
    CanonicalPolicy.credit lay true ds = CanonicalPolicy.credit lay false ds + 4 := by
  rw [CanonicalPolicy.credit_lower hl, CanonicalPolicy.credit_lower hl]
  simp

theorem producerDecodeAt_top_true (floor : Nat) (hf : 3 ≤ floor) (v : Digest) :
    CanonicalPolicy.producerDecodeAt 0 floor true v =
      CanonicalPolicy.producerDecodeAt 0 (floor - 3) false v := by
  have e1 (ds : List Nat) : CanonicalPolicy.pathReward 0 true ds = CanonicalPolicy.reward 0 ds + 3 := by
    simp [CanonicalPolicy.pathReward_top]
  have e2 (ds : List Nat) : CanonicalPolicy.pathReward 0 false ds = CanonicalPolicy.reward 0 ds := by
    simp [CanonicalPolicy.pathReward_top]
  cases h : CanonicalPolicy.producerDecodeAt 0 (floor - 3) false v with
  | some ds =>
      have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h
      apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
      refine ⟨hs.1, ?_, hs.2.2⟩
      have h1 := hs.2.1
      rw [e1]; rw [e2] at h1
      omega
  | none =>
      cases h' : CanonicalPolicy.producerDecodeAt 0 floor true v with
      | none => rfl
      | some ds =>
          have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h'
          have hc : CanonicalPolicy.producerDecodeAt 0 (floor - 3) false v = some ds := by
            apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
            refine ⟨hs.1, ?_, hs.2.2⟩
            have h1 := hs.2.1
            rw [e1] at h1; rw [e2]
            omega
          rw [hc] at h
          cases h

/-- On an accepted LOW top word (floor ≥ 3) the LOW credit is the plain credit plus 3. -/
theorem credit_top_true_of {floor : Nat} (hf : 3 ≤ floor) {v : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor true v = some ds) :
    CanonicalPolicy.credit 0 true ds = CanonicalPolicy.credit 0 false ds + 3 := by
  have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h
  have h1 := hs.2.1
  simp only [CanonicalPolicy.pathReward_top, if_true] at h1
  simp only [CanonicalPolicy.credit_top, if_true, if_false, Bool.false_eq_true, Nat.add_zero]
  omega

/-- The e7b top decoder event: through LOW (chosen when canonical-good or forced) the producer runs at floor
`floor - 3` and adds 3 to the credit; through HIGH it runs at `floor`. -/
theorem top_decoder_event (floor c : Nat) (hf : 3 ≤ floor) (answer : HashOutput) :
    (∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) ↔
      (if topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128) then
        accepted 0 (floor - 3) (fun ds => CanonicalPolicy.credit 0 false ds + 3 = c) (answer.extractLsb' 0 128)
      else accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) (answer.extractLsb' 128 128)) := by
  have hsel : lowSelected 0 answer =
      decide (topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128)) := rfl
  have hword : encodingAnswer 0 answer =
      if topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128) then
        answer.extractLsb' 0 128 else answer.extractLsb' 128 128 := rfl
  unfold CanonicalPolicy.producerDecodeOut
  rw [hsel, hword]
  by_cases hs : topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128)
  · simp only [hs, if_true, decide_true, accepted_iff]
    constructor
    · rintro ⟨⟨ds, l⟩, hd, hc⟩
      obtain ⟨ds', hd', he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨ds', by rw [← producerDecodeAt_top_true floor hf]; exact hd', ?_⟩
      rw [← credit_top_true_of hf hd']
      exact hc
    · rintro ⟨ds, hd, hc⟩
      have hd' : CanonicalPolicy.producerDecodeAt 0 floor true (answer.extractLsb' 0 128) = some ds := by
        rw [producerDecodeAt_top_true floor hf]; exact hd
      exact ⟨(ds, true), by rw [hd']; rfl, by rw [credit_top_true_of hf hd']; exact hc⟩
  · simp only [hs, if_false, decide_false, accepted_iff]
    constructor
    · rintro ⟨⟨ds, l⟩, hd, hc⟩
      obtain ⟨ds', hd', he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ds', hd', hc⟩
    · rintro ⟨ds, hd, hc⟩
      exact ⟨(ds, false), by rw [hd]; rfl, hc⟩

/-- Campaign R6: accepted top words of credit `c` (canonical producer at floor 0, no path bonus). -/
noncomputable def topWordCount (c : Nat) : Nat :=
  (univ.filter (accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c))).card

theorem card_filter_congr' {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card :=
  congrArg Finset.card (Finset.filter_congr fun a _ => h a)

theorem accepted_credit_acc (c : Nat) (v : Digest) :
    accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔ SigGolfResearch.R6Top.acc c v := by
  rw [accepted_iff, SigGolfResearch.R6Top.acc_iff]

theorem accepted_credit_floor_iff (floor c : Nat) (hf : floor ≤ c) (v : Digest) :
    accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔
      accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v := by
  rw [accepted_iff, accepted_iff]
  apply exists_congr; intro ds
  constructor
  · rintro ⟨hd, hc⟩; exact ⟨pda_zero_of hd, hc⟩
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp hd
    apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
    refine ⟨hs.1, ?_, hs.2.2⟩
    have h1 := hs.2.1
    simp only [CanonicalPolicy.credit] at hc
    omega

theorem accepted_top_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit))).card =
      topWordCount credit :=
  card_filter_congr' _ _ (accepted_credit_floor_iff floor credit hf)

/-- Campaign R6 + RC: the exact top credit law (credits `≥ 16`), from the R6 generating polynomial. -/
theorem topWordCount_eq (c : Nat) (hc : 16 ≤ c) :
    topWordCount c = SigGolfResearch.R6Top.histW SigGolfResearch.R6Top.topCountsR6 c := by
  by_cases h147 : c < 147
  · unfold topWordCount
    rw [card_filter_congr' _ (SigGolfResearch.R6Top.acc c) (accepted_credit_acc c),
      SigGolfResearch.R6Top.card_acc c hc h147]
  · have h0 : topWordCount c = 0 := by
      unfold topWordCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _ hv
      have := SigGolfResearch.R6Top.acc_le c v ((accepted_credit_acc c v).mp hv)
      omega
    rw [h0, SigGolfResearch.R6Top.histW_eq_zero _ _
      (fun e he => by have := SigGolfResearch.R6Top.topCountsR6_lt e he; omega)]

/-- Campaign R6 + RC (top floor 19, LOW bonus 3): the LOW-good predicate is acceptance at 16 without the bonus. -/
theorem topGood_iff (v : Digest) : topGood v ↔ accepted 0 16 (fun _ => True) v := by
  unfold topGood
  rw [show CanonicalPolicy.topFloor = 19 from rfl, producerDecodeAt_top_true 19 (by decide), accepted_iff]
  simp only [and_true]
  exact Option.isSome_iff_exists

/-- The credit of a top word (0 when the producer rejects it at floor 0). -/
def creditOf (v : Digest) : Nat :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => 0
  | some ds => CanonicalPolicy.credit 0 false ds

theorem creditOf_of_acc {c : Nat} {v : Digest} (h : SigGolfResearch.R6Top.acc c v) : creditOf v = c := by
  obtain ⟨ds, hd, hc⟩ := (SigGolfResearch.R6Top.acc_iff c v).mp h
  unfold creditOf; rw [hd]; exact hc

theorem accepted16_iff (v : Digest) :
    accepted 0 16 (fun _ => True) v ↔ ∃ c, 16 ≤ c ∧ SigGolfResearch.R6Top.acc c v := by
  rw [accepted_iff]
  constructor
  · rintro ⟨ds, hd, -⟩
    have hc := CanonicalPolicy.producerDecodeAt_credit hd
    exact ⟨_, hc, (SigGolfResearch.R6Top.acc_iff _ v).mpr ⟨ds, pda_zero_of hd, rfl⟩⟩
  · rintro ⟨c, hc, ha⟩
    have h := (accepted_credit_floor_iff 16 c hc v).mpr ((accepted_credit_acc c v).mpr ha)
    obtain ⟨ds, hd, -⟩ := (accepted_iff _ _ _ v).mp h
    exact ⟨ds, hd, trivial⟩

theorem fiber_free (c : Nat) (hc : 16 ≤ c) (v : Digest) :
    ((accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v) ∧ creditOf v = c) ↔
      (SigGolfResearch.R6Top.acc c v ∧ ¬ TopChoice.blocked v) := by
  constructor
  · rintro ⟨⟨ha, hb⟩, he⟩
    obtain ⟨c', -, hc'⟩ := (accepted16_iff v).mp ha
    have := creditOf_of_acc hc'
    subst he
    rw [this]; exact ⟨hc', hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨(accepted16_iff v).mpr ⟨c, hc, ha⟩, hb⟩, creditOf_of_acc ha⟩

/-- Campaign R6 + RC: the exact number of LOW-good top words whose LOW is not forced. -/
theorem topFreeCount_eq : topFreeCount = SigGolfResearch.R6Top.freeCountR6 := by
  unfold topFreeCount
  rw [card_filter_congr' _ (fun v => accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    (fun v => and_congr_left' (topGood_iff v))]
  rw [SigGolfResearch.R6Top.fiber_card_filter (fun v => accepted 0 16 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    creditOf (List.range' 16 131).toFinset (fun v hv => by
      obtain ⟨c, hc, ha⟩ := (accepted16_iff v).mp hv.1
      rw [creditOf_of_acc ha, List.mem_toFinset, List.mem_range'_1]
      have := SigGolfResearch.R6Top.acc_le c v ha
      omega)]
  rw [← SigGolfResearch.R6Top.freeCountR6_hist, ← List.sum_toFinset _ List.nodup_range']
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := List.mem_range'_1.mp (List.mem_toFinset.mp hc)
  rw [Finset.filter_filter, card_filter_congr' _ (fun v => SigGolfResearch.R6Top.acc c v ∧ ¬ TopChoice.blocked v)
    (fun v => fiber_free c hc'.1 v)]
  exact SigGolfResearch.R6Top.card_acc_free c hc'.1 (by omega)

/-- Campaign R6 + RC: the HIGH half is selected with weight `3*2^126 - freeCount` per accepted HIGH word. -/
def topHighWeight : Nat := 3*2^126 - SigGolfResearch.R6Top.freeCountR6

theorem topFreeCount_eq_filter :
    (univ.filter fun v : Digest => topGood v ∧ ¬ TopChoice.blocked v).card = SigGolfResearch.R6Top.freeCountR6 :=
  topFreeCount_eq

theorem freeCount_add_top :
    TopChoice.freeCount topGood + SigGolfResearch.R6Top.freeCountR6 = 3 * 2 ^ 126 := by
  have h := TopChoice.freeCount_add topGood
  rw [topFreeCount_eq_filter] at h
  exact h

/-- Pure arithmetic (keeps `TopChoice.freeCount topGood` abstract for the kernel). -/
theorem highWeight_arith (F : Nat) (h : F + SigGolfResearch.R6Top.freeCountR6 = 3 * 2 ^ 126) : F = topHighWeight := by
  unfold topHighWeight
  omega

theorem freeCount_eq_compl : TopChoice.freeCount topGood = topHighWeight :=
  highWeight_arith _ freeCount_add_top

/-- Generic restricted-choice path count. -/
theorem card_choose_path_generic (good : Digest → Prop) [DecidablePred good] (lo hi : Digest → Prop)
    [DecidablePred lo] [DecidablePred hi] (hlo : ∀ d, lo d → good d) :
    (univ.filter fun a : HashOutput => if good (a.extractLsb' 0 128) ∨ TopChoice.blocked (a.extractLsb' 0 128)
        then lo (a.extractLsb' 0 128) else hi (a.extractLsb' 128 128)).card =
      (univ.filter lo).card * 2^128 + TopChoice.freeCount good * (univ.filter hi).card := by
  have he : (univ.filter fun a : HashOutput => if good (a.extractLsb' 0 128) ∨ TopChoice.blocked (a.extractLsb' 0 128)
        then lo (a.extractLsb' 0 128) else hi (a.extractLsb' 128 128)).card =
      (univ.filter fun x : Digest × Digest => if good x.1 ∨ TopChoice.blocked x.1 then lo x.1 else hi x.2).card := by
    refine Finset.card_equiv TopChoice.splitEquiv fun a => ?_
    simp only [mem_filter, mem_univ, true_and, TopChoice.splitEquiv_apply, TopChoice.lowHalf,
      TopChoice.highHalf]
  rw [he, DualHalf.card_mode (fun v => good v ∨ TopChoice.blocked v) lo hi (fun d h => Or.inl (hlo d h)),
    Fintype.card_bitVec]
  unfold TopChoice.freeCount
  norm_num

/-- The e7b top selection count at credit `c ≥ floor ≥ 19`: weight `2^128` through LOW (credit `c - 3`),
`topHighWeight` through HIGH (credit `c`). -/
theorem selected_top_path_card (floor c : Nat) (hf : 19 ≤ floor) (hc : floor ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      topWordCount (c - 3) * 2^128 + topHighWeight * topWordCount c := by
  have he : (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) =
      (univ.filter fun a : HashOutput => if topGood (a.extractLsb' 0 128) ∨ TopChoice.blocked (a.extractLsb' 0 128)
        then accepted 0 (floor - 3) (fun ds => CanonicalPolicy.credit 0 false ds + 3 = c) (a.extractLsb' 0 128)
        else accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) (a.extractLsb' 128 128)) :=
    Finset.filter_congr fun a _ => top_decoder_event floor c (by omega) a
  have hlo : (univ.filter (accepted 0 (floor - 3) (fun ds => CanonicalPolicy.credit 0 false ds + 3 = c))).card =
      topWordCount (c - 3) := by
    have hq : (univ.filter (accepted 0 (floor - 3) (fun ds => CanonicalPolicy.credit 0 false ds + 3 = c))) =
        univ.filter (accepted 0 (floor - 3) (fun ds => CanonicalPolicy.credit 0 false ds = c - 3)) := by
      apply Finset.filter_congr
      intro v _
      unfold accepted
      cases CanonicalPolicy.producerDecodeAt 0 (floor - 3) false v with
      | none => rfl
      | some ds => simp only; omega
    rw [hq, accepted_top_credit_card (floor - 3) (c - 3) (by omega)]
  have hhi : (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c))).card =
      topWordCount c := accepted_top_credit_card floor c hc
  have hfree : TopChoice.freeCount topGood = topHighWeight := freeCount_eq_compl
  rw [he, card_choose_path_generic topGood _ _ (fun d h => accepted_topGood (by omega) h), hlo, hhi, hfree]

/-- The lower decoder event splits by the selected half. -/
theorem lower_decoder_event (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (answer : HashOutput) :
    (∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c) ↔
      (if lowerSpare (answer.extractLsb' 0 128) then
        accepted lay (floor - 4) (fun ds => CanonicalPolicy.credit lay false ds + 4 = c) (answer.extractLsb' 0 128)
      else accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = c) (answer.extractLsb' 128 128)) := by
  have hsel : lowSelected lay answer = decide (lowerSpare (answer.extractLsb' 0 128)) := by
    simp [lowSelected, hl]
  have hword : encodingAnswer lay answer =
      if lowerSpare (answer.extractLsb' 0 128) then answer.extractLsb' 0 128 else answer.extractLsb' 128 128 := by
    simp only [encodingAnswer, if_neg hl, DualHalf.select, DualHalf.selectPair]
  unfold CanonicalPolicy.producerDecodeOut
  rw [hsel, hword]
  by_cases hs : lowerSpare (answer.extractLsb' 0 128)
  · simp only [hs, if_true, decide_true, accepted_iff, producerDecodeAt_lower_true lay hl, credit_lower_true lay hl]
    constructor
    · rintro ⟨⟨ds, l⟩, hd, hc⟩
      obtain ⟨ds', hd', he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ds', hd', by simpa [credit_lower_true lay hl] using hc⟩
    · rintro ⟨ds, hd, hc⟩
      exact ⟨(ds, true), by rw [hd]; rfl, by simpa [credit_lower_true lay hl] using hc⟩
  · simp only [hs, if_false, decide_false, accepted_iff]
    constructor
    · rintro ⟨⟨ds, l⟩, hd, hc⟩
      obtain ⟨ds', hd', he⟩ := Option.map_eq_some_iff.mp hd
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ds', hd', hc⟩
    · rintro ⟨ds, hd, hc⟩
      exact ⟨(ds, false), by rw [hd]; rfl, hc⟩

/-- Raw lower word count at reward `r` (all floors below `r`). -/
noncomputable def lowerWordCount (r : Nat) : Nat :=
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧ SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = r).card

theorem accepted_floor_le {lay : Layer} {floor : Nat} {P : List Nat → Prop} {v : Digest}
    (h : accepted lay floor P v) : ∃ ds, floor ≤ CanonicalPolicy.credit lay false ds ∧ P ds := by
  obtain ⟨ds, hd, hp⟩ := (accepted_iff lay floor P v).mp h
  exact ⟨ds, CanonicalPolicy.producerDecodeAt_credit hd, hp⟩

theorem lower_low_count (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) :
    (univ.filter (accepted lay (floor - 4) (fun ds => CanonicalPolicy.credit lay false ds + 4 = c))).card =
      if 4 ≤ c then lowerWordCount (c - 4) else 0 := by
  split_ifs with hc
  · have he : (univ.filter (accepted lay (floor - 4) (fun ds => CanonicalPolicy.credit lay false ds + 4 = c))) =
        univ.filter (accepted lay (floor - 4) (fun ds => CanonicalPolicy.credit lay false ds = c - 4)) := by
      apply Finset.filter_congr
      intro v _
      unfold accepted
      cases CanonicalPolicy.producerDecodeAt lay (floor - 4) false v with
      | none => rfl
      | some ds => simp only; omega
    rw [he, accepted_lower_credit_card_all lay hl (floor - 4) (c - 4) (by omega)]
    rfl
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro v _ h
    obtain ⟨ds, _, hp⟩ := accepted_floor_le h
    omega

theorem lower_high_count (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) :
    (univ.filter (accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = c))).card =
      lowerWordCount c :=
  accepted_lower_credit_card_all lay hl floor c hf

/-- Path-aware lower selection count: weight `2^128` through LOW (credit + 4), `3 * 2^126` through HIGH. -/
theorem selected_lower_path_card (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card =
      (if 4 ≤ c then lowerWordCount (c - 4) else 0) * 2^128 + 3 * 2^126 * lowerWordCount c := by
  have he : (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card =
      (univ.filter fun x : Digest × Digest => if lowerSpare x.1 then
        accepted lay (floor - 4) (fun ds => CanonicalPolicy.credit lay false ds + 4 = c) x.1
      else accepted lay floor (fun ds => CanonicalPolicy.credit lay false ds = c) x.2).card := by
    refine Finset.card_equiv TopChoice.splitEquiv fun a => ?_
    simp only [mem_filter, mem_univ, true_and, TopChoice.splitEquiv_apply, TopChoice.lowHalf,
      TopChoice.highHalf]
    exact lower_decoder_event lay hl floor c a
  rw [he, DualHalf.card_mode_lower _ _ (fun d h => accepted_lowerSpare lay hl _ _ d h),
    lower_low_count lay hl floor c hf, lower_high_count lay hl floor c hf]

theorem selected_path_card_zero_of_lt (lay : Layer) (floor c : Nat) (hc : c < floor) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  rintro answer _ ⟨⟨ds, l⟩, hd, hcr⟩
  have := CanonicalPolicy.producerDecodeOut_credit hd
  simp only at hcr
  omega

end ClaudeWCT.W9.T3.ProducerV5.Canonical

#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.selected_lower_path_card
#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.topFreeCount_eq
#print axioms ClaudeWCT.W9.T3.ProducerV5.Canonical.selected_top_path_card
