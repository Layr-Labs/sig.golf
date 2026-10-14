import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.Numerics.LowerZeroCreditCount
import SigGolfCandidate.ClaudeWCT.Numerics.TopCreditCount
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.CompletenessV5

namespace SigGolfResearch.NonbinaryTop.EffectiveCounting
open scoped BigOperators
open Codec Finset Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 100000
set_option Elab.async false
set_option linter.constructorNameAsVariable false

/-- Safe leaf-buffer copies are local to a triple, plus the first top digit. -/
def copies5 (first : Bool) (d : Triple5) : Nat :=
  (if first && decide ((d 0).val = 4) then 1 else 0) +
  (if (d 0).val = 4 ∧ (d 1).val = 4 then 1 else 0) +
  (if (d 1).val = 4 ∧ (d 2).val = 4 then 1 else 0)
def copies8 (d : Triple8) : Nat :=
  (if (d 0).val = 7 ∧ (d 1).val = 7 then 1 else 0) +
  (if (d 1).val = 7 ∧ (d 2).val = 7 then 1 else 0)
def hasPenalty (q : Fin 17) : Bool := decide (q.val ≠ 9 ∧ q.val < 13)
/-- A penalized group's extra one shifts the global signed score by twelve. -/
def score5 (first penalized : Bool) (d : Triple5) : Nat :=
  CreditCounting.credit5 d + 4 * copies5 first d +
    if penalized then (if tripleSum5 d < 3 then 0 else 1) else 0
def score8 (d : Triple8) : Nat := CreditCounting.credit8 d + 4 * copies8 d
def score (w : Codec.Word) : Nat :=
  (∑ q : Fin 17, score5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) + score8 w.2
def stat5 (first penalized : Bool) (d : Triple5) : Nat :=
  256 * tripleSum5 d + score5 first penalized d
def stat8 (d : Triple8) : Nat := 256 * tripleSum8 d + score8 d
def stat (w : Codec.Word) : Nat :=
  (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) + stat8 w.2

theorem stat_eq (w : Codec.Word) : stat w = 256 * weight w + score w := by
  simp only [stat, stat5, stat8, weight, score, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem score5_le (first penalized : Bool) (d : Triple5) :
    score5 first penalized d ≤ 12 + if first then 4 else 0 := by
  revert first penalized d
  decide +kernel

theorem score8_le (d : Triple8) : score8 d ≤ 11 := by
  have hc := CreditCounting.credit8_le d
  have hs : copies8 d ≤ 2 := by unfold copies8; split_ifs <;> omega
  unfold score8
  omega

theorem score_le (w : Codec.Word) : score w ≤ 219 := by
  have hs : (∑ q : Fin 17, score5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) ≤
      ∑ q : Fin 17, (12 + if q.val = 0 then 4 else 0) := by
    apply Finset.sum_le_sum
    intro q _
    simpa using score5_le (decide (q.val = 0)) (hasPenalty q) (w.1 q)
  have hbound : (∑ q : Fin 17, (12 + if q.val = 0 then 4 else 0)) = 208 := by
    decide +kernel
  have ht := score8_le w.2
  rw [hbound] at hs
  unfold score
  omega

def group5 (y : Nat) (first penalized : Bool) : Nat := ∑ d : Triple5, y ^ stat5 first penalized d
def group8 (y : Nat) : Nat := ∑ d : Triple8, y ^ stat8 d

theorem weighted_words (y : Nat) :
    (∑ w : Codec.Word, y ^ stat w) =
      group5 y true true * group5 y false true ^ 11 * group5 y false false ^ 5 * group8 y := by
  rw [Fintype.sum_prod_type]
  simp only [stat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : Fin 17 → Triple5,
      y ^ (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (f q))) =
      ∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q) := by
    simpa only [group5, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 17) (d : Triple5) =>
        y ^ stat5 (decide (q.val = 0)) (hasPenalty q) d).symm
  rw [h]
  change (∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q)) * group8 y = _
  norm_num [Fin.prod_univ_succ, hasPenalty]
  ring_nf
  simp

def packed : Nat := group5 radix true true * group5 radix false true ^ 11 *
  group5 radix false false ^ 5 * group8 radix

theorem truncated_card (cut : Nat) (hc : 0 < cut) :
    (univ.filter fun w : Codec.Word => stat w < cut).card =
      (packed % radix ^ cut) % (radix - 1) := by
  classical
  unfold packed
  rw [← weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ stat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

theorem card_model_of_check (n : Nat)
    (h : (packed % radix ^ 37376) % (radix - 1) -
      (packed % radix ^ 37153) % (radix - 1) = n) :
    (univ.filter fun w : Codec.Word => weight w = 145 ∧ 33 ≤ score w).card = n := by
  classical
  have hs : (univ.filter fun w : Codec.Word => weight w = 145 ∧ 33 ≤ score w) =
      (univ.filter fun w : Codec.Word => stat w < 37376) \
        (univ.filter fun w : Codec.Word => stat w < 37153) := by
    ext w
    have hc := score_le w
    have he := stat_eq w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    omega
  rw [hs, card_sdiff_of_subset]
  · rw [truncated_card _ (by decide), truncated_card _ (by decide), h]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega

end SigGolfResearch.NonbinaryTop.EffectiveCounting
namespace SigGolfResearch.NonbinaryTop.EffectiveCounting
open Finset Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 100000
set_option Elab.async false
set_option linter.constructorNameAsVariable false

def count : Nat := 83400240069434534984140569709320435

theorem exact_packed_count :
    (packed % radix ^ 37376) % (radix - 1) -
      (packed % radix ^ 37153) % (radix - 1) = count := by
  decide +kernel

theorem card_model :
    (univ.filter fun w : Codec.Word => weight w = 145 ∧ 33 ≤ score w).card = count :=
  card_model_of_check count exact_packed_count


/-- The half gate is the high bit of top chain 52. -/
def gateWord (w : Codec.Word) : Prop := 4 ≤ (w.2 1).val
instance (w : Codec.Word) : Decidable (gateWord w) := inferInstanceAs (Decidable (4 ≤ (w.2 1).val))
def gateStat8 (d : Triple8) : Nat := stat8 d + 65536 * if 4 ≤ (d 1).val then 1 else 0
def gateStat (w : Codec.Word) : Nat :=
  (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) + gateStat8 w.2

theorem gateStat_eq (w : Codec.Word) :
    gateStat w = 256 * weight w + score w + 65536 * if gateWord w then 1 else 0 := by
  have h := stat_eq w
  by_cases hg : gateWord w
  · have hg' : 4 ≤ (w.2 1).val := hg
    simp only [gateStat, gateStat8, if_pos hg', if_pos hg]
    simpa only [stat, Nat.add_assoc] using congrArg (fun n : Nat => n + 65536) h
  · have hg' : ¬4 ≤ (w.2 1).val := hg
    simp only [gateStat, gateStat8, if_neg hg', if_neg hg, Nat.mul_zero, Nat.add_zero]
    exact h

theorem weight_le_225 (w : Codec.Word) : weight w ≤ 225 := by
  have h5 (d : Triple5) : tripleSum5 d ≤ 12 := by revert d; decide +kernel
  have h8 (d : Triple8) : tripleSum8 d ≤ 21 := by revert d; decide +kernel
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin 17))) => h5 (w.1 q))
  have ht := h8 w.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  unfold weight
  omega

def gateGroup8 (y : Nat) : Nat := ∑ d : Triple8, y ^ gateStat8 d
def gatePacked : Nat := group5 radix true true * group5 radix false true ^ 11 *
  group5 radix false false ^ 5 * gateGroup8 radix

theorem gate_weighted_words (y : Nat) :
    (∑ w : Codec.Word, y ^ gateStat w) =
      group5 y true true * group5 y false true ^ 11 * group5 y false false ^ 5 * gateGroup8 y := by
  rw [Fintype.sum_prod_type]
  simp only [gateStat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : Fin 17 → Triple5,
      y ^ (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (f q))) =
      ∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q) := by
    simpa only [group5, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 17) (d : Triple5) =>
        y ^ stat5 (decide (q.val = 0)) (hasPenalty q) d).symm
  rw [h]
  change (∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q)) * gateGroup8 y = _
  norm_num [Fin.prod_univ_succ, hasPenalty]
  ring_nf
  simp

theorem gate_truncated_card (cut : Nat) (hc : 0 < cut) :
    (univ.filter fun w : Codec.Word => gateStat w < cut).card =
      (gatePacked % radix ^ cut) % (radix - 1) := by
  classical
  unfold gatePacked
  rw [← gate_weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ gateStat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

def gateCount : Nat := 63440602704496645076755857690454972

theorem gate_exact_packed_count :
    (gatePacked % radix ^ 102912) % (radix - 1) -
      (gatePacked % radix ^ 102689) % (radix - 1) = gateCount := by
  decide +kernel

theorem gate_card_model :
    (univ.filter fun w : Codec.Word => weight w = 145 ∧ 33 ≤ score w ∧ gateWord w).card = gateCount := by
  classical
  have hs : (univ.filter fun w : Codec.Word => weight w = 145 ∧ 33 ≤ score w ∧ gateWord w) =
      (univ.filter fun w : Codec.Word => gateStat w < 102912) \
        (univ.filter fun w : Codec.Word => gateStat w < 102689) := by
    ext w
    have hc := score_le w
    have hw := weight_le_225 w
    have he := gateStat_eq w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    by_cases hg : gateWord w <;> simp [hg] at he ⊢ <;> omega
  rw [hs, card_sdiff_of_subset]
  · rw [gate_truncated_card _ (by decide), gate_truncated_card _ (by decide), gate_exact_packed_count]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega

end SigGolfResearch.NonbinaryTop.EffectiveCounting

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
      ClaudeWCT.WCT9.producerZeroBound, producerRankBound, false_or, filter_zero_count,
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
theorem wordCredit_top (v : Digest) : wordCredit 0 (dataDigits 0 v) = topCredit v := by
  unfold wordCredit topCredit
  rw [show chainCount 0 = 54 from rfl, filter_length_eq_sum]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < 54 := List.mem_range.mp hi
  have hg : (dataDigits 0 v).getD i 0 = coreDigit 0 v i := by
    simp [dataDigits, dataCount, hi']
  rw [hg]
  by_cases h51 : i < 51
  · simp only [maxDigit, h51, if_true]
    split_ifs <;> simp_all
  · simp only [maxDigit, h51, if_true, if_false]
    split_ifs <;> simp_all
theorem decode_top_eq (v : Digest) : decode 0 v = if 2 ^ 128 ≤ v.toNat then none else
    if topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0 then some (dataDigits 0 v) else none := by
  simp only [decode, encodedBits, if_true]
  by_cases h1 : 2 ^ 128 ≤ v.toNat
  · simp
  · simp only [h1, if_false]
    by_cases h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0
    · simp [h2.1, h2.2]
    · rw [if_neg h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [if_neg h2]
theorem producerDecode_top_isSome_iff (v : Digest) :
    (producerDecode 0 v).isSome ↔ ∃ w, Decoder.parse 17 (topFlip v).toNat = some w ∧
      Counting.weight w = target 0 ∧ producerFloor 0 + ClaudeWCT.WCT9.dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) ≤
        CreditCounting.credit w + 4 * ClaudeWCT.WCT9.savedCopies 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) := by
  unfold producerDecode
  rw [decode_top_eq]
  simp only [producerZeroBound, producerRankBound, eq_self_iff_true, true_or, and_true]
  constructor
  · intro h
    by_cases h1 : 2 ^ 128 ≤ v.toNat
    · rw [if_pos h1] at h; simp at h
    · rw [if_neg h1] at h
      by_cases h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0
      · rw [if_pos h2] at h
        simp only at h
        split_ifs at h with h3
        · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
            ((SigGolfCandidate.T3.Nonbinary.parse_top_isSome_iff v).mpr h2.1)
          refine ⟨w, hw, ?_, ?_⟩
          · rw [← SigGolfCandidate.T3.Nonbinary.wordDigits_sum, ← SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw]
            exact h2.2
          · rw [← SigGolfCandidate.T3.Nonbinary.topCredit_parse hw, ← wordCredit_top,
              ← SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw]
            exact h3
        · simp at h
      · rw [if_neg h2] at h; simp at h
  · rintro ⟨w, hw, hweight, hcredit⟩
    have hp := (SigGolfCandidate.T3.Nonbinary.parse_top_isSome_iff v).mp (by rw [hw]; rfl)
    have h2 : topRanksValid v = true ∧ (dataDigits 0 v).sum = target 0 := by
      refine ⟨hp, ?_⟩
      rw [SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw, SigGolfCandidate.T3.Nonbinary.wordDigits_sum]
      exact hweight
    rw [if_neg (Nat.not_le.mpr v.isLt), if_pos h2]
    simp only
    rw [if_pos (by rw [wordCredit_top, SigGolfCandidate.T3.Nonbinary.topCredit_parse hw,
      SigGolfCandidate.T3.Nonbinary.dataDigits_parse hw]; exact hcredit)]
    rfl
theorem card_producer_top (T f n : ℕ) (hT : target 0 = T) (hf : producerFloor 0 = f)
    (hn : (univ.filter fun w : Codec.Word => Counting.weight w = T ∧
      f + ClaudeWCT.WCT9.dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) ≤
        CreditCounting.credit w + 4 * ClaudeWCT.WCT9.savedCopies 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w)).card = n) :
    (univ.filter fun v : Digest => (producerDecode 0 v).isSome).card = n := by
  classical
  rw [← hn, ← ClaudeWCT.Numerics.TopCredit.card_parse_filter]
  refine Finset.card_equiv topFlipEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [producerDecode_top_isSome_iff, hT, hf]
  rfl
noncomputable def producerCount (lay : Layer) : ℕ :=
  (univ.filter fun v : Digest => (producerDecode lay v).isSome).card

def producerCountUpper (lay : Layer) : ℕ :=
  ![91088036708222302737139366458447855,
    58782472808233403853217196834292020,
    46428947739236900406585478288441112,
    46428947739236900406585478288441112] lay

theorem producerCount_le_upper (lay : Layer) : producerCount lay ≤ producerCountUpper lay := by
  have hlo (l : Layer) (hl : l ≠ 0) : producerCount l ≤ EncodingCounting.rawAcceptedCount l := by
    have hc : (univ.filter fun v : Digest => (decode l v).isSome).card =
        EncodingCounting.rawAcceptedCount l := by
      rw [← Fintype.card_subtype, Fintype.card_congr (EncodingCounting.acceptedDigestEquiv l hl),
        EncodingCounting.accepted_words_count]
    rw [← hc]
    apply Finset.card_le_card
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨ds, hd⟩ := Option.isSome_iff_exists.mp hv
    exact Option.isSome_iff_exists.mpr ⟨ds, ClaudeWCT.WCT9.producerDecode_decode hd⟩
  fin_cases lay
  · change (univ.filter fun v : Digest => (producerDecode 0 v).isSome).card ≤ Counting.count
    rw [card_producer_top 145 21 _ rfl rfl rfl]
    rw [← Counting.accepted_card]
    apply Finset.card_le_card
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact hw.1
  · exact hlo 1 (by decide)
  · exact hlo 2 (by decide)
  · exact hlo 3 (by decide)

theorem producerDecode_lowerSpare (lay : Layer) (hl : lay ≠ 0) (v : Digest)
    (hv : (producerDecode lay v).isSome) : lowerSpare v := by
  obtain ⟨ds, hd⟩ := Option.isSome_iff_exists.mp hv
  exact decode_lowerSpare hl (ClaudeWCT.WCT9.producerDecode_decode hd)

noncomputable def producerGateCount (lay : Layer) : ℕ :=
  (univ.filter fun v : Digest => (producerDecode lay v).isSome ∧ TopDualHalf.gate v).card

/-- Top selected density numerator; lower numerators retain their original meaning. -/
noncomputable def producerSelectedCount (lay : Layer) : ℕ :=
  if lay = 0 then producerCount lay + 2 * producerGateCount lay else producerCount lay

section SelectedCardinality
attribute [local irreducible] producerCount producerGateCount producerSelectedCount

theorem producer_top_answer_card :
    (univ.filter fun a : HashOutput => (producerEncodingDecode 0 a).isSome).card =
      (univ.filter fun a : HashOutput => (producerDecode 0 (TopDualHalf.select a)).isSome).card := by
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and, producerEncodingDecode,
    ClaudeWCT.WCT9.encodingAnswer, if_pos rfl, if_true]

theorem producer_lower_answer_card (lay : Layer) (hl : lay ≠ 0) :
    (univ.filter fun a : HashOutput => (producerEncodingDecode lay a).isSome).card =
      (univ.filter fun a : HashOutput => (producerDecode lay (DualHalf.select a)).isSome).card := by
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and, producerEncodingDecode,
    ClaudeWCT.WCT9.encodingAnswer, if_neg hl]

theorem producer_gate_card (lay : Layer) :
    (univ.filter fun value : Digest =>
      (producerDecode lay value).isSome ∧ TopDualHalf.gate value).card = producerGateCount lay := by
  unfold producerGateCount
  apply congrArg Finset.card
  ext value
  simp only [mem_filter, mem_univ, true_and]

theorem producer_raw_card (lay : Layer) :
    (univ.filter fun value : Digest =>
      (producerDecode lay value).isSome).card = producerCount lay := by
  unfold producerCount
  apply congrArg Finset.card
  ext value
  simp only [mem_filter, mem_univ, true_and]

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

theorem producer_top_selected_card :
    (univ.filter fun a : HashOutput => (producerDecode 0 (TopDualHalf.select a)).isSome).card =
      (producerCount 0 + 2 * producerGateCount 0) * 2^127 := by
  exact selected_top_count_transport (fun value => (producerDecode 0 value).isSome)
    (producerCount 0) (producerGateCount 0) (producer_raw_card 0) (producer_gate_card 0)

theorem producer_lower_selected_card (lay : Layer) (hl : lay ≠ 0) :
    (univ.filter fun a : HashOutput => (producerDecode lay (DualHalf.select a)).isSome).card =
      producerCount lay * (7 * 2^126) := by
  exact selected_lower_count_transport (fun value => (producerDecode lay value).isSome)
    (producerCount lay) (producer_raw_card lay) (producerDecode_lowerSpare lay hl)

theorem producerSelectedCount_eq (lay : Layer) :
    producerSelectedCount lay =
      if lay = 0 then producerCount lay + 2 * producerGateCount lay else producerCount lay := by
  unfold producerSelectedCount
  rfl

theorem producerSelectedCount_lower (lay : Layer) (hl : lay ≠ 0) :
    producerSelectedCount lay = producerCount lay :=
  (producerSelectedCount_eq lay).trans (if_neg hl)

theorem selected_count_cases (c n g s : Layer → Nat)
    (hs : ∀ lay, s lay = if lay = 0 then n lay + 2 * g lay else n lay)
    (h0 : c 0 = (n 0 + 2 * g 0) * 2^127)
    (hlo : ∀ lay, lay ≠ 0 → c lay = n lay * (7 * 2^126)) (lay : Layer) :
    c lay = s lay * (if lay = 0 then 2^127 else 7 * 2^126) := by
  rw [hs]
  by_cases hl : lay = 0
  · subst lay
    simpa only [if_pos rfl, if_true] using h0
  · simpa only [if_neg hl] using hlo lay hl

theorem card_producerEncodingDecode (lay : Layer) :
    (univ.filter fun a : HashOutput => (producerEncodingDecode lay a).isSome).card =
      producerSelectedCount lay * (if lay = 0 then 2^127 else 7*2^126) := by
  exact selected_count_cases
    (fun lay => (univ.filter fun a : HashOutput => (producerEncodingDecode lay a).isSome).card)
    producerCount producerGateCount producerSelectedCount producerSelectedCount_eq
    (producer_top_answer_card.trans producer_top_selected_card)
    (fun l hl => (producer_lower_answer_card l hl).trans (producer_lower_selected_card l hl)) lay

end SelectedCardinality

theorem producer_uniform_probability (lay : Layer) :
    Pr[fun answer => (producerEncodingDecode lay answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (producerSelectedCount lay : ENNReal) * (if lay = 0 then 2^127 else 7*2^126) / 2^256 := by
  classical
  rw [probEvent_uniformSample, card_producerEncodingDecode]
  simp only [Fintype.card_bitVec, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ite]

noncomputable def producerRate (lay : Layer) : ℝ :=
  (producerSelectedCount lay : ℝ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256

theorem producerRate_nonneg (lay : Layer) : 0 ≤ producerRate lay := by
  unfold producerRate
  split_ifs <;> positivity

theorem producerRate_le_one (lay : Layer) : producerRate lay ≤ 1 := by
  have hc := Finset.card_filter_le (Finset.univ : Finset HashOutput)
    (fun a => (producerEncodingDecode lay a).isSome)
  rw [card_producerEncodingDecode, Finset.card_univ, Fintype.card_bitVec] at hc
  unfold producerRate
  apply (div_le_one (by positivity : (0 : ℝ) < 2^256)).2
  exact_mod_cast hc

theorem producer_failMass (lay : Layer) :
    failMass (producerEncodingDecode lay) = ENNReal.ofReal (1 - producerRate lay) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, producer_uniform_probability,
    ENNReal.ofReal_sub 1 (producerRate_nonneg lay), ENNReal.ofReal_one]
  congr 1
  unfold producerRate
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  congr 2
  split_ifs <;> norm_num


open scoped BigOperators
open SigGolfResearch.NonbinaryTop.EffectiveCounting

theorem topWord_getD (w : Codec.Word) (i : Nat) (hi : i < 54) :
    (SigGolfCandidate.T3.Nonbinary.wordDigits w).getD i 0 =
      if h : i < 51 then (w.1 ⟨i / 3, by omega⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val
      else (w.2 ⟨(i - 51) % 3, Nat.mod_lt _ (by decide)⟩).val := by
  interval_cases i <;> rfl

attribute [local irreducible] SigGolfCandidate.T3.Nonbinary.wordDigits

def topCopyFlag (w : Codec.Word) (i : Nat) : Nat :=
  if ClaudeWCT.WCT9.safeZeroCopy 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) i then 1 else 0

theorem topCopyFlag_block (w : Codec.Word) (q : Fin 17) :
    ([3*q.val, 3*q.val+1, 3*q.val+2].map (topCopyFlag w)).sum =
      copies5 (decide (q.val = 0)) (w.1 q) := by
  fin_cases q <;>
    simp [topCopyFlag, ClaudeWCT.WCT9.safeZeroCopy, maxDigit, topWord_getD, copies5, and_comm, -List.getD_eq_getElem?_getD]
  all_goals split_ifs <;> omega

theorem topCopyFlag_tail (w : Codec.Word) :
    ([51,52,53].map (topCopyFlag w)).sum = copies8 w.2 := by
  simp [topCopyFlag, ClaudeWCT.WCT9.safeZeroCopy, maxDigit, topWord_getD, copies8, and_comm, -List.getD_eq_getElem?_getD]
  all_goals split_ifs <;> omega

theorem savedCopies_top_word (w : Codec.Word) :
    ClaudeWCT.WCT9.savedCopies 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) =
      (∑ q : Fin 17, copies5 (decide (q.val = 0)) (w.1 q)) + copies8 w.2 := by
  unfold ClaudeWCT.WCT9.savedCopies
  rw [filter_length_eq_sum]
  rw [show chainCount 0 = 54 from rfl]
  simp only [decide_eq_true_eq]
  rw [show (fun i => if ClaudeWCT.WCT9.safeZeroCopy 0
      (SigGolfCandidate.T3.Nonbinary.wordDigits w) i then (1 : Nat) else 0) = topCopyFlag w from rfl]
  have hi : List.range 54 =
      (List.ofFn fun q : Fin 17 => [3*q.val, 3*q.val+1, 3*q.val+2]).flatten ++ [51,52,53] := by
    decide +kernel
  rw [hi, List.map_append, List.sum_append, topCopyFlag_tail]
  apply congrArg (fun n : Nat => n + copies8 w.2)
  rw [List.map_flatten, List.sum_flatten]
  simp only [List.map_map, List.map_ofFn, Function.comp_def, topCopyFlag_block, List.sum_ofFn]

theorem dispatchPenalty_top_word (w : Codec.Word) :
    ClaudeWCT.WCT9.dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) =
      ∑ q : Fin 17, if hasPenalty q && decide (Counting.tripleSum5 (w.1 q) < 3) then 1 else 0 := by
  unfold ClaudeWCT.WCT9.dispatchPenalty
  rw [if_pos rfl]
  unfold ClaudeWCT.WCT9.topDispatchPenalty
  rw [filter_length_eq_sum]
  simp only [Fin.sum_univ_succ]
  simp [SigGolfCandidate.T3.Nonbinary.wordDigits, List.ofFn_succ,
    List.range_succ, hasPenalty, Counting.tripleSum5, Fin.sum_univ_succ, Nat.add_assoc]


theorem top_score_add_penalty (w : Codec.Word) :
    EffectiveCounting.score w +
      ClaudeWCT.WCT9.dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) =
        CreditCounting.credit w +
          4 * ClaudeWCT.WCT9.savedCopies 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) + 12 := by
  rw [savedCopies_top_word, dispatchPenalty_top_word]
  have hs (q : Fin 17) :
      score5 (decide (q.val = 0)) (hasPenalty q) (w.1 q) +
        (if hasPenalty q && decide (Counting.tripleSum5 (w.1 q) < 3) then 1 else 0) =
      CreditCounting.credit5 (w.1 q) + 4 * copies5 (decide (q.val = 0)) (w.1 q) +
        (if hasPenalty q then 1 else 0) := by
    unfold score5
    cases hp : hasPenalty q <;> by_cases ht : Counting.tripleSum5 (w.1 q) < 3 <;> simp [hp, ht]
  have h := Finset.sum_congr rfl (fun q (_ : q ∈ (Finset.univ : Finset (Fin 17))) => hs q)
  have h12 : (∑ q : Fin 17, if hasPenalty q then (1 : Nat) else 0) = 12 := by decide +kernel
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h12] at h
  unfold EffectiveCounting.score EffectiveCounting.score8 CreditCounting.credit
  omega

theorem top_effective_score_iff (w : Codec.Word) :
    33 ≤ EffectiveCounting.score w ↔
      21 + ClaudeWCT.WCT9.dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) ≤
        CreditCounting.credit w + 4 * ClaudeWCT.WCT9.savedCopies 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) := by
  have h := top_score_add_penalty w
  omega

theorem producerCount_top_exact : producerCount 0 = 83400240069434534984140569709320435 := by
  change (univ.filter fun v : Digest => (producerDecode 0 v).isSome).card = _
  apply card_producer_top 145 21 _ rfl rfl
  convert EffectiveCounting.card_model using 1
  · exact congrArg Finset.card (filter_congr fun w _ => by rw [top_effective_score_iff])
  · rfl


theorem gate_of_top_parse {v : Digest} {w : Codec.Word}
    (hw : Decoder.parse 17 (topFlip v).toNat = some w) :
    TopDualHalf.gate v ↔ EffectiveCounting.gateWord w := by
  have hd := SigGolfCandidate.T3.Nonbinary.coreDigit_parse8 hw (1 : Fin 3)
  change topCode v / 2 ^ 125 % 8 = (w.2 1).val at hd
  rw [topCode_div_high v 125 (by decide)] at hd
  have hv := v.isLt
  unfold TopDualHalf.gate EffectiveCounting.gateWord
  norm_num at hd hv ⊢
  omega

theorem producerGateCount_top_exact :
    producerGateCount 0 = 63440602704496645076755857690454972 := by
  classical
  rw [show (63440602704496645076755857690454972 : Nat) = EffectiveCounting.gateCount from rfl,
    ← EffectiveCounting.gate_card_model, ← ClaudeWCT.Numerics.TopCredit.card_parse_filter]
  unfold producerGateCount
  refine Finset.card_equiv topFlipEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and]
  change ((producerDecode 0 v).isSome ∧ TopDualHalf.gate v) ↔
    ∃ w, Decoder.parse 17 (topFlip v).toNat = some w ∧
      Counting.weight w = 145 ∧ 33 ≤ EffectiveCounting.score w ∧ EffectiveCounting.gateWord w
  rw [producerDecode_top_isSome_iff]
  constructor
  · rintro ⟨⟨w, hw, ht, hc⟩, hg⟩
    exact ⟨w, hw, ht, (top_effective_score_iff w).mpr hc, (gate_of_top_parse hw).mp hg⟩
  · rintro ⟨w, hw, ht, hc, hg⟩
    exact ⟨⟨w, hw, ht, (top_effective_score_iff w).mp hc⟩, (gate_of_top_parse hw).mpr hg⟩

theorem producerSelectedCount_top_exact :
    producerSelectedCount 0 = 210281445478427825137652285090230379 := by
  simp only [producerSelectedCount, if_pos rfl, producerCount_top_exact, producerGateCount_top_exact]
  norm_num

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
def producerCountLower (lay : Layer) : Nat :=
  ![210281445478427825137652285090230379,
    54408112790925688753987891000775297,
    44444210514614632453013305786840214,
    44444210514614632453013305786840214] lay

theorem producerCount_lower_model (l : Layer) (hl : l ≠ 0) :
    SigGolfResearch.LowerEffectiveCounting.count (target l) (ClaudeWCT.WCT9.producerFloor l) ≤
      producerCount l :=
  card_producer_lower l hl _ (SigGolfResearch.LowerEffectiveCounting.card_lowerProducerAccept_model l hl)

section SelectedLowerBounds
attribute [local irreducible] producerCount producerGateCount producerSelectedCount

/-- Lower bounds for the selected-density numerators; the top includes its gated low-half contribution. -/
theorem producerCount_ge (lay : Layer) : producerCountLower lay ≤ producerSelectedCount lay := by
  fin_cases lay
  · exact le_of_eq producerSelectedCount_top_exact.symm
  · change producerCountLower (1 : Layer) ≤ producerSelectedCount (1 : Layer)
    have h := producerCount_lower_model 1 (by decide)
    change SigGolfResearch.LowerEffectiveCounting.count 201 10 ≤ _ at h
    rw [SigGolfResearch.LowerEffectiveCounting.exact_201] at h
    rw [producerSelectedCount_lower (1 : Layer) (by decide)]
    exact h
  · change producerCountLower (2 : Layer) ≤ producerSelectedCount (2 : Layer)
    have h := producerCount_lower_model 2 (by decide)
    change SigGolfResearch.LowerEffectiveCounting.count 202 9 ≤ _ at h
    rw [SigGolfResearch.LowerEffectiveCounting.exact_202] at h
    rw [producerSelectedCount_lower (2 : Layer) (by decide)]
    exact h
  · change producerCountLower (3 : Layer) ≤ producerSelectedCount (3 : Layer)
    have h := producerCount_lower_model 3 (by decide)
    change SigGolfResearch.LowerEffectiveCounting.count 202 9 ≤ _ at h
    rw [SigGolfResearch.LowerEffectiveCounting.exact_202] at h
    rw [producerSelectedCount_lower (3 : Layer) (by decide)]
    exact h

end SelectedLowerBounds

theorem producerRate_ge (lay : Layer) :
    (producerCountLower lay : ℝ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256 ≤ producerRate lay := by
  unfold producerRate
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast producerCount_ge lay)
  split_ifs <;> positivity

theorem producerRate_bounds (lay : Layer) : 1 / 8192 ≤ producerRate lay ∧ producerRate lay ≤ 1 := by
  refine ⟨?_, producerRate_le_one lay⟩
  have h := producerRate_ge lay
  fin_cases lay <;> norm_num [producerCountLower] at h ⊢ <;> linarith

theorem producer_uniform_probability_lower (lay : Layer) :
    (producerCountLower lay : ENNReal) * (if lay = 0 then 2^127 else 7*2^126) / 2^256 ≤
      Pr[fun answer => (producerEncodingDecode lay answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [producer_uniform_probability]
  apply ENNReal.div_le_div_right
  exact mul_le_mul' (by exact_mod_cast producerCount_ge lay) le_rfl

theorem ofReal_sample_count (n k : Nat) :
    ENNReal.ofReal (((n : ℚ) * k / 2^256 : ℚ) : ℝ) = (n : ENNReal) * k / 2^256 := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

theorem producer_failure_power_of_rate (lay : Layer) (fuel bits : Nat)
    (hrate : (bits : ℚ) * 0.6931471808 ≤ fuel *
      ((producerCountLower lay : ℚ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256)) :
    failMass (producerEncodingDecode lay) ^ fuel ≤ 1 / (2 : ENNReal) ^ bits := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _
    ((producerCountLower lay : ℚ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256)
  · split_ifs <;> positivity
  · fin_cases lay <;> norm_num [producerCountLower]
  · have hcast := ofReal_sample_count (producerCountLower lay)
      (if lay = 0 then 2^127 else 7*2^126)
    simp only [Nat.cast_ite, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hcast
    rw [hcast]
    exact producer_uniform_probability_lower lay
  · exact hrate

theorem producer_failure_power (lay : Layer) :
    failMass (producerEncodingDecode lay) ^ searchLimit lay ≤ 1 / (2 : ENNReal) ^ 600 := by
  apply producer_failure_power_of_rate lay (searchLimit lay) 600
  fin_cases lay <;> norm_num [producerCountLower, searchLimit, ClaudeWCT.WCT9.lowerSearchLimit, counterLimit]
end ClaudeWCT.W9.T3.ProducerV5

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3
open ClaudeWCT.WCT9
/-- A digit predicate after an arbitrary canonical producer floor. -/
def accepted (lay : Layer) (floor : Nat) (P : List Nat → Prop) (value : Digest) : Prop :=
  match CanonicalPolicy.producerDecodeAt lay floor value with
  | none => False
  | some digits => P digits
instance (lay : Layer) (floor : Nat) (P : List Nat → Prop) [DecidablePred P] :
    DecidablePred (accepted lay floor P) := fun value => by
  unfold accepted
  split <;> infer_instance

theorem accepted_iff (lay : Layer) (floor : Nat) (P : List Nat → Prop) (value : Digest) :
    accepted lay floor P value ↔
      ∃ digits, CanonicalPolicy.producerDecodeAt lay floor value = some digits ∧ P digits := by
  unfold accepted
  cases hd : CanonicalPolicy.producerDecodeAt lay floor value <;> simp

theorem accepted_lowerSpare (lay : Layer) (hl : lay ≠ 0) (floor : Nat)
    (P : List Nat → Prop) (value : Digest) (h : accepted lay floor P value) : lowerSpare value := by
  obtain ⟨digits, hd, _⟩ := (accepted_iff lay floor P value).mp h
  have hs := (CanonicalPolicy.producerDecodeAt_spec hd).1
  have hd' : decode (1 : Layer) value = some digits := by
    simpa only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] using hs
  exact decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hd'

theorem selected_top_card (floor : Nat) (P : List Nat → Prop) [DecidablePred P]
    (n g : Nat) (hn : (univ.filter (accepted 0 floor P)).card = n)
    (hg : (univ.filter fun value => accepted 0 floor P value ∧ TopDualHalf.gate value).card = g) :
    (univ.filter fun answer : HashOutput => accepted 0 floor P (encodingAnswer 0 answer)).card =
      (n + 2*g)*2^127 := by
  exact selected_top_count_transport (accepted 0 floor P) n g hn hg

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
      dispatchPenalty, wordCredit, savedCopies, safeZeroCopy, producerZeroBound, producerRankBound,
      chainCount, maxDigit]
end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

theorem accepted_top_parse (floor : Nat) (P : List Nat → Prop) (v : Digest) :
    accepted 0 floor P v ↔ ∃ w : Codec.Word,
      Decoder.parse 17 (topFlip v).toNat = some w ∧ Counting.weight w = 145 ∧
      floor + dispatchPenalty 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) ≤
        CanonicalPolicy.reward 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) ∧
      P (SigGolfCandidate.T3.Nonbinary.wordDigits w) := by
  rw [accepted_decode_iff]
  simp only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_pos rfl,
    producerZeroBound, producerRankBound, eq_self_iff_true, ite_true, true_or, true_and]
  rw [SigGolfCandidate.T3.Nonbinary.decode_top_eq_map]
  change (∃ digits,
    (((Decoder.parse 17 (topFlip v).toNat).filter fun w => decide (Counting.weight w = 145)).map
      SigGolfCandidate.T3.Nonbinary.wordDigits) = some digits ∧
      floor + dispatchPenalty 0 digits ≤ CanonicalPolicy.reward 0 digits ∧ P digits) ↔ _
  simp only [Option.map_eq_some_iff, Option.filter_eq_some_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨ds, ⟨w, ⟨hp, hw⟩, he⟩, hf, hP⟩
    subst ds
    exact ⟨w, hp, hw, hf, hP⟩
  · rintro ⟨w, hp, hw, hf, hP⟩
    exact ⟨_, ⟨w, ⟨hp, hw⟩, rfl⟩, hf, hP⟩

theorem accepted_top_credit_parse (floor credit : Nat) (v : Digest) :
    accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = credit) v ↔
      ∃ w : Codec.Word, Decoder.parse 17 (topFlip v).toNat = some w ∧
        Counting.weight w = 145 ∧ floor ≤ credit ∧ EffectiveCounting.score w = credit+12 := by
  rw [accepted_top_parse]
  apply exists_congr
  intro w
  by_cases hp : Decoder.parse 17 (topFlip v).toNat = some w
  · simp only [hp, true_and]
    have hword : wordCredit 0 (SigGolfCandidate.T3.Nonbinary.wordDigits w) = CreditCounting.credit w := by
      rw [← SigGolfCandidate.T3.Nonbinary.dataDigits_parse hp,
        ClaudeWCT.W9.T3.ProducerV5.wordCredit_top,
        SigGolfCandidate.T3.Nonbinary.topCredit_parse hp]
    have hscore := top_score_add_penalty w
    simp only [CanonicalPolicy.credit, CanonicalPolicy.reward, hword]
    omega
  · simp only [hp, false_and]
end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

theorem accepted_top_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = credit))).card =
      (univ.filter fun w : Codec.Word => Counting.weight w = 145 ∧
        EffectiveCounting.score w = credit+12).card := by
  classical
  rw [← ClaudeWCT.Numerics.TopCredit.card_parse_filter]
  refine Finset.card_equiv topFlipEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [accepted_top_credit_parse]
  simp only [hf, true_and]
  rfl

theorem accepted_top_gate_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter fun v => accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = credit) v ∧
      TopDualHalf.gate v).card =
      (univ.filter fun w : Codec.Word => Counting.weight w = 145 ∧
        EffectiveCounting.score w = credit+12 ∧ EffectiveCounting.gateWord w).card := by
  classical
  rw [← ClaudeWCT.Numerics.TopCredit.card_parse_filter]
  refine Finset.card_equiv topFlipEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [accepted_top_credit_parse]
  constructor
  · rintro ⟨⟨w, hp, hw, _, hc⟩, hg⟩
    exact ⟨w, hp, hw, hc, (gate_of_top_parse hp).mp hg⟩
  · rintro ⟨w, hp, hw, hc, hg⟩
    exact ⟨⟨w, hp, hw, hf, hc⟩, (gate_of_top_parse hp).mpr hg⟩

theorem selected_top_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter fun answer : HashOutput => accepted 0 floor
      (fun ds => CanonicalPolicy.credit 0 ds = credit) (encodingAnswer 0 answer)).card =
      ((univ.filter fun w : Codec.Word => Counting.weight w = 145 ∧
          EffectiveCounting.score w = credit+12).card +
       2*(univ.filter fun w : Codec.Word => Counting.weight w = 145 ∧
          EffectiveCounting.score w = credit+12 ∧ EffectiveCounting.gateWord w).card)*2^127 := by
  exact selected_top_card floor _ _ _ (accepted_top_credit_card floor credit hf)
    (accepted_top_gate_credit_card floor credit hf)

end ClaudeWCT.W9.T3.ProducerV5.Canonical
namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

theorem accepted_credit_floor {lay : Layer} {floor credit : Nat} {v : Digest}
    (h : accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = credit) v) :
    floor ≤ credit := by
  obtain ⟨ds, hd, hc⟩ := (accepted_iff lay floor _ v).mp h
  exact hc ▸ CanonicalPolicy.producerDecodeAt_credit hd

theorem accepted_top_credit_le {floor credit : Nat} {v : Digest}
    (h : accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = credit) v) : credit ≤ 207 := by
  obtain ⟨w, _, _, _, hs⟩ := (accepted_top_credit_parse floor credit v).mp h
  have hw := EffectiveCounting.score_le w
  omega

theorem selected_credit_card_zero_of_lt (lay : Layer) (floor credit : Nat) (hf : credit < floor) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay ds = credit) (encodingAnswer lay answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_credit_floor h
  omega

theorem selected_top_credit_card_zero_of_gt (floor credit : Nat) (hc : 207 < credit) :
    (univ.filter fun answer : HashOutput => accepted 0 floor
      (fun ds => CanonicalPolicy.credit 0 ds = credit) (encodingAnswer 0 answer)).card = 0 := by
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
    CanonicalPolicy.credit 1 (digits w) = score w := by
  simp only [CanonicalPolicy.credit, reward_lower_model, dispatchPenalty,
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
    simp only [producerZeroBound, show (1 : Layer) ≠ 0 by decide, false_or,
      filter_zero_count, digits_zeros] at hz
    exact ⟨w, he, hw, hf, hz, hP⟩
  · rintro ⟨w, he, hw, hf, hz, hP⟩
    subst v
    refine ⟨digits w, decode_encode_201 w hw, ?_, ?_, ?_, hP⟩
    · simpa only [dispatchPenalty, show (1 : Layer) ≠ 0 by decide, if_false,
        Nat.add_zero, reward_lower_model] using hf
    · simpa only [producerZeroBound, show (1 : Layer) ≠ 0 by decide, false_or,
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
    (univ.filter (accepted 1 floor (fun ds => CanonicalPolicy.credit 1 ds = credit))).card =
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
    CanonicalPolicy.credit lay ds = CanonicalPolicy.credit 1 ds := by
  fin_cases lay <;> simp_all [CanonicalPolicy.credit, CanonicalPolicy.reward,
    dispatchPenalty, wordCredit, savedCopies, safeZeroCopy, chainCount, maxDigit]

theorem accepted_lower_credit_eq_one (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat) (v : Digest) :
    accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = credit) v ↔
      accepted 1 floor (fun ds => CanonicalPolicy.credit 1 ds = credit) v := by
  rw [accepted_lower_eq_one lay hl]
  simp only [credit_lower_eq_one lay hl]

theorem accepted_lower_credit_card_all (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat)
    (hf : floor ≤ credit) :
    (univ.filter (accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = credit))).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        zeros w ≤ 5 ∧ weight w = 201 ∧ score w = credit).card := by
  rw [show (univ.filter (accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = credit))) =
      (univ.filter (accepted 1 floor (fun ds => CanonicalPolicy.credit 1 ds = credit))) by
        exact Finset.filter_congr fun v _ => accepted_lower_credit_eq_one lay hl floor credit v]
  exact accepted_lower_credit_card floor credit hf

theorem selected_lower_credit_card (lay : Layer) (hl : lay ≠ 0) (floor credit : Nat)
    (hf : floor ≤ credit) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay ds = credit) (encodingAnswer lay answer)).card =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        zeros w ≤ 5 ∧ weight w = 201 ∧ score w = credit).card * (7*2^126) := by
  exact selected_lower_card lay hl floor _ _ (accepted_lower_credit_card_all lay hl floor credit hf)

theorem accepted_lower_credit_le (lay : Layer) (hl : lay ≠ 0) {floor credit : Nat} {v : Digest}
    (h : accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = credit) v) : credit ≤ 117 := by
  have h1 := (accepted_lower_credit_eq_one lay hl floor credit v).mp h
  obtain ⟨w, _, _, _, _, hc⟩ := (accepted_lower_model floor _ v).mp h1
  rw [credit_lower_model] at hc
  exact hc ▸ SigGolfResearch.LowerEffectiveCounting.score_le w

theorem selected_lower_credit_card_zero_of_gt (lay : Layer) (hl : lay ≠ 0)
    (floor credit : Nat) (hc : 117 < credit) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay ds = credit) (encodingAnswer lay answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_lower_credit_le lay hl h
  omega

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem producerDecodeAt_top_credit_lt {floor : Nat} {value : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor value = some ds) :
    CanonicalPolicy.credit 0 ds < 220 := by
  have ha : accepted 0 floor (fun digits => CanonicalPolicy.credit 0 digits =
      CanonicalPolicy.credit 0 ds) value := (accepted_iff 0 floor _ value).mpr ⟨ds, h, rfl⟩
  have hb := accepted_top_credit_le ha
  omega

theorem producerDecodeAt_lower_credit_lt (lay : Layer) (hl : lay ≠ 0)
    {floor : Nat} {value : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt lay floor value = some ds) :
    CanonicalPolicy.credit lay ds < 128 := by
  have ha : accepted lay floor (fun digits => CanonicalPolicy.credit lay digits =
      CanonicalPolicy.credit lay ds) value := (accepted_iff lay floor _ value).mpr ⟨ds, h, rfl⟩
  have hb := accepted_lower_credit_le lay hl ha
  omega

#print axioms producerDecodeAt_top_credit_lt
#print axioms producerDecodeAt_lower_credit_lt
end ClaudeWCT.W9.T3.ProducerV5.Canonical
