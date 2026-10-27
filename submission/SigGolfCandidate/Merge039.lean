import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Fintype.BigOperators
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge031
import SigGolfCandidate.Merge032
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge036
import SigGolfCandidate.Merge037
import SigGolfCandidate.Merge038

-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_CompletenessV5 ====
section

namespace ClaudeWCT.W9.T3.Budgets.V5
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3.Budgets (failMass_eq_one_sub_accept rejection_power_le ofReal_inv_two_pow)
open ClaudeWCT.W9.T3.BaseAudit
theorem failure_power_of_rate {β : Type} (decoder : HashOutput → Option β) (p : ℚ) (L bits : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hacc : ENNReal.ofReal (p : ℝ) ≤ Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)])
    (hrate : (bits : ℚ) * 0.6931471808 ≤ L * p) :
    failMass decoder ^ L ≤ 1 / (2 : ENNReal) ^ bits := by
  have hp0' : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
  have hp1' : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  have hm : failMass decoder ≤ ENNReal.ofReal (1 - (p : ℝ)) := by
    rw [failMass_eq_one_sub_accept, ENNReal.ofReal_sub 1 hp0', ENNReal.ofReal_one]
    exact tsub_le_tsub_left hacc 1
  refine (pow_le_pow_left₀ zero_le hm L).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le (p : ℝ) hp1' L bits (by
    have hl := Real.log_two_lt_d9
    have hr := (Rat.cast_le (K := ℝ)).mpr hrate
    push_cast at hr
    have hb : (0 : ℝ) ≤ bits := Nat.cast_nonneg _
    nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem ofReal_count_div (n : ℕ) :
    ENNReal.ofReal (((n : ℚ) / 2 ^ 128 : ℚ) : ℝ) = (n : ENNReal) / 2 ^ 128 := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
theorem ofReal_selected_count_div (n : ℕ) :
    ENNReal.ofReal (((n : ℚ) / (2 * 2 ^ 128) : ℚ) : ℝ) =
      (n : ENNReal) / (2 * 2 ^ 128) := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
  norm_num
theorem top_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.topCount144 : ENNReal) / (2 * 2 ^ 128)) :
    failMass decoder ^ (2 ^ 22) ≤ 1 / (2 : ENNReal) ^ 1000 :=
  failure_power_of_rate decoder V5.p1 (2 ^ 22) 1000 (by norm_num [V5.p1, V5.topCount144])
    (by norm_num [V5.p1, V5.topCount144])
    (by rw [hacc, V5.p1, ofReal_selected_count_div])
    (by exact_mod_cast V5.rate_top_1000)
theorem lower199f5_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.lowerCount199f5 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 600 :=
  failure_power_of_rate decoder (V5.lowerCount199f5 / 2 ^ 128) (2 ^ 21) 600
    (by norm_num [V5.lowerCount199f5]) (by norm_num [V5.lowerCount199f5])
    (by rw [hacc, ofReal_count_div])
    (by norm_num [V5.lowerCount199f5])
theorem lower199f4_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.lowerCount199f4 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 600 :=
  failure_power_of_rate decoder (V5.lowerCount199f4 / 2 ^ 128) (2 ^ 21) 600
    (by norm_num [V5.lowerCount199f4]) (by norm_num [V5.lowerCount199f4])
    (by rw [hacc, ofReal_count_div])
    (by norm_num [V5.lowerCount199f4])
theorem lower200f4_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.lowerCount200f4 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 600 :=
  failure_power_of_rate decoder (V5.lowerCount200f4 / 2 ^ 128) (2 ^ 21) 600
    (by norm_num [V5.lowerCount200f4]) (by norm_num [V5.lowerCount200f4])
    (by rw [hacc, ofReal_count_div])
    (by norm_num [V5.lowerCount200f4])
theorem digest_failure_power_900_of {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (V5.p0 : ℝ)) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 900 :=
  failure_power_of_rate decoder V5.p0 (2 ^ 21) 900 V5.p0_nonneg V5.p0_le_one hacc.ge
    (by exact_mod_cast V5.rate_digest_900)
theorem digest_failure_power_450_of {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (V5.p0 : ℝ)) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 450 := by
  refine (digest_failure_power_900_of decoder hacc).trans ?_
  gcongr
  · norm_num
  · norm_num
end ClaudeWCT.W9.T3.Budgets.V5
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ProducerDecodeV5 ====
section

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

/-! Restricted top choice (configuration (1)+(2)): LOW is forced iff bits 126, 127 of the top word are zero,
i.e. iff the digit of top chain 52 (bits 125..127) is below 2. `freeWord`: LOW is not forced. -/
def freeWord (w : Codec.Word) : Prop := 2 ≤ (w.2 1).val
instance (w : Codec.Word) : Decidable (freeWord w) := inferInstanceAs (Decidable (2 ≤ (w.2 1).val))
def freeStat8 (d : Triple8) : Nat := stat8 d + 65536 * if 2 ≤ (d 1).val then 1 else 0
def freeStat (w : Codec.Word) : Nat :=
  (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (w.1 q)) + freeStat8 w.2

theorem freeStat_eq (w : Codec.Word) :
    freeStat w = 256 * weight w + score w + 65536 * if freeWord w then 1 else 0 := by
  have h := stat_eq w
  by_cases hg : freeWord w
  · have hg' : 2 ≤ (w.2 1).val := hg
    simp only [freeStat, freeStat8, if_pos hg', if_pos hg]
    simpa only [stat, Nat.add_assoc] using congrArg (fun n : Nat => n + 65536) h
  · have hg' : ¬2 ≤ (w.2 1).val := hg
    simp only [freeStat, freeStat8, if_neg hg', if_neg hg, Nat.mul_zero, Nat.add_zero]
    exact h

def freeGroup8 (y : Nat) : Nat := ∑ d : Triple8, y ^ freeStat8 d
def freePacked : Nat := group5 radix true true * group5 radix false true ^ 11 *
  group5 radix false false ^ 5 * freeGroup8 radix

theorem free_weighted_words (y : Nat) :
    (∑ w : Codec.Word, y ^ freeStat w) =
      group5 y true true * group5 y false true ^ 11 * group5 y false false ^ 5 * freeGroup8 y := by
  rw [Fintype.sum_prod_type]
  simp only [freeStat, pow_add]
  rw [← Finset.sum_mul_sum]
  have h : (∑ f : Fin 17 → Triple5,
      y ^ (∑ q : Fin 17, stat5 (decide (q.val = 0)) (hasPenalty q) (f q))) =
      ∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q) := by
    simpa only [group5, ← Finset.prod_pow_eq_pow_sum] using
      (Fintype.prod_sum fun (q : Fin 17) (d : Triple5) =>
        y ^ stat5 (decide (q.val = 0)) (hasPenalty q) d).symm
  rw [h]
  change (∏ q : Fin 17, group5 y (decide (q.val = 0)) (hasPenalty q)) * freeGroup8 y = _
  norm_num [Fin.prod_univ_succ, hasPenalty]
  ring_nf
  simp

theorem free_truncated_card (cut : Nat) (hc : 0 < cut) :
    (univ.filter fun w : Codec.Word => freeStat w < cut).card =
      (freePacked % radix ^ cut) % (radix - 1) := by
  classical
  unfold freePacked
  rw [← free_weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ freeStat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

/-- Top words at target 146 accepted by the canonical top producer on the LOW path (e7b: credit + 3 ≥ 18, i.e.
score ≥ 15 + 12) whose LOW is not forced. -/
def freeCount : Nat := 62603755540080218178176754635310864

theorem free_exact_packed_count :
    (freePacked % radix ^ 103168) % (radix - 1) -
      (freePacked % radix ^ 102939) % (radix - 1) = freeCount := by
  decide +kernel

theorem free_card_model :
    (univ.filter fun w : Codec.Word => weight w = 146 ∧ 27 ≤ score w ∧ freeWord w).card = freeCount := by
  classical
  have hs : (univ.filter fun w : Codec.Word => weight w = 146 ∧ 27 ≤ score w ∧ freeWord w) =
      (univ.filter fun w : Codec.Word => freeStat w < 103168) \
        (univ.filter fun w : Codec.Word => freeStat w < 102939) := by
    ext w
    have hc := score_le w
    have hw := weight_le_225 w
    have he := freeStat_eq w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    by_cases hg : freeWord w <;> simp [hg] at he ⊢ <;> omega
  rw [hs, card_sdiff_of_subset]
  · rw [free_truncated_card _ (by decide), free_truncated_card _ (by decide), free_exact_packed_count]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    omega

/-! Top-bytes layer: the canonical top producer caps the zero digits of a top word at 9 (of its 54 digits). -/
def zeros5 (d : Triple5) : Nat := ∑ i : Fin 3, if (d i).val = 0 then 1 else 0
def zeros8 (d : Triple8) : Nat := ∑ i : Fin 3, if (d i).val = 0 then 1 else 0
def zeros (w : Codec.Word) : Nat := (∑ q : Fin 17, zeros5 (w.1 q)) + zeros8 w.2

/-- Zero-capped canonical free top words: LOW-path accepted at floor 22 with the d6b LOW bonus 2 (score ≥ 32), LOW not forced, at most
9 zero digits. Kept as a cardinality; its value is decided downstream (`ClaudeWCT.Numerics.TopZero`). -/
def zeroFreeCard : Nat :=
  (univ.filter fun w : Codec.Word => weight w = 146 ∧ 32 ≤ score w ∧ freeWord w ∧ zeros w ≤ 9).card

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

open scoped BigOperators
open SigGolfResearch.NonbinaryTop.EffectiveCounting

theorem topWord_getD (w : Codec.Word) (i : Nat) (hi : i < 54) :
    (SigGolfCandidate.T3.Nonbinary.wordDigits w).getD i 0 =
      if h : i < 51 then (w.1 ⟨i / 3, by omega⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val
      else (w.2 ⟨(i - 51) % 3, Nat.mod_lt _ (by decide)⟩).val := by
  interval_cases i <;> rfl

theorem count_zero_ofFn3 (f : Fin 3 → Nat) :
    (List.ofFn f).count 0 = ∑ i : Fin 3, if f i = 0 then 1 else 0 := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.count_cons, List.count_nil, beq_iff_eq, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  split_ifs <;> simp_all

theorem wordDigits_count_zero (w : Codec.Word) :
    (SigGolfCandidate.T3.Nonbinary.wordDigits w).count 0 = EffectiveCounting.zeros w := by
  unfold SigGolfCandidate.T3.Nonbinary.wordDigits EffectiveCounting.zeros EffectiveCounting.zeros5
    EffectiveCounting.zeros8
  simp only [List.count_append, List.count_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    count_zero_ofFn3]

attribute [local irreducible] SigGolfCandidate.T3.Nonbinary.wordDigits

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

/-- The canonical top predicate (T51: floor 14 with the d6b LOW bonus 2) holds for every word whose reward reaches a
floor `≥ 12`. -/
theorem accepted_topGood {floor : Nat} (hf : 12 ≤ floor) {P : List Nat → Prop} {value : Digest}
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
theorem selected_top_card (floor : Nat) (hf : 12 ≤ floor) (P : List Nat → Prop) [DecidablePred P]
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
      canonicalZeroBound lay digits ∧ producerRankBound lay value ∧ P digits := by
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
      dispatchPenalty, wordCredit, savedCopies, safeZeroCopy, canonicalZeroBound, producerZeroCap, producerRankBound,
      chainCount, maxDigit]
end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfResearch.NonbinaryTop

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

theorem selected_credit_card_zero_of_lt (lay : Layer) (floor credit : Nat) (hf : credit < floor) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay false ds = credit) (encodingAnswer lay answer)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro answer _ h
  have := accepted_credit_floor h
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
    simp only [canonicalZeroBound, producerZeroCap, show (1 : Layer) ≠ 0 by decide, if_false,
      filter_zero_count, digits_zeros] at hz
    exact ⟨w, he, hw, hf, hz, hP⟩
  · rintro ⟨w, he, hw, hf, hz, hP⟩
    subst v
    refine ⟨digits w, decode_encode_201 w hw, ?_, ?_, ?_, hP⟩
    · simpa only [dispatchPenalty, show (1 : Layer) ≠ 0 by decide, if_false,
        Nat.add_zero, reward_lower_model] using hf
    · simpa only [canonicalZeroBound, producerZeroCap, show (1 : Layer) ≠ 0 by decide, if_false,
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
      canonicalZeroBound lay ds ∧ producerRankBound lay v := by
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
      CanonicalPolicy.producerDecodeAt 0 (floor - 2) false v := by
  have e1 (ds : List Nat) : CanonicalPolicy.pathReward 0 true ds = CanonicalPolicy.reward 0 ds + 2 := by
    simp [CanonicalPolicy.pathReward_top]
  have e2 (ds : List Nat) : CanonicalPolicy.pathReward 0 false ds = CanonicalPolicy.reward 0 ds := by
    simp [CanonicalPolicy.pathReward_top]
  cases h : CanonicalPolicy.producerDecodeAt 0 (floor - 2) false v with
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
          have hc : CanonicalPolicy.producerDecodeAt 0 (floor - 2) false v = some ds := by
            apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
            refine ⟨hs.1, ?_, hs.2.2⟩
            have h1 := hs.2.1
            rw [e1] at h1; rw [e2]
            omega
          rw [hc] at h
          cases h

/-- On an accepted LOW top word (floor ≥ 3) the LOW credit is the plain credit plus 2 (d6b). -/
theorem credit_top_true_of {floor : Nat} (hf : 3 ≤ floor) {v : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor true v = some ds) :
    CanonicalPolicy.credit 0 true ds = CanonicalPolicy.credit 0 false ds + 2 := by
  have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp h
  have h1 := hs.2.1
  simp only [CanonicalPolicy.pathReward_top, if_true] at h1
  simp only [CanonicalPolicy.credit_top, if_true, if_false, Bool.false_eq_true, Nat.add_zero]
  omega

/-- The d6b top decoder event: through LOW (chosen when canonical-good or forced) the producer runs at floor
`floor - 2` and adds 2 to the credit; through HIGH it runs at `floor`. -/
theorem top_decoder_event (floor c : Nat) (hf : 3 ≤ floor) (answer : HashOutput) :
    (∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) ↔
      (if topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128) then
        accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c) (answer.extractLsb' 0 128)
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
end
-- ==== merged from ClaudeWCT_Numerics_N600Data ====
section

namespace ClaudeWCT.Numerics.N600
def words : List (List Nat) :=[[0,0,0,0,3,4],[0,0,0,0,4,3],[0,0,0,1,2,4],[0,0,0,1,3,3],[0,0,0,1,4,2],[0,0,0,2,1,4],[0,0,0,2,2,3],[0,0,0,2,3,2],[0,0,0,2,4,1],[0,0,0,3,0,4],[0,0,0,3,1,3],[0,0,0,3,2,2],[0,0,0,3,3,1],[0,0,0,3,4,0],[0,0,0,4,0,3],[0,0,0,4,1,2],[0,0,0,4,2,1],[0,0,0,4,3,0],[0,0,1,0,2,4],[0,0,1,0,3,3],[0,0,1,0,4,2],[0,0,1,1,1,4],[0,0,1,1,2,3],[0,0,1,1,3,2],[0,0,1,1,4,1],[0,0,1,2,0,4],[0,0,1,2,1,3],[0,0,1,2,2,2],[0,0,1,2,3,1],[0,0,1,2,4,0],[0,0,1,3,0,3],[0,0,1,3,1,2],[0,0,1,3,2,1],[0,0,1,3,3,0],[0,0,1,4,0,2],[0,0,1,4,1,1],[0,0,1,4,2,0],[0,0,2,0,1,4],[0,0,2,0,2,3],[0,0,2,0,3,2],[0,0,2,0,4,1],[0,0,2,1,0,4],[0,0,2,1,1,3],[0,0,2,1,2,2],[0,0,2,1,3,1],[0,0,2,1,4,0],[0,0,2,2,0,3],[0,0,2,2,1,2],[0,0,2,2,2,1],[0,0,2,2,3,0],[0,0,2,3,0,2],[0,0,2,3,1,1],[0,0,2,3,2,0],[0,0,2,4,0,1],[0,0,2,4,1,0],[0,0,3,0,0,4],[0,0,3,0,1,3],[0,0,3,0,2,2],[0,0,3,0,3,1],[0,0,3,0,4,0],[0,0,3,1,0,3],[0,0,3,1,1,2],[0,0,3,1,2,1],[0,0,3,1,3,0],[0,0,3,2,0,2],[0,0,3,2,1,1],[0,0,3,2,2,0],[0,0,3,3,0,1],[0,0,3,3,1,0],[0,0,3,4,0,0],[0,0,4,0,0,3],[0,0,4,0,1,2],[0,0,4,0,2,1],[0,0,4,0,3,0],[0,0,4,1,0,2],[0,0,4,1,1,1],[0,0,4,1,2,0],[0,0,4,2,0,1],[0,0,4,2,1,0],[0,0,4,3,0,0],[0,1,0,0,2,4],[0,1,0,0,3,3],[0,1,0,0,4,2],[0,1,0,1,1,4],[0,1,0,1,2,3],[0,1,0,1,3,2],[0,1,0,1,4,1],[0,1,0,2,0,4],[0,1,0,2,1,3],[0,1,0,2,2,2],[0,1,0,2,3,1],[0,1,0,2,4,0],[0,1,0,3,0,3],[0,1,0,3,1,2],[0,1,0,3,2,1],[0,1,0,3,3,0],[0,1,0,4,0,2],[0,1,0,4,1,1],[0,1,0,4,2,0],[0,1,1,0,1,4],[0,1,1,0,2,3],[0,1,1,0,3,2],[0,1,1,0,4,1],[0,1,1,1,0,4],[0,1,1,1,1,3],[0,1,1,1,3,1],[0,1,1,1,4,0],[0,1,1,2,0,3],[0,1,1,2,3,0],[0,1,1,3,0,2],[0,1,1,3,1,1],[0,1,1,3,2,0],[0,1,1,4,0,1],[0,1,1,4,1,0],[0,1,2,0,0,4],[0,1,2,0,1,3],[0,1,2,0,2,2],[0,1,2,0,3,1],[0,1,2,0,4,0],[0,1,2,1,0,3],[0,1,2,1,3,0],[0,1,2,2,0,2],[0,1,2,2,2,0],[0,1,2,3,0,1],[0,1,2,3,1,0],[0,1,2,4,0,0],[0,1,3,0,0,3],[0,1,3,0,1,2],[0,1,3,0,2,1],[0,1,3,0,3,0],[0,1,3,1,0,2],[0,1,3,1,1,1],[0,1,3,1,2,0],[0,1,3,2,0,1],[0,1,3,2,1,0],[0,1,3,3,0,0],[0,1,4,0,0,2],[0,1,4,0,1,1],[0,1,4,0,2,0],[0,1,4,1,0,1],[0,1,4,1,1,0],[0,1,4,2,0,0],[0,2,0,0,1,4],[0,2,0,0,2,3],[0,2,0,0,3,2],[0,2,0,0,4,1],[0,2,0,1,0,4],[0,2,0,1,1,3],[0,2,0,1,2,2],[0,2,0,1,3,1],[0,2,0,1,4,0],[0,2,0,2,0,3],[0,2,0,2,1,2],[0,2,0,2,2,1],[0,2,0,2,3,0],[0,2,0,3,0,2],[0,2,0,3,1,1],[0,2,0,3,2,0],[0,2,0,4,0,1],[0,2,0,4,1,0],[0,2,1,0,0,4],[0,2,1,0,1,3],[0,2,1,0,2,2],[0,2,1,0,3,1],[0,2,1,0,4,0],[0,2,1,1,0,3],[0,2,1,1,3,0],[0,2,1,2,0,2],[0,2,1,2,2,0],[0,2,1,3,0,1],[0,2,1,3,1,0],[0,2,1,4,0,0],[0,2,2,0,0,3],[0,2,2,0,1,2],[0,2,2,0,2,1],[0,2,2,0,3,0],[0,2,2,1,0,2],[0,2,2,1,2,0],[0,2,2,2,0,1],[0,2,2,2,1,0],[0,2,2,3,0,0],[0,2,3,0,0,2],[0,2,3,0,1,1],[0,2,3,0,2,0],[0,2,3,1,0,1],[0,2,3,1,1,0],[0,2,3,2,0,0],[0,2,4,0,0,1],[0,2,4,0,1,0],[0,2,4,1,0,0],[0,3,0,0,0,4],[0,3,0,0,1,3],[0,3,0,0,2,2],[0,3,0,0,3,1],[0,3,0,0,4,0],[0,3,0,1,0,3],[0,3,0,1,1,2],[0,3,0,1,2,1],[0,3,0,1,3,0],[0,3,0,2,0,2],[0,3,0,2,1,1],[0,3,0,2,2,0],[0,3,0,3,0,1],[0,3,0,3,1,0],[0,3,0,4,0,0],[0,3,1,0,0,3],[0,3,1,0,1,2],[0,3,1,0,2,1],[0,3,1,0,3,0],[0,3,1,1,0,2],[0,3,1,1,1,1],[0,3,1,1,2,0],[0,3,1,2,0,1],[0,3,1,2,1,0],[0,3,1,3,0,0],[0,3,2,0,0,2],[0,3,2,0,1,1],[0,3,2,0,2,0],[0,3,2,1,0,1],[0,3,2,1,1,0],[0,3,2,2,0,0],[0,3,3,0,0,1],[0,3,3,0,1,0],[0,3,3,1,0,0],[0,3,4,0,0,0],[0,4,0,0,0,3],[0,4,0,0,1,2],[0,4,0,0,2,1],[0,4,0,0,3,0],[0,4,0,1,0,2],[0,4,0,1,1,1],[0,4,0,1,2,0],[0,4,0,2,0,1],[0,4,0,2,1,0],[0,4,0,3,0,0],[0,4,1,0,0,2],[0,4,1,0,1,1],[0,4,1,0,2,0],[0,4,1,1,0,1],[0,4,1,1,1,0],[0,4,1,2,0,0],[0,4,2,0,0,1],[0,4,2,0,1,0],[0,4,2,1,0,0],[0,4,3,0,0,0],[1,0,0,0,2,4],[1,0,0,0,3,3],[1,0,0,0,4,2],[1,0,0,1,1,4],[1,0,0,1,2,3],[1,0,0,1,3,2],[1,0,0,1,4,1],[1,0,0,2,0,4],[1,0,0,2,1,3],[1,0,0,2,2,2],[1,0,0,2,3,1],[1,0,0,2,4,0],[1,0,0,3,0,3],[1,0,0,3,1,2],[1,0,0,3,2,1],[1,0,0,3,3,0],[1,0,0,4,0,2],[1,0,0,4,1,1],[1,0,0,4,2,0],[1,0,1,0,1,4],[1,0,1,0,2,3],[1,0,1,0,3,2],[1,0,1,0,4,1],[1,0,1,1,0,4],[1,0,1,1,1,3],[1,0,1,1,3,1],[1,0,1,1,4,0],[1,0,1,2,0,3],[1,0,1,2,3,0],[1,0,1,3,0,2],[1,0,1,3,1,1],[1,0,1,3,2,0],[1,0,1,4,0,1],[1,0,1,4,1,0],[1,0,2,0,0,4],[1,0,2,0,1,3],[1,0,2,0,2,2],[1,0,2,0,3,1],[1,0,2,0,4,0],[1,0,2,1,0,3],[1,0,2,1,3,0],[1,0,2,2,0,2],[1,0,2,2,2,0],[1,0,2,3,0,1],[1,0,2,3,1,0],[1,0,2,4,0,0],[1,0,3,0,0,3],[1,0,3,0,1,2],[1,0,3,0,2,1],[1,0,3,0,3,0],[1,0,3,1,0,2],[1,0,3,1,1,1],[1,0,3,1,2,0],[1,0,3,2,0,1],[1,0,3,2,1,0],[1,0,3,3,0,0],[1,0,4,0,0,2],[1,0,4,0,1,1],[1,0,4,0,2,0],[1,0,4,1,0,1],[1,0,4,1,1,0],[1,0,4,2,0,0],[1,1,0,0,1,4],[1,1,0,0,2,3],[1,1,0,0,3,2],[1,1,0,0,4,1],[1,1,0,1,0,4],[1,1,0,1,4,0],[1,1,0,2,0,3],[1,1,0,4,0,1],[1,1,0,4,1,0],[1,1,1,0,0,4],[1,1,1,0,4,0],[1,1,1,1,3,0],[1,1,1,3,0,1],[1,1,1,4,0,0],[1,1,2,0,0,3],[1,1,2,0,3,0],[1,1,2,3,0,0],[1,1,3,0,0,2],[1,1,3,0,1,1],[1,1,3,0,2,0],[1,1,3,2,0,0],[1,1,4,0,0,1],[1,1,4,0,1,0],[1,1,4,1,0,0],[1,2,0,0,0,4],[1,2,0,0,1,3],[1,2,0,0,2,2],[1,2,0,0,3,1],[1,2,0,0,4,0],[1,2,0,1,3,0],[1,2,0,3,0,1],[1,2,0,3,1,0],[1,2,0,4,0,0],[1,2,1,0,0,3],[1,2,1,3,0,0],[1,2,2,0,0,2],[1,2,2,2,0,0],[1,2,3,0,0,1],[1,2,3,1,0,0],[1,2,4,0,0,0],[1,3,0,0,0,3],[1,3,0,0,1,2],[1,3,0,0,2,1],[1,3,0,0,3,0],[1,3,0,1,1,1],[1,3,0,1,2,0],[1,3,0,2,0,1],[1,3,0,2,1,0],[1,3,0,3,0,0],[1,3,1,0,0,2],[1,3,1,0,2,0],[1,3,1,2,0,0],[1,3,2,0,0,1],[1,3,2,1,0,0],[1,3,3,0,0,0],[1,4,0,0,0,2],[1,4,0,0,1,1],[1,4,0,0,2,0],[1,4,0,1,0,1],[1,4,0,1,1,0],[1,4,0,2,0,0],[1,4,1,0,0,1],[1,4,1,0,1,0],[1,4,1,1,0,0],[1,4,2,0,0,0],[2,0,0,0,1,4],[2,0,0,0,2,3],[2,0,0,0,3,2],[2,0,0,0,4,1],[2,0,0,1,0,4],[2,0,0,1,1,3],[2,0,0,1,2,2],[2,0,0,1,3,1],[2,0,0,1,4,0],[2,0,0,2,0,3],[2,0,0,2,1,2],[2,0,0,2,2,1],[2,0,0,2,3,0],[2,0,0,3,0,2],[2,0,0,3,1,1],[2,0,0,3,2,0],[2,0,0,4,0,1],[2,0,0,4,1,0],[2,0,1,0,0,4],[2,0,1,0,1,3],[2,0,1,0,2,2],[2,0,1,0,3,1],[2,0,1,0,4,0],[2,0,1,1,0,3],[2,0,1,1,3,0],[2,0,1,2,0,2],[2,0,1,2,2,0],[2,0,1,3,0,1],[2,0,1,3,1,0],[2,0,1,4,0,0],[2,0,2,0,0,3],[2,0,2,0,1,2],[2,0,2,0,2,1],[2,0,2,0,3,0],[2,0,2,1,0,2],[2,0,2,1,2,0],[2,0,2,2,0,1],[2,0,2,2,1,0],[2,0,2,3,0,0],[2,0,3,0,0,2],[2,0,3,0,1,1],[2,0,3,0,2,0],[2,0,3,1,0,1],[2,0,3,1,1,0],[2,0,3,2,0,0],[2,0,4,0,0,1],[2,0,4,0,1,0],[2,0,4,1,0,0],[2,1,0,0,0,4],[2,1,0,0,1,3],[2,1,0,0,2,2],[2,1,0,0,3,1],[2,1,0,0,4,0],[2,1,0,1,3,0],[2,1,0,3,0,1],[2,1,0,4,0,0],[2,1,1,0,0,3],[2,1,1,0,3,0],[2,1,1,3,0,0],[2,1,2,0,0,2],[2,1,2,2,0,0],[2,1,3,0,0,1],[2,1,3,0,1,0],[2,1,3,1,0,0],[2,1,4,0,0,0],[2,2,0,0,0,3],[2,2,0,0,1,2],[2,2,0,0,2,1],[2,2,0,0,3,0],[2,2,0,1,2,0],[2,2,0,2,0,1],[2,2,0,3,0,0],[2,2,1,0,0,2],[2,2,1,2,0,0],[2,2,2,0,0,1],[2,2,2,1,0,0],[2,2,3,0,0,0],[2,3,0,0,0,2],[2,3,0,0,1,1],[2,3,0,0,2,0],[2,3,0,1,0,1],[2,3,0,1,1,0],[2,3,0,2,0,0],[2,3,1,0,0,1],[2,3,1,0,1,0],[2,3,1,1,0,0],[2,3,2,0,0,0],[2,4,0,0,0,1],[2,4,0,0,1,0],[2,4,0,1,0,0],[2,4,1,0,0,0],[3,0,0,0,0,4],[3,0,0,0,1,3],[3,0,0,0,2,2],[3,0,0,0,3,1],[3,0,0,0,4,0],[3,0,0,1,0,3],[3,0,0,1,1,2],[3,0,0,1,2,1],[3,0,0,1,3,0],[3,0,0,2,0,2],[3,0,0,2,1,1],[3,0,0,2,2,0],[3,0,0,3,0,1],[3,0,0,3,1,0],[3,0,0,4,0,0],[3,0,1,0,0,3],[3,0,1,0,1,2],[3,0,1,0,2,1],[3,0,1,0,3,0],[3,0,1,1,0,2],[3,0,1,1,1,1],[3,0,1,1,2,0],[3,0,1,2,0,1],[3,0,1,2,1,0],[3,0,1,3,0,0],[3,0,2,0,0,2],[3,0,2,0,1,1],[3,0,2,0,2,0],[3,0,2,1,0,1],[3,0,2,1,1,0],[3,0,2,2,0,0],[3,0,3,0,0,1],[3,0,3,0,1,0],[3,0,3,1,0,0],[3,0,4,0,0,0],[3,1,0,0,0,3],[3,1,0,0,1,2],[3,1,0,0,2,1],[3,1,0,0,3,0],[3,1,0,1,1,1],[3,1,0,1,2,0],[3,1,0,2,0,1],[3,1,0,3,0,0],[3,1,1,0,0,2],[3,1,1,0,2,0],[3,1,1,1,1,0],[3,1,1,2,0,0],[3,1,2,0,0,1],[3,1,2,0,1,0],[3,1,2,1,0,0],[3,1,3,0,0,0],[3,2,0,0,0,2],[3,2,0,0,1,1],[3,2,0,0,2,0],[3,2,0,1,0,1],[3,2,0,1,1,0],[3,2,0,2,0,0],[3,2,1,0,0,1],[3,2,1,1,0,0],[3,2,2,0,0,0],[3,3,0,0,0,1],[3,3,0,0,1,0],[3,3,0,1,0,0],[3,3,1,0,0,0],[3,4,0,0,0,0],[4,0,0,0,0,3],[4,0,0,0,1,2],[4,0,0,0,2,1],[4,0,0,0,3,0],[4,0,0,1,0,2],[4,0,0,1,1,1],[4,0,0,1,2,0],[4,0,0,2,0,1],[4,0,0,2,1,0],[4,0,0,3,0,0],[4,0,1,0,0,2],[4,0,1,0,1,1],[4,0,1,0,2,0],[4,0,1,1,0,1],[4,0,1,1,1,0],[4,0,1,2,0,0],[4,0,2,0,0,1],[4,0,2,0,1,0],[4,0,2,1,0,0],[4,0,3,0,0,0],[4,1,0,0,0,2],[4,1,0,0,1,1],[4,1,0,0,2,0],[4,1,0,1,0,1],[4,1,0,1,1,0],[4,1,0,2,0,0],[4,1,1,0,0,1],[4,1,1,0,1,0],[4,1,1,1,0,0],[4,1,2,0,0,0],[4,2,0,0,0,1],[4,2,0,0,1,0],[4,2,0,1,0,0],[4,2,1,0,0,0],[4,3,0,0,0,0]]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def w1Data : List (Nat × Int) :=
  [(0, -16), (2, 16), (9, 64), (14, 60), (17, 4), (18, -108), (19, 6), (20, 3), (21, 138), (23, 4), (24, 8), (25, 12), (26, 10), (27, 16), (32, -6), (33, -11), (34, -9), (36, -3), (37, -138), (48, -37), (49, -14), (50, -6), (55, -206), (62, -24), (63, -17), (64, -3), (65, -34), (66, -10), (67, -27), (68, -9), (69, -17), (70, -147), (71, -42), (72, 62), (73, 31), (80, 350), (89, -3), (90, -6), (91, -25), (92, -27), (93, -48), (94, -20), (95, -42), (96, -32), (97, -6), (98, -11), (99, -9), (101, -105), (113, -4), (114, -8), (115, -11), (116, -18), (117, -12), (118, -21), (119, -29), (120, -8), (121, -7), (122, -8), (123, -4), (125, -2), (126, -48), (127, -7), (128, -2), (129, 20), (130, 39), (131, 29), (132, 81), (133, 40), (134, 22), (135, 123), (138, 20), (139, 22), (140, -20), (142, 187), (156, -2), (157, -2), (158, -2), (159, -6), (160, -13), (161, -12), (162, -7), (163, -7), (164, -4), (165, -3), (166, -2), (173, 17), (174, 108), (175, 37), (176, 19), (179, 69), (180, 88), (181, 18), (190, 162), (207, 100), (213, 100), (218, 14), (221, 30), (222, 44), (223, 14), (224, 56), (225, 113), (226, 14), (227, -280), (228, 25), (233, -272), (245, -256), (284, 19), (285, 30), (286, 10), (287, 19), (288, 86), (289, 9), (290, 30), (291, 37), (292, 19), (293, 18), (294, 10), (335, 20), (338, 20), (339, 20), (340, 20), (342, 20), (344, 20), (365, -96), (366, 4), (367, 16), (368, -78), (369, -70), (370, -93), (372, -91), (374, -89), (427, 5), (428, 5), (429, 20), (461, -67), (462, -66), (463, -260), (528, -210), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf0Data : List (Nat × Int) :=
  [(0, -5), (2, 8), (9, 28), (14, 20), (17, 2), (18, -62), (19, 2), (20, 2), (21, 46), (23, 1), (24, 4), (25, 5), (26, 4), (27, 6), (32, -6), (33, -5), (34, -6), (36, -3), (37, -67), (48, -28), (49, -10), (50, -6), (55, -98), (62, -18), (63, -14), (64, -3), (65, -20), (66, -2), (67, -15), (68, -8), (69, -12), (70, -66), (71, -15), (72, 62), (73, 31), (80, 214), (89, -3), (90, -3), (91, -20), (92, -16), (93, -24), (94, -12), (95, -29), (96, -12), (97, -6), (98, -8), (99, -6), (101, -33), (113, -3), (114, -6), (115, -9), (116, -8), (117, -6), (118, -12), (119, -15), (120, -5), (121, -3), (122, -5), (123, -3), (125, -1), (126, -16), (127, -5), (128, -1), (129, 20), (130, 39), (131, 33), (132, 41), (133, 41), (134, 22), (135, 84), (138, 20), (139, 22), (140, -6), (142, 77), (156, -2), (157, -1), (158, -2), (159, -4), (160, -6), (161, -6), (162, -2), (163, -3), (164, -3), (166, -1), (173, 17), (174, 73), (175, 37), (176, 19), (179, 69), (180, 53), (181, 18), (190, 66), (207, 80), (213, 80), (218, 14), (221, 30), (222, 30), (223, 14), (224, 16), (225, 53), (226, 14), (227, -280), (228, 13), (233, -272), (245, -129), (284, 19), (285, 20), (286, 10), (287, 19), (288, 67), (290, 20), (291, 9), (292, 9), (293, 9), (294, 10), (335, 16), (338, 16), (339, 16), (340, 16), (344, 16), (365, -96), (366, 4), (367, 12), (368, -82), (369, -82), (370, -93), (374, -89), (427, 4), (428, 4), (429, 12), (461, -67), (462, -66), (463, -195), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf1Data : List (Nat × Int) :=
  [(0, -5), (2, 7), (9, 29), (14, 20), (17, 1), (18, -60), (19, 6), (21, 46), (23, 2), (24, 4), (25, 6), (26, 3), (27, 5), (32, -3), (33, -9), (34, -9), (37, -67), (48, -24), (49, -14), (50, -6), (55, -99), (62, -18), (63, -12), (65, -27), (66, -8), (67, -18), (68, -3), (69, -6), (70, -66), (71, -15), (72, 62), (73, 31), (80, 210), (90, -3), (91, -18), (92, -17), (93, -36), (94, -8), (95, -31), (96, -15), (97, -3), (98, -3), (99, -6), (101, -33), (113, -3), (114, -3), (115, -9), (116, -12), (117, -10), (118, -14), (119, -18), (120, -3), (123, -3), (126, -16), (127, -5), (128, -2), (129, 20), (130, 20), (131, 33), (132, 84), (133, 41), (135, 105), (139, 22), (140, -6), (142, 77), (156, -1), (157, -2), (158, -1), (159, -5), (160, -8), (161, -9), (162, -4), (174, 90), (175, 37), (176, 19), (179, 69), (180, 54), (181, 18), (190, 65), (207, 80), (213, 80), (218, 14), (221, 30), (222, 30), (223, 14), (224, 56), (225, 40), (227, -280), (233, -272), (245, -127), (284, 10), (285, 30), (286, 10), (287, 19), (288, 67), (289, 9), (290, 20), (291, 28), (335, 16), (338, 16), (339, 16), (340, 16), (342, 16), (365, -96), (366, 4), (367, 12), (368, -82), (369, -82), (370, -93), (372, -91), (427, 4), (428, 4), (429, 12), (461, -67), (462, -66), (463, -195), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf2Data : List (Nat × Int) :=
  [(0, -2), (2, 5), (9, 19), (14, 20), (18, -57), (20, 2), (21, 45), (23, 1), (24, 1), (25, 3), (26, 5), (27, 4), (33, -6), (36, -3), (37, -71), (48, -15), (55, -110), (62, -9), (65, -11), (66, -7), (67, -9), (68, -6), (69, -14), (70, -81), (71, -22), (72, 32), (80, 260), (92, -13), (93, -21), (94, -11), (95, -13), (96, -26), (98, -11), (99, -6), (101, -59), (115, -3), (116, -9), (117, -5), (118, -8), (119, -12), (120, -5), (121, -7), (122, -7), (123, -3), (126, -27), (127, -3), (131, 14), (132, 61), (133, 18), (134, 22), (135, 79), (138, 20), (139, 22), (140, -12), (142, 146), (159, -1), (160, -4), (161, -5), (162, -6), (163, -7), (164, -2), (165, -3), (166, -2), (174, 54), (175, 19), (179, 33), (180, 88), (181, 18), (190, 127), (207, 40), (213, 80), (221, 14), (223, 14), (224, 56), (225, 93), (226, 14), (227, -142), (228, 25), (233, -272), (245, -256), (287, 9), (288, 76), (289, 9), (290, 20), (291, 28), (292, 19), (293, 18), (294, 10), (338, 16), (339, 16), (340, 16), (342, 16), (344, 16), (368, -78), (369, -70), (370, -93), (372, -91), (374, -89), (428, 4), (429, 16), (462, -66), (463, -260), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf3Data : List (Nat × Int) :=
  [(0, -1), (2, 4), (9, 16), (14, 20), (17, 2), (18, -53), (19, 2), (21, 47), (23, 1), (24, 3), (25, 2), (26, 4), (27, 6), (32, -3), (33, -5), (34, -6), (37, -69), (48, -12), (49, -14), (55, -100), (62, -9), (63, -11), (64, -3), (65, -17), (66, -6), (67, -9), (68, -1), (69, -9), (70, -72), (71, -26), (72, 30), (73, 31), (80, 230), (89, -3), (90, -6), (91, -16), (92, -11), (93, -30), (94, -12), (95, -5), (96, -11), (99, -9), (101, -65), (113, -3), (114, -6), (115, -3), (116, -11), (117, -5), (118, -12), (119, -8), (120, -3), (121, -7), (123, -3), (125, -2), (126, -32), (127, -2), (129, 21), (130, 41), (131, 18), (132, 63), (133, 20), (134, 22), (135, 37), (139, 22), (140, -12), (142, 150), (156, -1), (157, -2), (158, -1), (159, -3), (160, -5), (161, -4), (162, -6), (163, -5), (164, -1), (165, -2), (173, 17), (174, 108), (175, 18), (179, 18), (180, 34), (181, 18), (190, 131), (207, 80), (213, 40), (218, 14), (221, 16), (222, 28), (224, 43), (225, 93), (226, 14), (227, -280), (228, 12), (233, -135), (245, -256), (284, 19), (285, 20), (286, 10), (287, 10), (288, 58), (290, 10), (291, 28), (292, 19), (293, 18), (335, 16), (338, 16), (339, 16), (342, 16), (344, 16), (365, -96), (366, 4), (367, 12), (368, -82), (369, -82), (372, -91), (374, -89), (427, 4), (428, 4), (429, 12), (461, -67), (462, -66), (463, -195), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf4Data : List (Nat × Int) :=
  [(0, -1), (2, 4), (9, 16), (14, 20), (17, 1), (18, -53), (19, 2), (20, 2), (21, 45), (23, 1), (24, 2), (25, 4), (26, 3), (27, 7), (32, -3), (33, -3), (34, -6), (36, -3), (37, -68), (48, -19), (49, -4), (50, -6), (55, -97), (62, -9), (63, -9), (64, -3), (65, -16), (66, -3), (67, -15), (68, -5), (69, -5), (70, -75), (71, -26), (72, 32), (73, 31), (80, 229), (90, -3), (91, -11), (92, -16), (93, -24), (94, -9), (95, -20), (96, -9), (97, -6), (98, -5), (101, -62), (114, -6), (115, -3), (116, -9), (117, -3), (118, -14), (119, -14), (120, -3), (121, -2), (122, -7), (125, -1), (126, -28), (127, -5), (128, -1), (129, -1), (130, 40), (131, 15), (132, 64), (133, 22), (134, 22), (135, 64), (138, 20), (140, -12), (142, 149), (158, -1), (159, -2), (160, -9), (161, -6), (162, -3), (163, -2), (164, -3), (165, -2), (166, -2), (173, 17), (174, 72), (175, 37), (176, 19), (179, 34), (180, 35), (190, 129), (207, 80), (213, 40), (221, 16), (222, 44), (223, 14), (224, 27), (225, 80), (226, 14), (227, -280), (228, 25), (233, -137), (245, -256), (284, 9), (285, 30), (287, 10), (288, 37), (289, 9), (290, 30), (291, 27), (292, 10), (293, 18), (294, 10), (335, 16), (339, 16), (340, 16), (342, 16), (344, 16), (365, -96), (367, 16), (369, -70), (370, -93), (372, -91), (374, -89), (427, 4), (429, 16), (461, -67), (463, -260), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wf5Data : List (Nat × Int) :=
  [(0, -2), (2, 4), (9, 20), (14, 20), (17, 2), (18, -55), (21, 47), (23, 2), (24, 2), (25, 4), (26, 1), (27, 4), (32, -3), (33, -5), (37, -72), (48, -13), (55, -114), (62, -9), (63, -5), (65, -11), (66, -4), (67, -15), (68, -4), (69, -5), (70, -81), (71, -22), (72, 30), (80, 257), (89, -3), (90, -3), (91, -10), (92, -8), (93, -9), (94, -8), (95, -28), (96, -23), (97, -3), (98, -6), (101, -63), (113, -3), (114, -3), (115, -6), (116, -5), (117, -7), (118, -3), (119, -20), (120, -5), (121, -2), (122, -5), (125, -2), (126, -25), (127, -1), (128, -2), (129, 21), (130, 18), (131, 13), (132, 17), (133, 20), (135, 123), (138, 20), (140, -12), (142, 149), (156, -2), (157, -1), (158, -1), (159, -3), (160, -7), (161, -6), (163, -4), (164, -3), (165, -2), (166, -1), (173, 17), (174, 35), (176, 19), (179, 53), (180, 88), (190, 130), (207, 40), (213, 80), (218, 14), (221, 14), (222, 44), (224, 26), (225, 93), (227, -138), (228, 25), (233, -272), (245, -256), (284, 19), (285, 20), (286, 10), (287, 9), (288, 39), (289, 9), (290, 20), (291, 28), (292, 19), (293, 9), (294, 10), (335, 16), (338, 16), (340, 16), (342, 16), (344, 16), (365, -96), (366, 4), (367, 12), (368, -82), (369, 12), (370, -93), (372, -91), (374, -89), (427, 4), (428, 4), (429, 12), (461, -67), (462, -66), (463, -195), (528, -175), (563, 563)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def w2Data : List (Nat × Int) :=
  [(0, 42592), (1, -37528), (2, 10518), (3, -50594), (4, -48796), (5, 36924), (6, -31374), (7, -8976), (8, -28540), (9, 10804), (10, -23292), (11, -15790), (12, 51026), (13, -4868), (14, 67510), (15, -56364), (16, -3898), (17, -15746), (18, -68390), (19, -9518), (20, -13025), (21, 184112), (22, -4654), (23, -12428), (24, 9708), (25, 19912), (26, 12078), (27, 26860), (28, 7726), (29, 2204), (30, 125926), (31, -4152), (32, -20404), (33, -17485), (34, 63439), (35, -3454), (36, -6831), (37, -198542), (38, 22708), (39, 47524), (40, 41566), (41, 31342), (42, 14442), (43, 66404), (44, -1096), (45, -1976), (46, 95322), (47, -3080), (48, -40341), (49, -13002), (50, 794), (51, 4322), (52, 11622), (53, 26642), (54, 6116), (55, -215512), (56, 10658), (57, 23668), (58, 16516), (59, 63422), (60, 43080), (61, 25018), (62, -20542), (63, -18735), (64, -1423), (65, -2514), (66, -17072), (67, -39599), (68, -16803), (69, -25785), (70, -186609), (71, -81132), (72, 45272), (73, 34405), (74, 18396), (75, 9938), (76, 26422), (77, 14750), (78, 22876), (79, 9764), (80, 246502), (81, 15484), (82, 3236), (83, 8838), (84, 9358), (85, 1112), (86, 55244), (87, 2820), (88, 5106), (89, -2047), (90, -9202), (91, -43073), (92, -47977), (93, -79278), (94, -33556), (95, -58940), (96, -51934), (97, -5986), (98, -7999), (99, -9183), (100, 9696), (101, -173561), (102, 6630), (103, 15392), (104, 11582), (105, 13406), (106, 6792), (107, 8912), (108, 6844), (109, 5698), (110, 14454), (111, 570), (112, 1110), (113, -6340), (114, -20154), (115, -27623), (116, -52348), (117, -32592), (118, -41691), (119, -80033), (120, -14160), (121, -13411), (122, -9308), (123, -11852), (125, -7514), (126, -146470), (127, -27291), (128, -7680), (129, 15648), (130, 30927), (131, 1065), (132, 57435), (133, 32590), (134, 20928), (135, 119285), (136, 10428), (137, 8766), (138, 23824), (139, 24110), (140, -69584), (141, 3630), (142, 189343), (143, 2768), (144, 2072), (145, 1608), (146, 1832), (147, 1600), (148, 1352), (149, 448), (150, 224), (152, 2400), (154, -7608), (155, -46688), (156, -23758), (157, -16182), (158, -8324), (159, -25098), (160, -83733), (161, -87104), (162, -36077), (163, -27627), (164, -15498), (165, -11219), (166, -7632), (168, 384), (171, -73456), (172, 1152), (173, 19033), (174, 117150), (175, 38913), (176, 19511), (178, 768), (179, 75167), (180, 93990), (181, 18902), (182, 1278), (183, 858), (184, 1704), (185, 2286), (186, 1500), (187, -18740), (188, 1464), (189, 1254), (190, 180178), (191, 420), (193, -27856), (196, -15504), (197, -23360), (198, -7408), (199, -30880), (200, -7464), (201, -7696), (203, -14568), (205, -20000), (207, 124400), (209, -2632), (210, -16014), (211, -10746), (212, -21480), (213, 94898), (214, -18724), (215, -15644), (216, -18054), (217, -15398), (218, 13984), (219, -5116), (221, 38888), (222, 57088), (223, 18846), (224, 74534), (225, 138641), (226, 18636), (227, -166040), (228, 34737), (229, 192), (230, 864), (231, 96), (232, 288), (233, -163362), (234, 192), (235, 192), (236, 96), (245, -158210), (246, 288), (247, 432), (248, 432), (249, 288), (255, -9688), (256, -14832), (257, -4992), (258, -9688), (259, -43536), (260, -4688), (261, -14808), (262, -19000), (263, -9592), (264, -9312), (265, -4888), (278, -5760), (279, -8592), (280, -8544), (281, -5664), (284, 32875), (285, 49920), (286, 16780), (287, 32685), (288, 146386), (289, 15801), (290, 49248), (291, 63225), (292, 31725), (293, 30786), (294, 15980), (300, 24), (301, 96), (302, 96), (303, 144), (305, -5120), (308, -5120), (309, -5120), (310, -5120), (312, -5120), (314, -5120), (333, -2096), (334, -8352), (335, 37640), (336, -12432), (338, 45400), (339, 45440), (340, 45140), (342, 44540), (344, 43940), (365, -79296), (366, 11492), (367, 45472), (368, -33028), (369, -11440), (370, -77469), (372, -75985), (374, -74493), (393, -1380), (394, -1380), (395, -5520), (427, 27715), (428, 27375), (429, 108140), (461, -66263), (462, -65340), (463, -257660), (493, 36750), (528, -229110), (563, 316969)]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def wwData : List (Nat × Int) :=
  [(0, 256), (2, -512), (4, 256), (9, -2048), (11, 2048), (14, -1920), (16, 1920), (17, -128), (18, 7552), (19, -64), (20, -3552), (21, -4224), (22, 96), (23, 11968), (24, -256), (25, -256), (26, 448), (27, -13952), (28, 4688), (29, 896), (30, 17664), (31, 480), (32, -12256), (33, 2096), (34, 2008), (35, 16624), (36, 13568), (37, 3624), (38, 1356), (39, -32748), (40, 2897), (41, 1180), (42, 16052), (43, -3544), (44, -736), (45, -1440), (46, -14804), (47, 1600), (48, 4680), (49, 672), (50, 288), (51, -14280), (52, 2068), (53, -1534), (54, -3290), (55, 33832), (56, -1858), (57, -13376), (58, -40408), (59, -1420), (60, -1684), (61, -2568), (62, -7044), (63, -3992), (64, -32140), (65, 380), (66, 8333), (67, 2506), (68, 991), (69, -33686), (70, 3606), (71, -1740), (72, -11207), (73, 41444), (74, 13032), (75, -3132), (76, -63760), (77, -3384), (78, -4184), (79, -26384), (80, -17228), (81, 4918), (82, 8570), (83, -1154), (84, -20484), (85, 9672), (86, 2860), (87, 6442), (88, 27030), (89, 52018), (90, -20826), (91, -46356), (92, 44464), (93, 15510), (94, 46480), (95, -3792), (96, -657), (97, -96), (98, -74310), (99, 14182), (100, 5168), (101, 98136), (102, 5600), (103, 18730), (104, 15604), (105, 5382), (106, 6744), (107, 44898), (108, 8728), (109, -17244), (110, 22660), (111, 9288), (112, -8212), (113, -5108), (114, -11692), (115, -15458), (116, -11422), (117, -94170), (118, 12744), (119, 25566), (120, 4696), (121, -3136), (122, -22218), (123, 1150), (124, 5430), (125, 58438), (126, 17575), (127, -25304), (128, -37801), (129, -1896), (130, 8174), (131, 6242), (132, 19020), (133, 16838), (134, 8611), (135, -141448), (136, 7685), (137, 9514), (138, 30857), (139, 2678), (140, 14873), (141, 21772), (142, -36526), (143, -20794), (144, 38068), (145, -12824), (146, 13783), (147, -16964), (148, 9526), (149, 10848), (150, -92738), (151, 14550), (152, 57056), (153, 31316), (154, 21246), (155, 19514), (156, 112320), (157, 8024), (158, 20596), (159, 23274), (160, 105354), (161, 14680), (162, 20822), (163, 86968), (164, 13624), (165, 9886), (166, 12234), (167, -6604), (168, -2238), (169, -15472), (170, -9382), (171, 10942), (172, -41174), (173, -39520), (174, -11942), (175, -35736), (176, -25038), (177, 5048), (178, -6825), (179, -60268), (180, -7142), (181, -55440), (182, 6173), (183, 10398), (184, 1393), (185, -5712), (186, -1124), (187, -23462), (188, 20406), (189, 22790), (190, -56952), (191, -1768), (192, -12316), (193, -276), (194, 4090), (195, 32470), (196, 17097), (197, -91972), (198, -41949), (199, -12736), (200, -6230), (201, 6966), (202, -15107), (203, -16060), (204, 10238), (205, -31310), (206, -36382), (207, 366), (208, -36320), (209, 6906), (210, 32824), (211, 42120), (212, -3828), (213, 7640), (214, 48946), (215, 116116), (216, 7294), (217, -7552), (218, 18752), (219, 26964), (220, -4474), (221, 13790), (222, 131514), (223, -15536), (224, -16080), (225, -41068), (226, -15076), (227, -30040), (228, -7316), (229, -67030), (230, -25561), (231, -39022), (232, -3024), (233, -9558), (234, -4192), (235, -60928), (236, -78447), (237, -15164), (238, -18539), (239, -9890), (240, -30068), (241, -54204), (242, -48231), (243, -69386), (244, -69004), (245, -9006), (246, 16690), (247, -38836), (248, -80850), (249, -19734), (250, -69406), (251, 43408), (252, -4504), (253, 1506), (254, -48959), (255, -1838), (256, -3524), (257, -25890), (258, -35670), (259, -10058), (260, 9), (261, -34486), (262, -50785), (263, 68404), (264, 83775), (265, 2370), (266, -60790), (267, 12858), (268, -59264), (269, -19418), (270, 176619), (271, -10748), (272, -22492), (273, -17534), (274, 9496), (275, -12140), (276, -19176), (277, -1760), (278, -17578), (279, -9894), (280, -53566), (281, -3290), (282, 171594), (283, -53240), (284, 16949), (285, -4300), (286, -8390), (287, 56934), (288, 91392), (289, -2960), (290, -6914), (291, -58380), (292, -16164), (293, 71932), (294, -1534), (295, -26584), (296, 1882), (297, 98638), (298, 38928), (299, -40488), (300, 86202), (301, 17634), (302, 30452), (303, 76796), (304, 63046), (305, 43878), (306, -20370), (307, -175044), (308, 7640), (309, 40912), (310, 34764), (311, 29086), (312, 44098), (313, -165416), (314, 8216), (315, 99370), (316, 38994), (317, -30940), (318, -6156), (319, 7070), (320, 18743), (321, 24508), (322, 61072), (323, 18552), (324, 7829), (325, -159806), (326, -3021), (327, -4610), (328, 74108), (329, 8718), (330, -11919), (331, -1724), (332, 56798), (333, -16222), (334, 49568), (335, -7078), (336, 3160), (337, 12108), (338, 18194), (339, -5682), (340, 1342), (341, 5616), (342, 17922), (343, -24708), (344, 3068), (345, 13876), (346, 64201), (347, -1568), (348, 35172), (349, 54528), (350, -357), (351, 3002), (352, 21777), (353, 46136), (354, 38076), (355, 54888), (356, 16272), (357, 2864), (358, -19425), (359, 15224), (360, 39342), (361, 5912), (362, -79384), (363, 24378), (364, 68230), (365, -4406), (366, 6432), (367, 55466), (368, 76), (369, -74352), (370, 58726), (371, 41828), (372, -3508), (373, 20590), (374, -19176), (375, -130090), (376, -26104), (377, -63192), (378, -37396), (379, -50666), (380, -45620), (381, -10432), (382, -16728), (383, -24954), (384, -42194), (385, -12582), (386, -23218), (387, -50012), (388, 15668), (389, -41014), (390, -12480), (391, -34464), (392, 25740), (393, -15764), (394, -5430), (395, -29976), (396, 10452), (397, 31760), (398, 20338), (399, 18214), (400, 2890), (401, -46716), (402, 20940), (403, 30434), (404, 18284), (405, 39126), (406, -25384), (407, -83828), (408, -27692), (409, 622), (410, -11584), (411, 28460), (412, -30170), (413, -40986), (414, 10416), (415, 51026), (416, 14848), (417, -74590), (418, 33666), (419, -23272), (420, 88784), (421, 7980), (422, 34192), (423, -18612), (424, 20816), (425, 9844), (426, 23764), (427, 61610), (428, 13396), (429, 54506), (430, 42016), (431, 20246), (432, 41300), (433, 20476), (434, -35160), (435, -25702), (436, 17542), (437, 8404), (438, 44820), (439, 40652), (440, -87204), (441, 3192), (442, 14876), (443, 8084), (444, 16776), (445, -75666), (446, -52866), (447, 11048), (448, -66234), (449, -61626), (450, -54717), (451, -39556), (452, -178810), (453, -6056), (454, -2958), (455, -39638), (456, -5221), (457, -28504), (458, -101776), (459, 5628), (460, 170494), (461, 14324), (462, 35836), (463, 33934), (464, 35816), (465, 33554), (466, 102546), (467, 22932), (468, 25398), (469, 12234), (470, -24064), (471, 23354), (472, 126398), (473, 23304), (474, 20044), (475, 27240), (476, -270), (477, -11044), (478, 168500), (479, 23124), (480, 30492), (481, 79050), (482, -6816), (483, -8184), (484, -59764), (485, 6198), (486, 12848), (487, 6550), (488, 4690), (489, 3908), (490, 67804), (491, 22220), (492, 13008), (493, 8448), (494, 10584), (495, 24304), (496, 13676), (497, -2332), (498, 22638), (499, 5030), (500, 39648), (501, -3130), (502, -24652), (503, -36826), (504, -40540), (505, -26152), (506, -12038), (507, -63158), (508, 3668), (509, 21758), (510, -3328), (511, -6760), (512, -17882), (513, 27796), (514, -19704), (515, -26878), (516, 12062), (517, 12962), (518, 88230), (519, -3746), (520, -15936), (521, -49380), (522, -3048), (523, -10860), (524, -11838), (525, 13516), (526, 6532), (527, 3838), (528, 38916), (529, 11332), (530, 3936), (531, 27486), (532, 36140), (533, 35162), (534, 16438), (535, -47444), (536, -32718), (537, -34816), (538, -11404), (539, -25186), (540, -5380), (541, -49568), (542, -85642), (543, -206056), (544, -42220), (545, -27710), (546, 24646), (547, -17294), (548, -44064), (549, -88978), (550, -22268), (551, -8746), (552, -9854), (553, -6500), (554, 2502), (555, -15982), (556, 36184), (557, 32246), (558, 4196), (559, 2326), (560, -11424), (561, 19468), (562, -9984), (563, 7474), (564, 41024), (565, 71816), (566, -5220), (567, -4300), (568, -6039), (569, -4470), (570, 4710), (571, -13278), (572, 47492), (573, -4198), (574, 7497), (575, -18226), (576, 17430), (577, 57236), (578, 1511), (579, 4944), (580, 16080), (581, -133150), (582, 14383), (583, 67172), (584, 152745), (585, -22000), (586, -548), (587, -22414), (588, 17456), (589, 12550), (590, -5712), (591, -13992), (592, 17592), (593, -61016), (594, -72260), (595, -32230), (596, -34120), (597, -5148), (598, 32838), (599, 40252), (600, -202592), (601, 69878), (602, 26960), (603, 40814), (604, -23014), (605, -46976), (606, 690), (607, 49986), (608, -143180), (609, 3700), (610, 49872), (611, -43710), (612, -23956), (613, 33180), (614, 35840), (615, 47616), (617, 49740), (618, -227284), (619, 64880), (620, 14648), (621, 24134), (622, 16364), (623, 32322), (624, 24262), (625, -15844), (626, -3112), (627, 9666), (628, -29580), (629, 39280), (630, -23122), (631, -6054), (632, -12622), (633, -162562), (634, -46210), (635, 56296), (636, 12012), (637, -62870), (638, -21348), (639, -9880), (640, -8246), (641, -18220), (642, -42548), (643, 350584), (644, -1800), (645, 5180), (646, 8960), (647, 12740), (648, 3660), (649, 32), (650, -468), (651, -18640), (652, -28084), (653, -110026), (654, -15856), (655, -42332), (656, -92128), (657, -54750), (658, -92930), (659, -69824), (660, -73996), (661, -48956), (662, -58636), (663, -64744), (664, -128888), (665, -9862), (666, -13602), (667, -12444), (668, -6780), (669, -13200), (670, -130140), (672, -2560), (673, -1760), (674, -22840), (675, -12400), (676, -56104), (677, -7408), (678, -11186), (679, -20544), (680, -14160), (681, -30126), (682, -35074), (683, -18064), (684, -29126), (685, -40400), (686, -32678), (687, -43392), (688, -19480), (689, -22678), (690, 137358), (691, -12312), (692, 24200), (693, 45174), (694, 69942), (695, 127110), (696, 186480), (697, 24772), (698, 138498), (700, -3840), (701, 15540), (702, -19948), (703, -45020), (704, -14460), (705, 203802), (706, 31984), (707, -7948), (708, 86680), (709, -20840), (710, -10320), (711, -5610), (712, -13550), (713, -5200), (714, -9430), (715, 1450), (716, -5490), (717, 3830), (718, -70570), (719, -492), (720, -402), (721, -1212), (722, -5936), (723, -14238), (724, -13512), (725, -7882), (726, -7882), (727, -4504), (728, -3378), (729, -2252), (730, 9216), (731, -768), (732, -3056), (733, 15104), (734, 13072), (735, -27200), (736, 22242), (737, 147024), (738, 60342), (739, 48590), (740, 22133), (741, -32108), (742, 108504), (743, 111548), (744, 45103), (745, -2546), (746, 3790), (747, -15180), (748, -11545), (749, -31832), (750, -40918), (751, -55808), (752, -37118), (753, 111922), (754, -30040), (755, 104004), (756, -21180), (757, -5200), (761, 114240), (762, 200), (763, 200), (764, 800), (765, 200), (766, 400), (767, 1200), (768, 1000), (769, 1000), (770, 112800), (771, 1000), (772, 200), (773, 108320), (776, 112600), (781, 15764), (784, 33780), (785, 49544), (786, 15764), (787, 63056), (788, 127238), (789, 15764), (790, -315280), (791, 28150), (792, -960), (793, -920), (794, -3640), (795, -460), (796, -309792), (797, -7390), (798, -14130), (799, -7310), (800, -6230), (801, -20250), (802, -13930), (803, -16640), (804, -2640), (805, -13080), (806, -2640), (807, -10400), (808, -288256), (812, -7980), (813, -12600), (814, -4200), (815, -7980), (816, -36120), (817, -3780), (818, -12600), (819, -15540), (820, -7980), (821, -7560), (822, -4200), (826, 12864), (827, 12136), (828, 47248), (829, 6260), (830, 11356), (831, 62262), (832, 48676), (833, 60554), (834, 12012), (835, 59246), (836, 11748), (837, 46280), (847, 21394), (848, 33780), (849, 11260), (850, 21394), (851, 96836), (852, 10134), (853, 33780), (854, 41687), (855, 21444), (856, 20493), (857, 11460), (858, 400), (863, -8400), (866, -8400), (867, -8400), (868, -8400), (870, -8400), (872, -8400), (888, -670), (889, -1330), (890, -5940), (891, -5240), (892, -10400), (893, 40320), (894, -1680), (895, -6720), (896, 32760), (897, 29400), (898, 61580), (900, 38220), (901, 22520), (902, 59900), (903, 22520), (905, 22520), (907, 22520), (922, 4489), (923, 8844), (924, 39196), (925, 34320), (926, 67600), (928, -108096), (929, 4504), (930, 18016), (931, -87828), (932, -78820), (933, -104718), (935, -102466), (937, -100214), (955, -2100), (956, -2100), (957, -8400), (989, 28140), (990, 33350), (991, 114830), (992, 22520), (1024, -75442), (1025, -74316), (1026, -292760), (1056, 44100), (1091, -236460), (1126, 316969)]
def wfData : Nat → List (Nat × Int)
  | 0 => wf0Data
  | 1 => wf1Data
  | 2 => wf2Data
  | 3 => wf3Data
  | 4 => wf4Data
  | _ => wf5Data
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
/-- Exact coverage histograms of j ordered ranks, for 1 ≤ j ≤ 8. -/
def coverageH1Data : List (Nat × Nat) := [(1, 563)]
def coverageH2Data : List (Nat × Nat) := [(1, 563), (2, 202), (3, 1884), (4, 5808), (5, 828), (6, 2232), (7, 1436), (8, 5280), (9, 12136), (10, 8060), (11, 3768), (12, 3040), (13, 1006), (14, 1336), (15, 11432), (16, 5468), (17, 7498), (18, 10728), (19, 8586), (20, 6298), (21, 14804), (22, 1384), (23, 5838), (24, 486), (25, 1040), (26, 6726), (27, 3920), (28, 5828), (29, 6214), (30, 8598), (31, 6230), (32, 11930), (33, 4788), (34, 7226), (35, 6120), (36, 3288), (37, 10666), (38, 2554), (39, 2912), (40, 1780), (41, 2530), (42, 1376), (43, 4818), (44, 1810), (45, 3020), (46, 3002), (47, 5022), (48, 1930), (49, 1664), (50, 2968), (51, 6908), (52, 1292), (53, 2492), (54, 4654), (55, 5350), (56, 4618), (57, 4804), (58, 3310), (59, 3522), (60, 1802), (61, 3638), (62, 1242), (63, 1232), (64, 418), (65, 2052), (66, 850), (67, 536), (68, 416), (69, 306), (70, 250), (71, 2840), (72, 592), (73, 726), (74, 718), (75, 432), (76, 776), (77, 546), (78, 2220), (79, 746), (80, 1548), (81, 1980), (82, 1858), (83, 930), (84, 1174), (85, 478), (86, 1206), (87, 558), (88, 852), (89, 1080), (90, 1036), (91, 746), (92, 596), (93, 430), (94, 584), (95, 214), (96, 122), (97, 48), (98, 72), (99, 24), (100, 44), (101, 68), (102, 64), (103, 96), (104, 392), (105, 176), (106, 72), (107, 88), (108, 76), (109, 72), (110, 48), (111, 144), (112, 308), (113, 284), (114, 208), (115, 248), (116, 272), (117, 200), (118, 160), (119, 124), (120, 104), (121, 112), (122, 64), (123, 24), (124, 48), (125, 18), (126, 48), (127, 24), (128, 72), (129, 66), (130, 42), (131, 36), (132, 42), (133, 36), (134, 84), (135, 60), (136, 48), (137, 12)]
def coverageH3Data : List (Nat × Nat) := [(1, 563), (2, 606), (3, 7596), (4, 29040), (5, 6996), (6, 25386), (7, 18486), (8, 84876), (9, 214326), (10, 158844), (11, 85242), (12, 99546), (13, 32550), (14, 56070), (15, 483822), (16, 233070), (17, 391830), (18, 584916), (19, 500040), (20, 421506), (21, 931194), (22, 121092), (23, 543360), (24, 37890), (25, 90846), (26, 746340), (27, 416562), (28, 730818), (29, 771528), (30, 1348218), (31, 848034), (32, 1657242), (33, 711828), (34, 1289940), (35, 1016406), (36, 583938), (37, 2273640), (38, 445002), (39, 638346), (40, 449628), (41, 720954), (42, 409362), (43, 1382484), (44, 579342), (45, 1028160), (46, 1302522), (47, 1896258), (48, 729750), (49, 616332), (50, 1180698), (51, 2754012), (52, 491904), (53, 1216788), (54, 1832022), (55, 2420280), (56, 2185104), (57, 2130468), (58, 1552296), (59, 2172870), (60, 1131492), (61, 2230182), (62, 994098), (63, 1078116), (64, 423846), (65, 1960626), (66, 919284), (67, 611610), (68, 453936), (69, 365016), (70, 367446), (71, 3464946), (72, 679752), (73, 730080), (74, 665772), (75, 482814), (76, 995262), (77, 1060404), (78, 3350646), (79, 1101474), (80, 2221188), (81, 2717520), (82, 2465226), (83, 1371702), (84, 1838142), (85, 750252), (86, 3078714), (87, 1136124), (88, 1519878), (89, 1952826), (90, 2217882), (91, 1725432), (92, 1237656), (93, 968592), (94, 1574286), (95, 1395990), (96, 649866), (97, 395532), (98, 832740), (99, 354936), (100, 528288), (101, 811194), (102, 404874), (103, 808422), (104, 2278974), (105, 781152), (106, 356196), (107, 501024), (108, 708528), (109, 646212), (110, 890478), (111, 956718), (112, 2035254), (113, 2189370), (114, 1927452), (115, 1810974), (116, 1988442), (117, 1847616), (118, 1404504), (119, 1064994), (120, 1116216), (121, 934932), (122, 1529508), (123, 482028), (124, 333624), (125, 165552), (126, 738900), (127, 424896), (128, 874998), (129, 999642), (130, 625116), (131, 572262), (132, 826926), (133, 1346490), (134, 1059378), (135, 1237104), (136, 1868298), (137, 1293666), (138, 686658), (139, 641424), (140, 473256), (141, 514140), (142, 553950), (143, 528696), (144, 282948), (145, 257082), (146, 549090), (147, 725010), (148, 339426), (149, 621522), (150, 168816), (151, 144420), (152, 379080), (153, 500742), (154, 843780), (155, 612888), (156, 1203132), (157, 1624194), (158, 1017276), (159, 944094), (160, 1239636), (161, 1058658), (162, 415200), (163, 400494), (164, 69984), (165, 826680), (166, 492600), (167, 499044), (168, 311796), (169, 186954), (170, 62400), (171, 371850), (172, 821460), (173, 209370), (174, 517638), (175, 329136), (176, 204132), (177, 120816), (178, 226188), (181, 65412), (182, 724638), (183, 762480), (184, 1027836), (185, 1115706), (186, 459432), (187, 407640), (188, 460482), (189, 385002), (190, 132456), (191, 129834), (193, 28800), (196, 165312), (197, 336426), (198, 404700), (199, 181122), (200, 221490), (201, 937380), (202, 101886), (203, 327792), (204, 398784), (205, 207708), (206, 195480), (207, 98352), (209, 8964), (210, 53784), (211, 35856), (212, 71712), (213, 98604), (214, 465576), (215, 696348), (216, 661626), (217, 443628), (218, 54720), (219, 55908), (220, 37206), (222, 35910), (224, 36486), (226, 100512), (227, 152316), (228, 50310), (229, 101970), (230, 457758), (231, 50526), (232, 149292), (233, 199368), (234, 136608), (235, 251064), (236, 201816), (237, 223776), (245, 58068), (246, 132780), (247, 200094), (248, 255246), (249, 188076), (250, 58068), (252, 56340), (254, 56916), (255, 15840), (256, 23760), (257, 7920), (258, 15840), (259, 71280), (260, 7920), (261, 23760), (262, 31680), (263, 15840), (264, 15840), (265, 7920), (267, 50772), (268, 201348), (269, 200952), (270, 296352), (275, 27108), (278, 36180), (279, 41148), (280, 40860), (281, 9216), (282, 26460), (284, 26604), (291, 14112), (292, 14112), (293, 54432), (300, 20232), (301, 80496), (302, 80352), (303, 119232), (305, 3600), (308, 3600), (309, 3600), (310, 3600), (312, 3600), (314, 3600), (325, 19872), (326, 19872), (327, 77472), (333, 2304), (334, 9216), (335, 9216), (336, 13824), (353, 5760), (359, 9288), (360, 9288), (361, 36648), (388, 8640), (393, 1440), (394, 1440), (395, 5760), (423, 4320), (458, 720)]
def coverageH4Data : List (Nat × Nat) := [(1, 563), (2, 1414), (3, 24852), (4, 121968), (5, 43428), (6, 193476), (7, 160400), (8, 854736), (9, 2421004), (10, 2003900), (11, 1170780), (12, 1803604), (13, 599482), (14, 1296340), (15, 10911212), (16, 5403080), (17, 10040254), (18, 16009560), (19, 14286882), (20, 13115422), (21, 30591248), (22, 4294720), (23, 22250286), (24, 1550898), (25, 3989180), (26, 36221958), (27, 20074532), (28, 37801136), (29, 40109350), (30, 80374890), (31, 47403290), (32, 96615254), (33, 41740332), (34, 86601794), (35, 64642068), (36, 39321948), (37, 173063290), (38, 31828294), (39, 51349892), (40, 40416316), (41, 65646286), (42, 39258524), (43, 132561810), (44, 56829694), (45, 105783932), (46, 154930574), (47, 203466234), (48, 80787166), (49, 67804208), (50, 139730068), (51, 325545188), (52, 61221836), (53, 158776340), (54, 225862186), (55, 322366270), (56, 285359842), (57, 282631924), (58, 202217158), (59, 324605214), (60, 183701714), (61, 337118210), (62, 167119446), (63, 192648080), (64, 79571686), (65, 374867928), (66, 180866602), (67, 123086180), (68, 91945304), (69, 76388370), (70, 87966358), (71, 740802764), (72, 143413384), (73, 151982286), (74, 140164894), (75, 106937028), (76, 235434164), (77, 263387994), (78, 810977424), (79, 270853814), (80, 556793148), (81, 679081740), (82, 612152326), (83, 366910302), (84, 496944730), (85, 200685790), (86, 926349858), (87, 317439774), (88, 386030232), (89, 503313204), (90, 610946176), (91, 505161890), (92, 346662596), (93, 283498366), (94, 524519516), (95, 521032402), (96, 243383606), (97, 155977488), (98, 326604624), (99, 151490304), (100, 228142460), (101, 354594992), (102, 164267860), (103, 371914860), (104, 966564884), (105, 321768536), (106, 156261912), (107, 227723392), (108, 330427852), (109, 302536128), (110, 474836556), (111, 400181364), (112, 869586464), (113, 1002373160), (114, 911699728), (115, 827675396), (116, 924639212), (117, 925490936), (118, 687369448), (119, 549056776), (120, 533089136), (121, 454640392), (122, 933931144), (123, 305067888), (124, 177063648), (125, 86375586), (126, 452039112), (127, 234267216), (128, 448072644), (129, 510108894), (130, 332588202), (131, 327379224), (132, 478808118), (133, 914085816), (134, 581482416), (135, 755536788), (136, 1265939316), (137, 883620216), (138, 479283372), (139, 441242304), (140, 365501592), (141, 425905512), (142, 487237764), (143, 419583768), (144, 218453808), (145, 205397532), (146, 438077340), (147, 612903492), (148, 278157204), (149, 523105836), (150, 144267864), (151, 124509552), (152, 455092560), (153, 457737684), (154, 709588512), (155, 561550128), (156, 1039315560), (157, 1389899028), (158, 884303112), (159, 837426012), (160, 1148247792), (161, 1010362284), (162, 390246384), (163, 374377164), (164, 69986880), (165, 796832976), (166, 459235320), (167, 519178344), (168, 347494632), (169, 187970052), (170, 63650832), (171, 539300964), (172, 956451744), (173, 304538556), (174, 702210948), (175, 386657880), (176, 258910056), (177, 131540544), (178, 322992384), (179, 6219360), (180, 7774200), (181, 89014944), (182, 892933548), (183, 910488720), (184, 1281775680), (185, 1478303820), (186, 632567808), (187, 595741608), (188, 645239412), (189, 542635980), (190, 202736136), (191, 185447028), (193, 96787920), (196, 323912400), (197, 639247476), (198, 712610712), (199, 408988932), (200, 407817468), (201, 1653373920), (202, 178561908), (203, 629442480), (204, 703181352), (205, 397580088), (206, 353948544), (207, 186834720), (209, 19225944), (210, 115374768), (211, 77928312), (212, 158122032), (213, 221579232), (214, 885463800), (215, 1309298688), (216, 1254155364), (217, 851970840), (218, 113019768), (219, 110013696), (220, 68453100), (221, 12938544), (222, 85285404), (223, 6469272), (224, 94005108), (225, 13592232), (226, 312339624), (227, 461408904), (228, 168189420), (229, 315687348), (230, 1413496908), (231, 157272756), (232, 466435656), (233, 621929928), (234, 402898488), (235, 691372680), (236, 537633912), (237, 563948064), (245, 180433320), (246, 436007976), (247, 654614964), (248, 825244116), (249, 611539824), (250, 184564080), (252, 178371072), (254, 182870880), (255, 106475784), (256, 160215456), (257, 53716512), (258, 108345984), (259, 485865384), (260, 54026544), (261, 160952688), (262, 214902720), (263, 106608480), (264, 107293632), (265, 53902944), (267, 211387896), (268, 841501728), (269, 840141288), (270, 1243924800), (275, 168243960), (278, 240876480), (279, 282931608), (280, 277461600), (281, 70017024), (282, 165881712), (284, 180778368), (285, 18134712), (286, 6044904), (287, 12089808), (288, 54404136), (289, 6044904), (290, 18134712), (291, 97962528), (292, 86000016), (293, 301726992), (294, 6044904), (300, 154993128), (301, 617464896), (302, 615413928), (303, 912059856), (305, 64630368), (308, 64529664), (309, 65634624), (310, 64982496), (312, 63948960), (314, 64500384), (325, 171043896), (326, 171166224), (327, 671820768), (333, 44051520), (334, 175789824), (335, 183925632), (336, 260515968), (338, 8764800), (339, 8764800), (340, 8764800), (342, 8764800), (344, 8764800), (353, 48455424), (359, 139337400), (360, 139351008), (361, 549002640), (366, 3887616), (367, 15550464), (368, 15550464), (369, 23325696), (388, 116063424), (393, 47514720), (394, 47507232), (395, 188319552), (423, 100156176), (427, 5723520), (428, 5723520), (429, 22894080), (458, 37098720), (493, 4994640)]
def coverageH5Data : List (Nat × Nat) := [(1, 563), (2, 3030), (3, 76860), (4, 493680), (5, 241380), (6, 1290330), (7, 1230390), (8, 7500300), (9, 23950230), (10, 22135140), (11, 14035890), (12, 26504850), (13, 9176670), (14, 23978430), (15, 198355470), (16, 102221430), (17, 204966270), (18, 350039460), (19, 325107480), (20, 320504130), (21, 804350250), (22, 116976540), (23, 688782240), (24, 48947490), (25, 134309550), (26, 1301624340), (27, 725827050), (28, 1439280330), (29, 1547203560), (30, 3468864090), (31, 1956673290), (32, 4144781250), (33, 1808704980), (34, 4170500340), (35, 2989122750), (36, 1896330810), (37, 9407894040), (38, 1661351850), (39, 2959680930), (40, 2513556180), (41, 4091347290), (42, 2556309450), (43, 8708479620), (44, 3783662310), (45, 7311800400), (46, 12141159090), (47, 14643308850), (48, 5993269710), (49, 5026581180), (50, 11153786850), (51, 25682448780), (52, 5081115480), (53, 13542400020), (54, 18562322670), (55, 28378274400), (56, 24591881640), (57, 24920989380), (58, 17679799800), (59, 31520373510), (60, 19451631660), (61, 33042359070), (62, 17686447050), (63, 21354705300), (64, 9120316950), (65, 43969456650), (66, 21523883820), (67, 14947712370), (68, 11279575200), (69, 9646826760), (70, 12488323590), (71, 95466684450), (72, 18209955840), (73, 19246107480), (74, 18141244980), (75, 14361399870), (76, 33291226590), (77, 38023435620), (78, 116395822230), (79, 39442319730), (80, 82858645500), (81, 100765593960), (82, 90330067170), (83, 57385208310), (84, 78543805830), (85, 31504609620), (86, 158806946250), (87, 51948373380), (88, 58562666910), (89, 77323454370), (90, 99153751410), (91, 85972732320), (92, 57356765400), (93, 48871113480), (94, 98591366670), (95, 104752020030), (96, 49579895730), (97, 32695741020), (98, 68070404220), (99, 33430453320), (100, 51268769160), (101, 81626979450), (102, 35669896050), (103, 87161988750), (104, 216012039510), (105, 70805266800), (106, 36150285300), (107, 54181497600), (108, 80181295080), (109, 73934504220), (110, 125384948670), (111, 90461599950), (112, 199947946230), (113, 243729790890), (114, 225540870420), (115, 201092641590), (116, 227273424690), (117, 239306226600), (118, 175248393720), (119, 146470985730), (120, 133602489840), (121, 115566873300), (122, 278164118820), (123, 91915355340), (124, 47474706720), (125, 22818282600), (126, 135407623860), (127, 65210693280), (128, 116028087030), (129, 132324081930), (130, 89254842060), (131, 94149122430), (132, 139158012510), (133, 297038992890), (134, 160825668570), (135, 230220670680), (136, 418970722290), (137, 294535773930), (138, 163036034130), (139, 148941408240), (140, 133434925920), (141, 161680009140), (142, 191654545110), (143, 152151920520), (144, 78971187540), (145, 76227882930), (146, 158465317290), (147, 232213177170), (148, 102917083170), (149, 194284706730), (150, 54367799520), (151, 46753754820), (152, 216608639400), (153, 183877502550), (154, 270356925780), (155, 230059006680), (156, 404581982100), (157, 540453787650), (158, 347551292820), (159, 335583349590), (160, 479502454620), (161, 432494954610), (162, 166190045040), (163, 158764209390), (164, 31831191240), (165, 340649364360), (166, 190767719880), (167, 238017899220), (168, 155756014140), (169, 78686988810), (170, 26948118600), (171, 286248792690), (172, 441903647580), (173, 166361913570), (174, 354840233190), (175, 183362087160), (176, 127514367060), (177, 59509520400), (178, 169303752780), (179, 5658668640), (180, 7029631440), (181, 48080110980), (182, 447498223950), (183, 444013584120), (184, 649649777460), (185, 796624887690), (186, 349508323320), (187, 347372640120), (188, 361935631770), (189, 307932208410), (190, 121561660560), (191, 106652245770), (193, 78282061800), (196, 207217785840), (197, 402604377210), (198, 438252578100), (199, 274079852490), (200, 255143672850), (201, 1022305565100), (202, 110571493350), (203, 407558458320), (204, 443980828440), (205, 270994875420), (206, 227399097000), (207, 126896658240), (209, 14123790540), (210, 84882710280), (211, 57660205680), (212, 117843403920), (213, 171663868140), (214, 596182364280), (215, 878191069260), (216, 850380974010), (217, 586081538940), (218, 82430153640), (219, 78814463820), (220, 47087702190), (221, 12997529040), (222, 65620679550), (223, 6606775320), (224, 74528815710), (225, 18349474440), (226, 263546625720), (227, 389279758260), (228, 145823520270), (229, 269371201170), (230, 1210533135870), (231, 135558620190), (232, 406508013540), (233, 545090703480), (234, 342939013080), (235, 564605545800), (236, 430355345640), (237, 434971017120), (245, 171076221060), (246, 407255069340), (247, 612219604830), (248, 780991051230), (249, 584780854980), (250, 179016925260), (252, 175390974420), (254, 181662718260), (255, 123826511040), (256, 186606683280), (257, 63469849320), (258, 127971282960), (259, 574212390600), (260, 64162041600), (261, 192618508560), (262, 258157207200), (263, 128328779040), (264, 129903077760), (265, 65554227120), (267, 224231020860), (268, 897226474980), (269, 898657275720), (270, 1341532802160), (275, 226590037500), (278, 325705663500), (279, 383138055180), (280, 377536523940), (281, 94144312320), (282, 230608779420), (284, 256445001300), (285, 29621699880), (286, 10049744520), (287, 20074043400), (288, 90039671520), (289, 10038934440), (290, 30230988720), (291, 131678830800), (292, 111728793960), (293, 383404297920), (294, 10174468080), (300, 228229143120), (301, 911907479520), (302, 910066244040), (303, 1355606969640), (305, 130572961200), (308, 131474586480), (309, 135069797040), (310, 133653307920), (312, 131894367600), (314, 134235671280), (325, 292115972040), (326, 292828825080), (327, 1159284803640), (333, 91151461920), (334, 364145646720), (335, 394384450200), (336, 539289753120), (338, 32237553840), (339, 32691927840), (340, 32514925560), (342, 32299391400), (344, 32592401640), (353, 91392604800), (359, 332158390320), (360, 332402886000), (361, 1315944665160), (365, 2532000000), (366, 12035487120), (367, 48141209760), (368, 50297471040), (369, 73729347840), (370, 2532000000), (372, 2532000000), (374, 2532000000), (388, 298125938040), (393, 167081161920), (394, 167000444160), (395, 662154762720), (423, 360351509760), (427, 36323677080), (428, 36286468680), (429, 144341293680), (458, 202619729040), (461, 2536250880), (462, 2536250880), (463, 10145003520), (493, 52945669800), (528, 5102244720)]
def coverageH6Data : List (Nat × Nat) := [(1, 563), (2, 6262), (3, 233364), (4, 1980528), (5, 1276548), (6, 8142252), (7, 8990936), (8, 62481840), (9, 225193396), (10, 232160900), (11, 160268748), (12, 354834820), (13, 129747226), (14, 397276516), (15, 3283985012), (16, 1775665448), (17, 3808805278), (18, 6964747128), (19, 6740311506), (20, 7084698358), (21, 19149543704), (22, 2864492824), (23, 18754851198), (24, 1366242426), (25, 3984131060), (26, 40633629126), (27, 23026373780), (28, 47689227728), (29, 52257196534), (30, 129015729138), (31, 70607198810), (32, 155077818470), (33, 68782499868), (34, 172892334386), (35, 120537914580), (36, 79216101948), (37, 438056484586), (38, 75198221374), (39, 145873497812), (40, 130928153380), (41, 213784899430), (42, 138812317916), (43, 479233684338), (44, 210701582350), (45, 420183861020), (46, 779547395582), (47, 877723003122), (48, 369942284350), (49, 311353005104), (50, 740986830148), (51, 1680060572708), (52, 349322093972), (53, 950383230212), (54, 1267142600554), (55, 2066389948390), (56, 1755544998538), (57, 1822367365924), (58, 1292436510070), (59, 2509344123702), (60, 1683612688202), (61, 2656933014578), (62, 1512788907462), (63, 1892405421392), (64, 829168059838), (65, 4094897492952), (66, 2024371617730), (67, 1434425873876), (68, 1095016102376), (69, 962270386626), (70, 1393333106110), (71, 9719540958500), (72, 1831006196992), (73, 1938306357366), (74, 1869164477878), (75, 1527084978732), (76, 3699012974876), (77, 4286085829386), (78, 13117779571560), (79, 4505510396606), (80, 9675338065908), (81, 11723438094420), (82, 10459366356598), (83, 6977432527590), (84, 9660531237514), (85, 3862737825238), (86, 20986404811866), (87, 6658256978118), (88, 7063196626632), (89, 9438703788660), (90, 12697363140496), (91, 11444622209306), (92, 7504811744996), (93, 6647614243030), (94, 14253507710564), (95, 15864366078994), (96, 7623165180422), (97, 5127546581808), (98, 10651725601032), (99, 5474678954304), (100, 8555792955764), (101, 13983916133048), (102, 5812284615604), (103, 15061435047036), (104, 35946414003572), (105, 11646430477736), (106, 6219871237992), (107, 9549847346368), (108, 14400511394356), (109, 13390243669752), (110, 24154992050628), (111, 15419960974764), (112, 34570232536088), (113, 44263060327904), (114, 41486673797608), (115, 36526811101508), (116, 41731009914332), (117, 45714517934240), (118, 33154974655240), (119, 28940726677024), (120, 24926704201304), (121, 21839978111992), (122, 59845680226504), (123, 19895529159264), (124, 9426285462888), (125, 4492611252618), (126, 29882934970728), (127, 13482437726544), (128, 22385527469772), (129, 25607543924886), (130, 17819593158282), (131, 20094764825976), (132, 29865344964942), (133, 69372028728336), (134, 33061567722384), (135, 51561446616300), (136, 100248021721428), (137, 70713116583432), (138, 39832344418500), (139, 36171649554240), (140, 34631337981600), (141, 43021580846880), (142, 52495432013220), (143, 38874683065080), (144, 20143678133760), (145, 19862483517180), (146, 40433313524220), (147, 61715793068460), (148, 26782969003020), (149, 50698305126300), (150, 14367045196200), (151, 12320853678480), (152, 69018918469200), (153, 51549743399340), (154, 72595393392240), (155, 66230041935360), (156, 110870995515600), (157, 148096218699420), (158, 95993083247280), (159, 94404438092460), (160, 140430152222280), (161, 129472953170580), (162, 49645203134640), (163, 47166053078820), (164, 10097706117240), (165, 101698761583680), (166, 55450823493000), (167, 75860517051480), (168, 47703085278960), (169, 22769090145420), (170, 7861970559720), (171, 101453572592340), (172, 139427763849720), (173, 60486784519740), (174, 120330129927180), (175, 59424830500080), (176, 42517732197960), (177, 18488915033760), (178, 59209876546320), (179, 2792003253120), (180, 3481906609080), (181, 17361495053520), (182, 152596101661860), (183, 148065163164600), (184, 223882513853400), (185, 290391455028420), (186, 129380602847040), (187, 135223456475880), (188, 135914708115540), (189, 116945081315220), (190, 48548375548080), (191, 41005112622540), (193, 38100032672280), (196, 85305262414800), (197, 163907161758780), (198, 175437266230800), (199, 116837507406180), (200, 103537055581380), (201, 411969406713720), (202, 44669388407220), (203, 170577179353680), (204, 182858833213440), (205, 120203408321160), (206, 95034040339680), (207, 56166764379360), (209, 6598536799680), (210, 39857752536960), (211, 27217381123320), (212, 55909610401440), (213, 84627529692240), (214, 259962152795400), (215, 381976294787280), (216, 374052789993420), (217, 261154324265160), (218, 38528602158960), (219, 36300252963240), (220, 20831734036620), (221, 7339656265920), (222, 31897895489820), (223, 3776726167200), (224, 37084802308020), (225, 12703792399920), (226, 136308430894800), (227, 202115849016960), (228, 77001357821820), (229, 140995043269740), (230, 637465876720020), (231, 71839973575740), (232, 217410544620720), (233, 293842014242280), (234, 180839286502320), (235, 287217302725560), (236, 215184294644280), (237, 209442727301040), (245, 97700794481640), (246, 231641413556520), (247, 349785166393980), (248, 450372510355980), (249, 339472724487720), (250, 104555935383480), (252, 104206359510720), (254, 108858169531920), (255, 82304455948680), (256, 124496642073120), (257, 42689810373720), (258, 86268151904160), (259, 388662848564880), (260, 43666085073120), (261, 131991293836800), (262, 177830928931680), (263, 88861613178720), (264, 90365638000800), (265, 45804388727520), (267, 140352890816880), (268, 564768323283600), (269, 568660130852760), (270, 855615681901200), (275, 168132521914080), (278, 244323952880280), (279, 287737302878520), (280, 285591793803960), (281, 71260582410240), (282, 177545042142720), (284, 200380438003560), (285, 25129085516640), (286, 8604182417760), (287, 17224824747240), (288, 77407886830680), (289, 8672019263280), (290, 26224088090760), (291, 99283618718880), (292, 82129926762600), (293, 276022738010400), (294, 8965805028840), (300, 185645022983040), (301, 744656819092320), (302, 746351176032240), (303, 1118669928287400), (305, 126245940235200), (308, 128672953436640), (309, 132645251685600), (310, 131853711657120), (312, 131360633184960), (314, 134693864260800), (325, 266012074584240), (326, 267498713264280), (327, 1067049097021800), (333, 95232446587680), (334, 381229167711360), (335, 421793488384440), (336, 568830128990880), (338, 41850504297840), (339, 42651612765120), (340, 42526237009800), (342, 42463061008680), (344, 43160215385640), (353, 92792959672320), (359, 388103670759840), (360, 389226637894920), (361, 1549623496415280), (365, 4666032000000), (366, 16193099084640), (367, 64764475716480), (368, 69090953516160), (369, 100855825543440), (370, 4739688000000), (372, 4747032000000), (374, 4782024000000), (388, 386224391538360), (393, 251092973558400), (394, 251246662923840), (395, 999529428194400), (423, 596533817903760), (427, 72046858416600), (428, 71953774272840), (429, 286367361484800), (458, 437404506590880), (461, 7226437985280), (462, 7206663490560), (463, 28730059983360), (493, 158424503090040), (528, 25850937790800), (563, 1323551250000)]
def coverageH7Data : List (Nat × Nat) := [(1, 563), (2, 12726), (3, 703836), (4, 7927920), (5, 6584676), (6, 50094786), (7, 64300446), (8, 509231436), (9, 2071292286), (10, 2379410124), (11, 1794208962), (12, 4533544386), (13, 1765362270), (14, 6188518350), (15, 51953043702), (16, 29636608470), (17, 67757302830), (18, 132508545876), (19, 133897396920), (20, 149383151946), (21, 433386520434), (22, 66749052132), (23, 477413180160), (24, 35787330810), (25, 110490981846), (26, 1177811793060), (27, 683233449402), (28, 1471377734778), (29, 1651228909848), (30, 4432743750498), (31, 2382468252234), (32, 5418369700002), (33, 2454368696388), (34, 6632138636340), (35, 4550435961246), (36, 3088341211578), (37, 18772944403080), (38, 3164775580722), (39, 6602939687106), (40, 6188730408588), (41, 10171251146994), (42, 6837708566682), (43, 23993617623444), (44, 10678732190742), (45, 21897675599520), (46, 44777602807602), (47, 47783382973578), (48, 20723932961550), (49, 17561246478972), (50, 44540266358658), (51, 99549576364812), (52, 21723211335504), (53, 60128919677988), (54, 78571711875342), (55, 136144632236760), (56, 113644505733024), (57, 120844921239588), (58, 86130524719176), (59, 179503942025310), (60, 130138117600932), (61, 192305405882142), (62, 115361546523258), (63, 148380380609076), (64, 66398840489646), (65, 335929847434986), (66, 167434888454484), (67, 121066582830690), (68, 93567221491296), (69, 84366464828856), (70, 135923345754126), (71, 870259421700186), (72, 162477752844792), (73, 172761960045360), (74, 170287363599612), (75, 143094565869654), (76, 360136394454102), (77, 422589786766644), (78, 1296300664601166), (79, 451233038770794), (80, 990611046438468), (81, 1195786664323440), (82, 1063180217901186), (83, 739768616568702), (84, 1036575045629382), (85, 414386303911692), (86, 2402755988836434), (87, 746807054280924), (88, 755253578863518), (89, 1021186480227186), (90, 1432082627778642), (91, 1333974019005432), (92, 866997862217256), (93, 796425805789152), (94, 1783967521401366), (95, 2054909655208830), (96, 1002815352874146), (97, 685242044486412), (98, 1425224996899620), (99, 761232575308296), (100, 1211134382839248), (101, 2032413649363314), (102, 809215243438434), (103, 2201041127354622), (104, 5085471277295094), (105, 1633431528611232), (106, 909297589183956), (107, 1425919669821024), (108, 2188833600190608), (109, 2053514393366772), (110, 3908052013923078), (111, 2254808168553318), (112, 5117786492109774), (113, 6847085523874050), (114, 6488825058710652), (115, 5661483846255174), (116, 6540403343949762), (117, 7397690383971216), (118, 5330986484013624), (119, 4853492690135754), (120, 3961463471447496), (121, 3513417986266692), (122, 10746686395562628), (123, 3588958285305708), (124, 1592001419318184), (125, 757488553813152), (126, 5593029194812500), (127, 2377630760449056), (128, 3703134251763198), (129, 4251836649309522), (130, 3047791500821676), (131, 3660851940194862), (132, 5449905651421686), (133, 13504022280205170), (134, 5815588950933258), (135, 9777086366506704), (136, 20045811622328898), (137, 14152373253699786), (138, 8094541548651978), (139, 7313849872005264), (140, 7431100017918696), (141, 9391098028177740), (142, 11759770972634790), (143, 8199199085850696), (144, 4236246214229988), (145, 4253677629550482), (146, 8529927115784970), (147, 13505285693771130), (148, 5753413826085786), (149, 10929257762761002), (150, 3131691191219136), (151, 2683577887971540), (152, 17600018895544680), (153, 11875793287383102), (154, 16123627551094980), (155, 15737537379018168), (156, 25123149767379132), (157, 33546214387140714), (158, 21874734830817036), (159, 21886446998326134), (160, 33859993045187316), (161, 31848421251519978), (162, 12200557241765760), (163, 11516383213065654), (164, 2616371423322384), (165, 24972420210339000), (166, 13277565739059720), (167, 19819573175633364), (168, 11927040489435876), (169, 5421669799076034), (170, 1884680961495360), (171, 28952371157835090), (172, 35919202899871620), (173, 17633845501156290), (174, 32979256938128718), (175, 15712849189699536), (176, 11508773159825172), (177, 4699834248728976), (178, 16667775641805708), (179, 1020389914555200), (180, 1281788343022320), (181, 5030550911443092), (182, 42273822746357958), (183, 40298098679435520), (184, 62651867244035916), (185, 85521458407846146), (186, 38401587767652312), (187, 42137357570311080), (188, 40892026254932202), (189, 35549866194275202), (190, 15514378623467976), (191, 12612731564880594), (193, 14191738206280320), (196, 27732881326078992), (197, 52872735838423746), (198, 55771137424860060), (199, 39222916139527722), (200, 33357692224131450), (201, 131973194170048980), (202, 14344734214795446), (203, 56532496336161552), (204, 59769335789029104), (205, 42299724356091468), (206, 31477051331565000), (207, 19768919867711952), (209, 2407116787691364), (210, 14635145560046424), (211, 10044973376511696), (212, 20726515310762352), (213, 32582002018368684), (214, 89719153876031736), (215, 131559466072763148), (216, 130217254619819346), (217, 91989342538041228), (218, 14171514212358720), (219, 13181543541052068), (220, 7269368673591486), (221, 3123601287404640), (222, 12155700979105950), (223, 1624371781201680), (224, 14436791916167166), (225, 6364598105266800), (226, 54362985496752912), (227, 81024494534756556), (228, 31281514294242030), (229, 56902859083900410), (230, 259019276786689398), (231, 29368024582602006), (232, 89570360403629532), (233, 122082723087331608), (234, 73883691740696208), (235, 113835857581713624), (236, 84011437518420216), (237, 78772915429794096), (245, 42610426284931428), (246, 100951411851977820), (247, 153300143956428294), (248, 198914852848205046), (249, 150716508993788556), (250, 46569819120009108), (252, 47204587791161220), (254, 49710283866681396), (255, 40909262336624640), (256, 62178664810343760), (257, 21429440334051120), (258, 43463947700754000), (259, 196879270262519040), (260, 22237364015406960), (261, 67634044631862240), (262, 91636811585208960), (263, 46066482171141600), (264, 47041763658345120), (265, 23949033216748080), (267, 66497197777185252), (268, 269154487857640308), (269, 272581454259710232), (270, 413077814662014432), (275, 91704737798726388), (278, 135004067784917940), (279, 159225913437290028), (280, 159221392836822540), (281, 39918195299652096), (282, 100505362040624940), (284, 114961751935723644), (285, 15418353463464000), (286, 5307662550612240), (287, 10664936568899760), (288, 48120380964223680), (289, 5417023865939280), (290, 16452607447859520), (291, 55678816651015152), (292, 45015985179742752), (293, 147899198486856432), (294, 5724462475974480), (300, 110686811865589512), (301, 446057826068864016), (302, 449368460981807472), (303, 677688155044273632), (305, 85584875474584080), (308, 88376187876619440), (309, 91256055135294000), (310, 91236584770569840), (312, 91912591671386640), (314, 94910613132392400), (325, 174628259412407472), (326, 176314347963486432), (327, 708043832259868272), (333, 70331953481611584), (334, 282490020898020096), (335, 317936513547833376), (336, 425522750440705344), (338, 35570475439670640), (339, 36349534705713600), (340, 36398845891742880), (342, 36644731502494080), (344, 37500875450186400), (353, 67352218791332160), (359, 315379420678158648), (360, 317340252884323368), (361, 1270447784891098968), (365, 4918930044000000), (366, 14685939062422320), (367, 58844408185264800), (368, 63742996121471520), (369, 93052332645209280), (370, 5080627104000000), (372, 5116552224000000), (374, 5189545536000000), (388, 346084507940369520), (393, 250543021215637920), (394, 251347236176719200), (395, 1004121639201055200), (423, 655028615540305440), (427, 88358016328137360), (428, 88404599147494560), (429, 352742076270843840), (458, 589192063654741680), (461, 11069404246279680), (462, 11048518925445120), (463, 44069871152590080), (493, 265594732576906320), (528, 56267910788685120), (563, 4243305307500000)]
def coverageH8Data : List (Nat × Nat) := [(1, 563), (2, 25654), (3, 2117172), (4, 31717488), (5, 33514308), (6, 304457796), (7, 455140400), (8, 4109759376), (9, 18856002604), (10, 24114901100), (11, 19912008300), (12, 56477488804), (13, 23547141322), (14, 92894639620), (15, 802710624332), (16, 484909594520), (17, 1179687956014), (18, 2463730052760), (19, 2604705811362), (20, 3075457510942), (21, 9536393037968), (22, 1516677665200), (23, 11696428922766), (24, 905204377458), (25, 2948762005340), (26, 32739478642758), (27, 19539628820852), (28, 43649204112896), (29, 50341238033350), (30, 145430451997770), (31, 77557920365450), (32, 182493569503814), (33, 84713188316652), (34, 243512880317954), (35, 166051335117348), (36, 116213725244748), (37, 766278716256730), (38, 127965258090214), (39, 284191431825812), (40, 276196849464076), (41, 458518652671726), (42, 318269862397484), (43, 1137513245187090), (44, 512996533697134), (45, 1079369655065852), (46, 2402739461183774), (47, 2462706300242394), (48, 1098336079650766), (49, 939632998424048), (50, 2522020627994308), (51, 5575582041396548), (52, 1274106759744956), (53, 3582150476406740), (54, 4617905601516346), (55, 8466935814633550), (56, 6963497493009202), (57, 7582238185697044), (58, 5449744614547078), (59, 12056402295830334), (60, 9374778832041794), (61, 13097065358063090), (62, 8221179536025606), (63, 10817185112694800), (64, 4930357486239526), (65, 25544584035087048), (66, 12831196470636442), (67, 9467983950813140), (68, 7411670569869464), (69, 6848560330706610), (70, 12192010155987478), (71, 72193158653635724), (72, 13406227221705784), (73, 14347530021110046), (74, 14436421259160814), (75, 12445581034838628), (76, 32394494184895604), (77, 38476010329292634), (78, 118482550642112784), (79, 41806537700969654), (80, 93829791638461068), (81, 112884938206086780), (82, 100183145314549846), (83, 72319890585298782), (84, 102569341600123690), (85, 41091598288822510), (86, 252176154091945218), (87, 77303137942923534), (88, 75365721083983272), (89, 103089604060135044), (90, 149853681118032976), (91, 143656675798090130), (92, 93125902068426116), (93, 88480017214366606), (94, 204599980936323836), (95, 242060821217215522), (96, 119946754813827686), (97, 83095793600934288), (98, 173512010049251904), (99, 95822718181432224), (100, 154996388965658060), (101, 266918899757276912), (102, 102465766718497540), (103, 290395541734506780), (104, 652259728349460644), (105, 208272446611384856), (106, 120473170913395512), (107, 192483817386311392), (108, 300388767245176252), (109, 284415916102949808), (110, 567705774404676396), (111, 301020539535973044), (112, 690851110738988864), (113, 961426371067720520), (114, 920493879840919648), (115, 798247937182694036), (116, 932929251228204572), (117, 1083143754274198376), (118, 777694247702783368), (119, 737345413322446696), (120, 572479918095341696), (121, 513713520271488712), (122, 1726368736945202344), (123, 578919947668484208), (124, 244065517782317328), (125, 116600619878805906), (126, 946279319464866792), (127, 381214745055755376), (128, 560663299129812804), (129, 646496021409771774), (130, 476810734321615722), (131, 607120419823736904), (132, 903317253826955478), (133, 2351066092116294456), (134, 934398498551480256), (135, 1677484123760172228), (136, 3589759397925071076), (137, 2533688873552203176), (138, 1469134520754057612), (139, 1322061960487068864), (140, 1417527535047726312), (141, 1813522866657794712), (142, 2325971834858747124), (143, 1539305998849572408), (144, 792138753484435728), (145, 808159747848692652), (146, 1604321535130394220), (147, 2625246427098191652), (148, 1100743161103219284), (149, 2100153643771859676), (150, 607822464732528024), (151, 521378783210082672), (152, 3905311406743852560), (153, 2427479559621574164), (154, 3195749842672951872), (155, 3327779780650453968), (156, 5079445271704130040), (157, 6776811476236715508), (158, 4439635587709526232), (159, 4514315952938395212), (160, 7254152227825114752), (161, 6950136693319313004), (162, 2661654716924689584), (163, 2495059112667753324), (164, 597713768073228240), (165, 5448438850918651056), (166, 2830080425803759800), (167, 4585514438360485224), (168, 2641788955120469112), (169, 1151158500436430052), (170, 402592609075178592), (171, 7234673504813331444), (172, 8196650698948118064), (173, 4485606389403353676), (174, 7947547777143243108), (175, 3677766697256972040), (176, 2747884181596726536), (177, 1060424406207782784), (178, 4113360726992776224), (179, 311463410081876640), (180, 394565099171566680), (181, 1274525118858204864), (182, 10329178671562189068), (183, 9711685319731355520), (184, 15460335902939392080), (185, 22107052294027667820), (186, 9951011310480706368), (187, 11449428297295205448), (188, 10733548851485810532), (189, 9419696285428791180), (190, 4323556989769282776), (191, 3380792497311201588), (193, 4485547519821345600), (196, 7811704642384455120), (197, 14814876843699882516), (198, 15420469406870476872), (199, 11395595639528485812), (200, 9351491043577467708), (201, 36802396263516171120), (202, 4009077026662649508), (203, 16268289906500921520), (204, 16973775546271635672), (205, 12928205239372794168), (206, 9051114378211242624), (207, 6060473246706953760), (209, 753977524521357864), (210, 4616246568188919888), (211, 3184288374103690392), (212, 6598827055982668752), (213, 10769453128926378432), (214, 26880499251253723320), (215, 39345332216877334368), (216, 39335653202334846084), (217, 28090404751939752600), (218, 4506616173111810408), (219, 4144993394320676016), (220, 2199956894449288380), (221, 1122974494792459344), (222, 4001104343604643884), (223, 589885894751188392), (224, 4848791298531737508), (225, 2628146751928686072), (226, 18510937194906596664), (227, 27745174880156745144), (228, 10837780355875602780), (229, 19603246446028631988), (230, 89847635035098636108), (231, 10245847012742346516), (232, 31464148214619685656), (233, 43244056235044681128), (234, 25839391906937784168), (235, 38825010674713436040), (236, 28283746269582323352), (237, 25587367794069447744), (245, 15793559720472126600), (246, 37391344373088638856), (247, 57120008310983748564), (248, 74627297574269439636), (249, 56810032652853031104), (250, 17598330216995542560), (252, 18120368493353290752), (254, 19234010225292569280), (255, 17043734481480832104), (256, 26040022543786589856), (257, 9007054018865490672), (258, 18349018192231784064), (259, 83604644934490693944), (260, 9491207506487343504), (261, 29031276583268881488), (262, 39551082275529901440), (263, 20004717760984504800), (264, 20510443829830493952), (265, 10487347998707157984), (267, 26634517816344247656), (268, 108437018535941635008), (269, 110452807712132679528), (270, 168479415294964653600), (275, 41561372369670660360), (278, 62004134526020119440), (279, 73263443103121308408), (280, 73783716550899369840), (281, 18604275576612655104), (282, 47221064552678525712), (284, 54712093057720157808), (285, 7788488618919145032), (286, 2690598951026794584), (287, 5430388739604782688), (288, 24621789280221936936), (289, 2784590541135749304), (290, 8494496079945882552), (291, 26187183201392343648), (292, 20723123884874384736), (293, 66457801145394982512), (294, 3008928689206811784), (300, 54659016091944087768), (301, 221369685921212040576), (302, 224190274315013000568), (303, 340080196016894963616), (305, 47078732965622325408), (308, 49255299746069223744), (309, 50927466071499099264), (310, 51217639977457257696), (312, 52178212457051839200), (314, 54253732491415314144), (325, 94135681326895255656), (326, 95462670710942648064), (327, 385680419724942085968), (333, 42144416960207909760), (334, 169960381964909673984), (335, 194215880370128056272), (336, 258566315467559819328), (338, 23828345556760090080), (339, 24400625592780944640), (340, 24550053018069242160), (342, 24941131149689984880), (344, 25694026302954668400), (353, 39860561884277965824), (359, 206104653937741998600), (360, 208183714058195982288), (361, 837857812647467843280), (365, 3914753669568000000), (366, 10557963115649663616), (367, 42431909661491099904), (368, 46571427093503499264), (369, 68082675852486316896), (370, 4112635407552000000), (372, 4171055692608000000), (374, 4258431463104000000), (388, 247769080432941718224), (393, 196402832554513203360), (394, 197688964847011216992), (395, 793235673474507591552), (423, 561732977663156947536), (427, 82620248557712780880), (428, 82896843436997551920), (429, 331879213131151996800), (458, 602224842279924793440), (461, 12360319889266298880), (462, 12365170242074173440), (463, 49427226352022077440), (493, 324004439467831590720), (528, 82884067205740950240), (563, 7796434227277500000)]
def coverageHData : Nat → List (Nat × Nat)
  | 1 => coverageH1Data
  | 2 => coverageH2Data
  | 3 => coverageH3Data
  | 4 => coverageH4Data
  | 5 => coverageH5Data
  | 6 => coverageH6Data
  | 7 => coverageH7Data
  | 8 => coverageH8Data
  | _ => []
def coverageHAt (j a : Nat) : Nat := ((coverageHData j).filter (fun e => e.1 == a)).foldl (fun s e => s + e.2) 0
def coverageHPack (base j : Nat) : Nat := (coverageHData j).foldr (fun e s => e.2 * base ^ e.1 + s) 0
end ClaudeWCT.Numerics.N600

-- Finite retained-occupancy certificate for the capped exponential bound.

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
def coverageProfiles : List (List Nat) := [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0], [2, 0, 1, 0, 0, 0], [2, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0]]
def coverageProfileUsed (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldr (fun e s => e.2 * e.1 + s) 0
def coverageProfileGroups (ms : List Nat) : Nat := ms.foldr (· + ·) 0
def coverageProfileMultiplicity (ms : List Nat) : Nat := ms.foldr (fun m s => fact m * s) 1
def coverageProfilePositions (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldr (fun e s => fact e.2 ^ e.1 * s) 1
def coverageProfileCount (n : Nat) (ms : List Nat) : Nat :=
  let s := n - coverageProfileUsed ms
  let g := s + coverageProfileGroups ms
  (fact 127 / (fact (127-g) * fact s * coverageProfileMultiplicity ms)) *
    (fact n / coverageProfilePositions ms)
def coverageProfilePack (base : Nat) (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldr (fun e s => coverageHPack base e.2 ^ e.1 * s) 1
def coverageOtherPack (base n : Nat) : Nat :=
  coverageProfiles.foldr (fun ms acc =>
    if coverageProfileUsed ms ≤ n then
      coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms) *
        base ^ (n - coverageProfileUsed ms) * coverageProfilePack base ms + acc
    else acc) 0
def coverageMarkedPack (base j : Nat) : Nat :=
  (coverageHData j).foldr (fun e s => e.1 * e.2 * base ^ e.1 + s) 0
def coverageRetainedPack (base r : Nat) : Nat :=
  (List.range 8).foldr (fun j acc =>
    if j + 1 ≤ r then
      (fact r / (fact (j+1) * fact (r-(j+1)))) * coverageMarkedPack base (j+1) *
        coverageOtherPack base (r-(j+1)) + acc
    else acc) 0
def coverageBinData : Array Nat := #[0, 0, 36, 56, 71, 82, 91, 99, 106, 111, 117, 122, 126, 130, 134, 137, 141, 144, 146, 149, 152, 154, 157, 159, 161, 163, 165, 167, 169, 171, 172, 174, 176, 177, 179, 180, 181, 183, 184, 186, 187, 188, 189, 190, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 206, 207, 208, 209, 210, 211, 211, 212, 213, 214, 214, 215, 216, 216, 217, 218, 219, 219, 220, 221, 221, 222, 222, 223, 224, 224, 225, 225, 226, 227, 227, 228, 228, 229, 229, 230, 230, 231, 232, 232, 233, 233, 234, 234, 235, 235, 236, 236, 236, 237, 237, 238, 238, 239, 239, 240, 240, 241, 241, 241, 242, 242, 243, 243, 244, 244, 244, 245, 245, 246, 246, 246, 247, 247, 247, 248, 248, 249, 249, 249, 250, 250, 250, 251, 251, 251, 252, 252, 253, 253, 253, 254, 254, 254, 255, 255, 255, 256, 256, 256, 256, 257, 257, 257, 258, 258, 258, 259, 259, 259, 260, 260, 260, 260, 261, 261, 261, 262, 262, 262, 262, 263, 263, 263, 264, 264, 264, 264, 265, 265, 265, 265, 266, 266, 266, 267, 267, 267, 267, 268, 268, 268, 268, 269, 269, 269, 269, 270, 270, 270, 270, 271, 271, 271, 271, 271, 272, 272, 272, 272, 273, 273, 273, 273, 274, 274, 274, 274, 274, 275, 275, 275, 275, 276, 276, 276, 276, 276, 277, 277, 277, 277, 277, 278, 278, 278, 278, 279, 279, 279, 279, 279, 280, 280, 280, 280, 280, 281, 281, 281, 281, 281, 281, 282, 282, 282, 282, 282, 283, 283, 283, 283, 283, 284, 284, 284, 284, 284, 285, 285, 285, 285, 285, 285, 286, 286, 286, 286, 286, 286, 287, 287, 287, 287, 287, 288, 288, 288, 288, 288, 288, 289, 289, 289, 289, 289, 289, 290, 290, 290, 290, 290, 290, 291, 291, 291, 291, 291, 291, 291, 292, 292, 292, 292, 292, 292, 293, 293, 293, 293, 293, 293, 293, 294, 294, 294, 294, 294, 294, 295, 295, 295, 295, 295, 295, 295, 296, 296, 296, 296, 296, 296, 296, 297, 297, 297, 297, 297, 297, 297, 298, 298, 298, 298, 298, 298, 298, 299, 299, 299, 299, 299, 299, 299, 300, 300, 300, 300, 300, 300, 300, 300, 301, 301, 301, 301, 301, 301, 301, 302, 302, 302, 302, 302, 302, 302, 302, 303, 303, 303, 303, 303, 303, 303, 303, 304, 304, 304, 304, 304, 304, 304, 304, 305, 305, 305, 305, 305, 305, 305, 305, 306, 306, 306, 306, 306, 306, 306, 306, 306, 307, 307, 307, 307, 307, 307, 307, 307, 308, 308, 308, 308, 308, 308, 308, 308, 308, 309, 309, 309, 309, 309, 309, 309, 309, 309, 310, 310, 310, 310, 310, 310, 310, 310, 310, 311, 311, 311, 311, 311, 311, 311, 311, 311, 312, 312, 312, 312, 312, 312, 312, 312, 312, 312, 313, 313, 313, 313, 313, 313, 313, 313, 313, 314, 314, 314, 314, 314, 314, 314, 314, 314, 314, 315, 315, 315, 315, 315, 315, 315, 315, 315, 315, 316, 316, 316, 316, 316, 316, 316, 316, 316, 316, 317, 317, 317, 317, 317, 317, 317, 317, 317, 317, 317, 318, 318, 318, 318, 318, 318, 318, 318, 318, 318, 318, 319, 319, 319, 319, 319, 319, 319, 319, 319, 319, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 321, 321, 321, 321, 321, 322, 322, 322, 322, 322, 322, 322, 322, 322, 322, 322, 323, 323, 323, 323, 323, 323, 323, 323, 323, 323, 323, 323, 324, 324, 324, 324, 324, 324, 324, 324, 324, 324, 324, 324, 325, 325, 325, 325, 325, 325, 325, 325, 325, 325, 325, 325, 326, 326, 326, 326, 326, 326, 326, 326, 326, 326, 326, 326, 326, 327, 327, 327, 327, 327, 327, 327, 327, 327, 327, 327, 327, 327, 328, 328, 328, 328, 328, 328, 328, 328, 328, 328, 328, 328, 329, 329, 329, 329, 329, 329, 329, 329, 329, 329, 329, 329, 329, 329, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 331, 331, 331, 331, 331, 331, 331, 331, 331, 331, 331, 331, 331, 331, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 333, 333, 333, 333, 333, 333, 333, 333, 333, 333, 333, 333, 333, 333, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 334, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 336, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 337, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 338, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 339, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 340, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 341, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 342, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 343, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 344, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 345, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 346, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 347, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 349, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 351, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 352, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 354, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 355, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 356, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 357, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 358, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 359, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 360, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 361, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 362, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 363, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 364, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 365, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 366, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 367, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 368, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 369, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 370, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 371, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 372, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 373, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 375, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 376, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 377, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 378, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 379, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 380, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 381, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 383, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 384, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 385, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 386, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 387, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 388, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 389, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 390, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 391, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 392, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 393, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 395, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 396, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 397, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 398, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 399, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 400, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 401, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 402, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 403, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 404, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 405, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 406, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 407, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 408, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 409, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 411, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 412, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 413, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 414, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 415, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 416, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 417, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 418, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 419, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 420, 421, 421]
def coverageBin (c : Nat) : Nat := coverageBinData[c]?.getD 0
def coverageRetainedCoeff (r c : Nat) : Nat :=
  coverageRetainedPack (2^512) r / (2^512)^c % (2^512)
def coverageBinnedPack (base r : Nat) : Nat :=
  let p := coverageRetainedPack (2^512) r
  (List.range 4096).foldr (fun c acc =>
    let n := (p >>> (512*c)) % (2^512)
    if n = 0 then acc else n * base ^ coverageBin c + acc) 0
def coverageProductPack (r : Nat) : Nat := coverageBinnedPack (2^4608) r ^ 9
def winsorScale : Nat := 2^96
def winsorCeil (n d : Nat) : Nat := (n + d - 1) / d
def winsorExpDen : Nat := fact 16 * 16 * winsorScale ^ 16
def winsorExpNum (u : Nat) : Nat :=
  16 * (List.range 16).foldr (fun i acc =>
    (fact 16 / fact i) * u ^ i * winsorScale ^ (16-i) + acc) 0 + 17 * u ^ 16
def winsorMGFPayData : List Nat := [757479905971184434798983148466, 757479905972493053934845819245, 757479905972172314038424172361, 757479905975474049067750770329, 757479905973932622924328542283, 757479905972723661260582837016, 757479905971834718882171915583, 757479905971689466925236606608, 757479905977812837114061801264, 757479905975858273093134721459, 757479905975995147412986895816, 757479905975592576212774430558, 757479905975197898568860373855, 757479905975455857957763139154, 757479905975582308685261233846, 757479905972359057228704968819, 757479905976977592723050163091, 757479905974951919396949789978, 757479905976120127926395178697, 757479905975776537310230505751, 757479905972632570081371935830, 757479905974724145089000314617, 757479905972349808357443177578, 757479905971609150806264612138, 757479905975862227106293608948, 757479905971997643400692728064, 757479905974988807459910732358, 757479905975379809399038722753, 757479905974325637936196435086, 757479905971600952151574154918, 757479905971785177150192436381, 757479905973771916127149777060, 757479905971558526269763486177, 757479905972686921295310201941, 757479905971495554270029125969, 757479905974165284733983423818, 757479905973756318830011679292, 757479905973275182450665950559, 757479905974847524167098682666, 757479905973306012969455069396, 757479905971719163205787686574, 757479905974312055375478478315, 757479905973440495190259842963, 757479905973369289439534850151, 757479905971763666135531079135, 757479905972105870791441409580, 757479905971770376362778507908, 757479905974204356952090285469, 757479905972785502619339513529, 757479905972532587556778964170, 757479905972470598710081293246, 757479905973807617190210567436, 757479905973926781221623272739, 757479905973517885884118262068, 757479905971341691374457508402, 757479905972689180560089929838, 757479905973074492158753522336, 757479905973614144179181931701, 757479905972767631750887957458, 757479905973026980206117576024, 757479905971755665546093864371, 757479905972353931601444770825, 757479905973087100740100674070, 757479905971649514886504353462, 757479905973152873131619330556, 757479905972554109467632142334, 757479905972825043615421929819, 757479905971275585315255783937, 757479905971666205381224981925, 757479905973155496840793730508, 757479905971695407708604909988, 757479905971409115946267158647, 757479905971649697775884802750, 757479905971453144513967442901, 757479905972840581638611100121, 757479905972802797711875224873, 757479905972432364416650816554, 757479905972831851947184654964, 757479905972938667030343600350, 757479905971682023072268439313, 757479905971339800015461322766, 757479905972681852858980568950, 757479905972023984329375659632, 757479905972023984681643736274, 757479905971897520436004123934, 757479905971494569855349503254, 757479905971373016398966737477, 757479905971521979807494192933, 757479905972456650171147620108, 757479905971798028955769745225, 757479905971545361222785006249, 757479905971738027971406667850, 757479905971711044311743680930, 757479905971816864665297471191, 757479905972102163918384497215, 757479905971313905606886731649, 757479905971588126376967855077, 757479905971319283396302803277, 757479905972109999886513071384, 757479905971240823525305417408, 757479905971839620996962750503, 757479905971410619139999973926, 757479905971720528478845251778, 757479905971633719807435119902, 757479905971974148556500940821, 757479905971202344936862280773, 757479905971713609512119016119, 757479905971432916107084171098, 757479905971314978041472776145, 757479905971700399034704795750, 757479905971379215966202879382, 757479905971879329560141925947, 757479905971806692134788406111, 757479905971308196344943470285, 757479905971378014422670952816, 757479905971258230285513249457, 757479905971744751863160255425, 757479905971251323648665081213, 757479905971686702798908282360, 757479905971433760339139072659, 757479905971883231180697004200, 757479905971321014415868773244, 757479905971589163435567871406, 757479905971603769238287829960, 757479905971546495424222729170, 757479905971434193081618767915, 757479905971530532395156065049, 757479905971490054880748224021, 757479905971529740402611989571, 757479905971270364395653651340, 757479905971435654479217556498, 757479905971572773119896334938, 757479905971426124071565522456, 757479905971641786751931895115, 757479905971277652986028363431, 757479905971496457259259872879, 757479905971349686194869832312, 757479905971360756004793031341, 757479905971632050767416814520, 757479905971270326880829000370, 757479905971249467245955276975, 757479905971218790821564489454, 757479905971248867969715844268, 757479905971612533359320356913, 757479905971458357862541043437, 757479905971354440962545498498, 757479905971391489640961193991, 757479905971400571149849901889, 757479905971275941436386214078, 757479905971415585303344069563, 757479905971561047636556708983, 757479905971602992763992673179, 757479905971191780682251837083, 757479905971498176436172532441, 757479905971268935458274866243, 757479905971439435001523514144, 757479905971500220124987946691, 757479905971276752428313874430, 757479905971452023961699815590, 757479905971430546384419315941, 757479905971430548002821716127, 757479905971203453533403089124, 757479905971392364645747891773, 757479905971372522935839828937, 757479905971307676885789075463, 757479905971294963417369124958, 757479905971189004779394983933, 757479905971396772247368083084, 757479905971270964518795319592, 757479905971335574570241337087, 757479905971364368039190204765, 757479905971358724660073037928, 757479905971430677779424792788, 757479905971246189958061918349, 757479905971437704115937491327, 757479905971442921763114410117, 757479905971330433476551606180, 757479905971225163876665922088, 757479905971244824799915207520, 757479905971278555168015266563, 757479905971202976597204701995, 757479905971328021105501458728, 757479905971287160190741313030, 757479905971189232985816097828, 757479905971267788869917024225, 757479905971306298035372909945, 757479905971335663006389138856, 757479905971356227577468404822, 757479905971384452485450211285, 757479905971333070601224842362, 757479905971259445296924041397, 757479905971278444219938438402, 757479905971270997884443368461, 757479905971216226102445466869, 757479905971219809333970473500, 757479905971311068960221497156, 757479905971228487293593670765, 757479905971208249247257258648, 757479905971307475298275800324, 757479905971206959157754989621, 757479905971337301295511849058, 757479905971187705440610275456, 757479905971206042430518904494, 757479905971274945774536534622, 757479905971248517589486238568, 757479905971283073238337608107, 757479905971283077262675287212, 757479905971227731336386250112, 757479905971282000259692926145, 757479905971274024422060243163, 757479905971258381506971940805, 757479905971281396643049489840, 757479905971238788780878509547, 757479905971199474008672022111, 757479905971288621959824007854, 757479905971288626769280061779, 757479905971237685801924784319, 757479905971253583012055552984, 757479905971286975104066713566, 757479905971280433841706437949, 757479905971263324202008578850, 757479905971280108980713677284, 757479905971255438972213337082, 757479905971271572406639064059, 757479905971259719478368500367, 757479905971277164570503523977, 757479905971258173568502356616, 757479905971233967828308630557, 757479905971206585090863161786, 757479905971220912461146631399, 757479905971203368659153581759, 757479905971217140182986632967, 757479905971234015693710383751, 757479905971214176943593027657, 757479905971257961051249659899, 757479905971213459888725449534, 757479905971229051320105881244, 757479905971210724470898040662, 757479905971257166925873706734, 757479905971217524392271576871, 757479905971236248822310390942, 757479905971250371907959357658, 757479905971225471227593528059, 757479905971188848881029806997, 757479905971239400898922515994, 757479905971214633396348358182, 757479905971199300973119818423, 757479905971229391035020772086, 757479905971235544274656150288, 757479905971194593739455259177, 757479905971207595272912505689, 757479905971190236213238138799, 757479905971200463202803350778, 757479905971196021565635229949, 757479905971199305391785131528, 757479905971185409346625473589, 757479905971196956627272170242, 757479905971222672775562535823, 757479905971186394492378327156, 757479905971225937090338935942, 757479905971232731112192959452, 757479905971187147796809706010, 757479905971200197859720190914, 757479905971185602050605763850, 757479905971203517010869522928, 757479905971191244085051625255, 757479905971211045456430918977, 757479905971217806807658800813, 757479905971220301384476920327, 757479905971223558323964142743, 757479905971210060419195376985, 757479905971206957996949459545, 757479905971194749335389821966, 757479905971195513493501055101, 757479905971186717306493275485, 757479905971207610379728740720, 757479905971211861220385182302, 757479905971205650071570104806, 757479905971196169439605469274, 757479905971195521437877252619, 757479905971211187859746380867, 757479905971211844887075050867, 757479905971199328571820725494, 757479905971204262527823045329, 757479905971214521943119615411, 757479905971205682565698326796, 757479905971197596265609135230, 757479905971198751561414473222, 757479905971211015222354705743, 757479905971206671249447760481, 757479905971200273672145628117, 757479905971187709422768119895, 757479905971205726082122113570, 757479905971206252669209938687, 757479905971186509014512392532, 757479905971205427048076289992, 757479905971193101563059010714, 757479905971204301888162460157, 757479905971189717713309334818, 757479905971205856026334508486, 757479905971205004304381972166, 757479905971187392457183984902, 757479905971203024733427872412, 757479905971205533183153801738, 757479905971190967227051711140, 757479905971196559963458602960, 757479905971190744419653702366, 757479905971190392151202640739, 757479905971199036354927199550, 757479905971192091013510795257, 757479905971198962062726492605, 757479905971189465549446504902, 757479905971192266342702949064, 757479905971194335097301624855, 757479905971187052945615052140, 757479905971196542914435590125, 757479905971191144473631389999, 757479905971198075047633745778, 757479905971187358844663429638, 757479905971190107444958410681, 757479905971189260003997601630, 757479905971199432202865175550, 757479905971191808642948062805, 757479905971195466989854754782, 757479905971198509592003361840, 757479905971195075015013155450, 757479905971196691663536627810, 757479905971191080106041273289, 757479905971194401680968368817, 757479905971195188945366896882, 757479905971189906302858493335, 757479905971190191636185449533, 757479905971187911977278134938, 757479905971187048624818432381, 757479905971187994596530952104, 757479905971197042377284506286, 757479905971188060460923441707, 757479905971191066852172444216, 757479905971194429947004671268, 757479905971196918453617140287, 757479905971191609887206851818, 757479905971191473359741768824, 757479905971191914860006487370, 757479905971189728301304075238, 757479905971196399649874115371, 757479905971194302804248724180, 757479905971196484785848817592, 757479905971192225272023139593, 757479905971192631477491411041, 757479905971192367214977457888, 757479905971192762953577529623, 757479905971193313524323086892, 757479905971189155179959436661, 757479905971189997253399704323, 757479905971189169000839721890, 757479905971190427214021472033, 757479905971193545742952936529, 757479905971194193489590271352, 757479905971193996846516685595, 757479905971193807292904453667, 757479905971190949952723634193, 757479905971194707889685583636, 757479905971191196952773915302, 757479905971190782988492821421, 757479905971194828697401798751, 757479905971193226624670510308, 757479905971193797312274408160, 757479905971191915594103985631, 757479905971191672679201001494, 757479905971194236162220164328, 757479905971191377442477595352, 757479905971190730121335936088, 757479905971194212348541855747, 757479905971191220666604555821, 757479905971192346328052805024, 757479905971194348694582117329, 757479905971191347784355724664, 757479905971193950039422265573, 757479905971192947684573708566, 757479905971194907494727679493, 757479905971191523587119572780, 757479905971193681815265162797, 757479905971191217884156439817, 757479905971192284761363287283, 757479905971194416962759541931, 757479905971193822650202721422, 757479905971195003757109859973, 757479905971195305449400228185, 757479905971194761982815504938, 757479905971193406612301124431, 757479905971193781974426670322, 757479905971192708344940397142, 757479905971196132900369132711, 757479905971196087451638504094, 757479905971195026192980417253, 757479905971196199172997508742, 757479905971195716819606640046, 757479905971196600602916069612, 757479905971194953392730014854, 757479905971196805356649051120, 757479905971195781519205903566, 757479905971196150970794918087, 757479905971196695408274340699, 757479905971195467540492777793, 757479905971196789694636057059, 757479905971196228733505435495, 757479905971195256700834964752, 757479905971196421272835763660, 757479905971195658807072540505, 757479905971197302046337671191, 757479905971197182857164078539, 757479905971197659627206971541, 757479905971196655765124518523, 757479905971197366609735611155, 757479905971197430467300650976, 757479905971198312948604089482, 757479905971197776230766666240, 757479905971199552831484776969, 757479905971199608663773430738, 757479905971199881895420550822, 757479905971198652412273083576, 757479905971199735929658148334, 757479905971201005354850524639, 757479905971200532898135164409, 757479905971200533308564387084, 757479905971201505554542986134, 757479905971201638436121217888, 757479905971201284347352281747, 757479905971202689363252514234, 757479905971202272066356717997, 757479905971201809266423670247, 757479905971203303197081547988, 757479905971203753072096736115, 757479905971202884703606714583, 757479905971204395448950324318, 757479905971204891683344817270, 757479905971204056876138395656, 757479905971205698865976322829, 757479905971205840056306377782, 757479905971205518583633670544, 757479905971206042437215018344, 757479905971206868250616731886, 757479905971206745419241407206, 757479905971207598482620443191, 757479905971207920036266455802, 757479905971208874176199769485, 757479905971208220070196465681, 757479905971208862937853249091, 757479905971209582279116082135, 757479905971210765801287217986, 757479905971210460502361401291, 757479905971211681404252800348, 757479905971211903806185256837, 757479905971212015417755822236, 757479905971213019221351027148, 757479905971213046652985260337, 757479905971213834967112480494, 757479905971214120989204562318, 757479905971214789291369498793, 757479905971215825681969282582, 757479905971215887238187783180, 757479905971217094072296135997, 757479905971217113276442916668, 757479905971218566520472381988, 757479905971218618650692093281, 757479905971219314791870953150, 757479905971219975016323531848, 757479905971221003306058927864, 757479905971221503730438954563, 757479905971222439967880202723, 757479905971222690349035607874, 757479905971223782124191239418, 757479905971224853685447182724, 757479905971225592652922718472, 757479905971225872974044362592, 757479905971226810915957785010, 757479905971228099458066697207, 757479905971228407407308973945, 757479905971229686995628438991, 757479905971230152633052965977, 757479905971231154008031401151, 757479905971232330303695197769, 757479905971233472712952095369, 757479905971234009939438160155, 757479905971235103023227400628, 757479905971235966327439058885, 757479905971237172609015690132, 757479905971238179718591938554, 757479905971239335923025262480, 757479905971240522287125327994, 757479905971241759247449529110, 757479905971242746327289082975, 757479905971243759084966722414, 757479905971244932369493293200, 757479905971246044761530845654, 757479905971247284669225681733, 757479905971248874801702789233, 757479905971249835793808320650, 757479905971251333162141700850, 757479905971252656758598758847, 757479905971254124213180674392, 757479905971255518351940864320, 757479905971256779329832026893, 757479905971257992790907457902, 757479905971259687556955031520, 757479905971261006006332134854, 757479905971262751493672815526, 757479905971264326846385922813, 757479905971265804687110459218, 757479905971267421543385900432, 757479905971269112165508124679, 757479905971270895758908166357, 757479905971272421235370186076, 757479905971274366372555619807, 757479905971275975483983747447, 757479905971277785568989238072, 757479905971279748308497010376, 757479905971281531493410102225, 757479905971283583368254339179, 757479905971285539878948617890, 757479905971287570187763033359, 757479905971289475173361454200, 757479905971291732630091899771, 757479905971293716210634197880, 757479905971296042046777657346, 757479905971298169326763630850, 757479905971300403142686793070, 757479905971302737097766383760, 757479905971305174775335116011, 757479905971307517114697147134, 757479905971309969101311673655, 757479905971312511219568986194, 757479905971315151726125806196, 757479905971317789686807712425, 757479905971320394090225526968, 757479905971323224348026062168, 757479905971325881319438012854, 757479905971328712503366496727, 757479905971331671061174909154, 757479905971334446371297744574, 757479905971337624544704743204, 757479905971340547408686847888, 757479905971343679746312422821, 757479905971346981339553844009, 757479905971350074948700539502, 757479905971353387423951836743, 757479905971356786322191629366, 757479905971360282066255504098, 757479905971363819913301589032, 757479905971367357918232700219, 757479905971371074176306761812, 757479905971374701021558235854, 757479905971378592596204510046, 757479905971382426856290037423, 757479905971386339656516222944, 757479905971390450693194196071, 757479905971394588647315530290, 757479905971398754513167244060, 757479905971403071366423623340, 757479905971407410917653149761, 757479905971411894554847487467, 757479905971416346941950239850, 757479905971421095421669016619, 757479905971425759218665846070, 757479905971430646076452824625, 757479905971435505925778600143, 757479905971440544634600072077, 757479905971445627942398349300, 757479905971450831808689871278, 757479905971456195964484804531, 757479905971461645063908119312, 757479905971467231257260283082, 757479905971472847101494155169, 757479905971478555106697721788, 757479905971484439479473738916, 757479905971490486902962282616, 757479905971496619988580925179, 757479905971502815167780305204, 757479905971509198568816400238, 757479905971515745733776604533, 757479905971522296580270956628, 757479905971529078874859432336, 757479905971535936479447587261, 757479905971543031178984520207, 757479905971550143225285217201, 757479905971557480599786952400, 757479905971564954662627310475, 757479905971572586621148828330, 757479905971580343987097196938, 757479905971588207887604449927, 757479905971596287439625976421, 757479905971604547724093913098, 757479905971612947947076526470, 757479905971621492366775378215, 757479905971630245062248304967, 757479905971639174896652974180, 757479905971648281523446613846, 757479905971657509778927675587, 757479905971667013340258748547, 757479905971676641743918155151, 757479905971686477449955201000, 757479905971696545263800938114, 757479905971706794501576660256, 757479905971717236454328743835, 757479905971727897013806588094, 757479905971738730853894520494, 757479905971749826801378793932, 757479905971761154308531389690, 757479905971772689840682153116, 757479905971784438623788375894, 757479905971796429621508221348, 757479905971808674698918076353, 757479905971821140798561318785, 757479905971833908683369783224, 757479905971846857115325429314, 757479905971860112412696747764, 757479905971873634225625221310, 757479905971887414603449837634, 757479905971901498191779929145, 757479905971915828428560097313, 757479905971930461210663739733, 757479905971945358261031153761, 757479905971960569086681926367, 757479905971976123212054074176, 757479905971991941254106978404, 757479905972008078364050977216, 757479905972024564923618015427, 757479905972041350919352921645, 757479905972058507745926244794, 757479905972075992027288861571, 757479905972093798469802023601, 757479905972111987609450724337, 757479905972130563115413512805, 757479905972149468336549499844, 757479905972168772928652113740, 757479905972188455370689690912, 757479905972208548593652849038, 757479905972229029854253719608, 757479905972249915324352367430, 757479905972271206479324469023, 757479905972292955011843039783, 757479905972315134923053180046, 757479905972337738454923136285, 757479905972360806768068064474, 757479905972384329590031065990, 757479905972408332034832057016, 757479905972432809700022642908, 757479905972457781923527434100, 757479905972483245363836218563, 757479905972509217321963461356, 757479905972535707588876838819, 757479905972562724502110094378, 757479905972590297746709801630, 757479905972618416506003025725, 757479905972647101141422767766, 757479905972676339460310115067, 757479905972706184450631810668, 757479905972736615618066772515, 757479905972767658484213915167, 757479905972799327259384183428, 757479905972831617632431432994, 757479905972864572036856984437, 757479905972898163469335305960, 757479905972932451036278123579, 757479905972967405645677147881, 757479905973003057973194327412, 757479905973039431745350523851, 757479905973076540904734909294, 757479905973114378074329738922, 757479905973152984244367258638, 757479905973192355609923115573, 757479905973232502498810771500, 757479905973273462757789363071, 757479905973315245528676100510, 757479905973357862269419167203, 757479905973401335243975211928, 757479905973445668022037429602, 757479905973490893938444059950, 757479905973537028509979074054, 757479905973584080246703718806, 757479905973632068757480723487, 757479905973681025329445104920, 757479905973730956098819058545, 757479905973781885073521705287, 757479905973833828307157500608, 757479905973886820063849009656, 757479905973940864146285721860, 757479905973995998318781943565, 757479905974052222428805094103, 757479905974109581600407975628, 757479905974168082190854576017, 757479905974227759738821142983, 757479905974288623751103459652, 757479905974350712458945743163, 757479905974414032340499921305, 757479905974478621653950644992, 757479905974544512341615465184, 757479905974611710596169295951, 757479905974680254931800292921, 757479905974750171987387852537, 757479905974821488632708121340, 757479905974894228099439822148, 757479905974968421192484494418, 757479905975044105311605491926, 757479905975121293669339477939, 757479905975200035370527428526, 757479905975280342251454671091, 757479905975362264624321629917, 757479905975445820521368244696, 757479905975531045297329343501, 757479905975617982917651028609, 757479905975706648444591391639, 757479905975797098045873539003, 757479905975889345840152313324, 757479905975983444961944907284, 757479905976079424138960410840, 757479905976177324914354641769, 757479905976277185716219049152, 757479905976379038151891667236, 757479905976482931893000958051, 757479905976588901407145180261, 757479905976696992956037420667, 757479905976807243775566320723, 757479905976919699825765438577, 757479905977034400544288288980, 757479905977151400409492016228, 757479905977270742346986830121, 757479905977392465701900679470, 757479905977516628575546686507, 757479905977643272735966335096, 757479905977772446603011371949, 757479905977904210959781984806, 757479905978038605540596021695, 757479905978175689541514461992, 757479905978315511299708786804, 757479905978458132492478047966, 757479905978603607140050682801, 757479905978751993169808496652, 757479905978903342316617571922, 757479905979057720734217328609, 757479905979215188515009180333, 757479905979375801115495526255, 757479905979539628770376765061, 757479905979706732423511394348, 757479905979877179360166819282, 757479905980051032715584316503, 757479905980228367620449073690, 757479905980409244398846669373, 757479905980593740511501954492, 757479905980781927215317644533, 757479905980973877631690891172, 757479905981169667151339250871, 757479905981369369990065863988, 757479905981573068184586937407, 757479905981780842934842812221, 757479905981992770687816424293, 757479905982208936119441663508, 757479905982429426869575911760, 757479905982654325438222152573, 757479905982883723416858375948, 757479905983117709302594137594, 757479905983356376141681171891, 757479905983599815286679840175, 757479905983848122196985800295, 757479905984101396261258622097, 757479905984359735928078618517, 757479905984623241079218637385, 757479905984892016791900625286, 757479905985166168948871860665, 757479905985445804049679371327, 757479905985731031957506359541, 757479905986021962413147646402, 757479905986318713069485139589, 757479905986621399788302546997, 757479905986930139609665006304, 757479905987245052693414909616, 757479905987566264929067402723, 757479905987893901173726865861, 757479905988228091995382813100, 757479905988568964477354573305, 757479905988916654273320614768, 757479905989271299052018891799, 757479905989633037216072817517, 757479905990002009064257804773, 757479905990378360872304625207, 757479905990762238374068856905, 757479905991153795789082214566, 757479905991553182424540797457, 757479905991960556901152381749, 757479905992376079271032826561, 757479905992799913085446341273, 757479905993232221886680706843, 757479905993673178493477758039, 757479905994122952786369066420, 757479905994581723753945829054, 757479905995049669730872796345, 757479905995526974335963039446, 757479905996013825388819484255, 757479905996510413225652348932, 757479905997016931788450749875, 757479905997533581973597235613, 757479905998060565845300021824, 757479905998598088240172265906, 757479905999146360637988974544, 757479905999705599853178659495, 757479906000276023309935099095, 757479906000857854821863978373, 757479906001451323569803957314, 757479906002056661062034398170, 757479906002674105703859893904, 757479906003303898929693287541, 757479906003946288613623090868, 757479906004601526060586651144, 757479906005269867870185803372, 757479906005951576002081495131, 757479906006646918711815105219, 757479906007356169019647807828, 757479906008079603918858587467, 757479906008817507124957039471, 757479906009570168721283199745, 757479906010337883057639026173, 757479906011120951928662014306, 757479906011919682425213150929, 757479906012734387374934356722, 757479906013565386549446406360, 757479906014413005879514984387, 757479906015277577114137015952, 757479906016159440272854866476, 757479906017058940457725780322, 757479906017976430658177079784, 757479906018912270783047533437, 757479906019866827288115064185, 757479906020840475377494876235, 757479906021833596067129387300, 757479906022846579446955597757, 757479906023879822611767493505, 757479906024933729941745410775, 757479906026008716050462397055, 757479906027105201689426024523, 757479906028223617144796127603, 757479906029364401076553091398, 757479906030528000297517067115, 757479906031714871892335408876, 757479906032925480628819318321, 757479906034160301331041830778, 757479906035419818810000207305, 757479906036704526750278779650, 757479906038014928373525110568, 757479906039351538329199858019, 757479906040714880399992633037, 757479906042105489380198191092, 757479906043523910716208947273, 757479906044970700189294845977, 757479906046446425802609446674, 757479906047951665609313668054, 757479906049487010007971611972, 757479906051053061828029916550, 757479906052650434226685151377, 757479906054279754506797155977, 757479906055941660773543880371, 757479906057636805521692310850, 757479906059365852915342805861, 757479906061129481292461353863, 757479906062928382346524385398, 757479906064763261363702599725, 757479906066634838088696422465, 757479906068543845956346420863, 757479906070491034236759301471, 757479906072477166483439469939, 757479906074503021171319684303, 757479906076569392766490382980, 757479906078677092049342654993, 757479906080826945468965064852, 757479906083019795705341363986, 757479906085256502795727143787, 757479906087537944209851461640, 757479906089865014511440022414, 757479906092238626135967965775, 757479906094659710200968139147, 757479906097129215724381202892, 757479906099648111482046615555, 757479906102217385010529961217, 757479906104838043995057662881, 757479906107511116302966693029, 757479906110237650009027092511, 757479906113018714319450428901, 757479906115855399982598498384, 757479906118748819366717878878, 757479906121700107107274674620, 757479906124710420577004589912, 757479906127780940414132264878, 757479906130912870645968051015, 757479906134107439473334888889, 757479906137365899619795911383, 757479906140689528962921788431, 757479906144079630846828998654, 757479906147537534909070534028, 757479906151064596882232139098, 757479906154662200272379480513, 757479906158331755578629436851, 757479906162074702127392118801, 757479906165892507515364202744, 757479906169786669102616536862, 757479906173758713778958694850, 757479906177810199455660485927, 757479906181942714814576970301, 757479906186157880464641296290, 757479906190457349396779803257, 757479906194842807826151166551, 757479906199315975391001885668, 757479906203878606178797085486, 757479906208532489742258442332, 757479906213279450893051360584, 757479906218121351300411426528, 757479906223060089694608868885, 757479906228097602782498323707, 757479906233235866250283780477, 757479906238476894970811422306, 757479906243822744277691114282, 757479906249275510469411965640, 757479906254837332106127626769, 757479906260510390059389720946, 757479906266296909237056607797, 757479906272199158805958625811, 757479906278219453373468563663, 757479906284360153824321897821, 757479906290623668224042359782, 757479906297012453020527767762, 757479906303529013392221013663, 757479906310175905100383173174, 757479906316955734519575002011, 757479906323871160636267255082, 757479906330924895181564019131, 757479906338119704501619869197, 757479906345458409957009624177, 757479906352943889541701758188, 757479906360579078701402093333, 757479906368366971602335912723, 757479906376310622429088964162, 757479906384413146282971514465, 757479906392677720571647957995, 757479906401107586364230610606, 757479906409706049423696658122, 757479906418476481814862446753, 757479906427422322854234853512, 757479906436547080679869229449, 757479906445854333623405059520, 757479906455347731703193603816, 757479906465030997724785743677, 757479906474907929028606089543, 757479906484982399006005230818, 757479906495258358344790028562, 757479906505739836918974761232, 757479906516430944987177926214, 757479906527335875274058556908, 757479906538458904157370525887, 757479906549804393658665080736, 757479906561376792899589479951, 757479906573180640124078095259, 757479906585220564319280173900, 757479906597501286972224959019, 757479906610027624088084046827, 757479906622804487947577649074, 757479906635836889079432711227, 757479906649129938269581788146, 757479906662688848402555125328, 757479906676518936751373344707, 757479906690625626853857221933, 757479906705014450778273987739, 757479906719691051170530503660, 757479906734661183583409642443, 757479906749930718651408048709, 757479906765505644412665059031, 757479906781392068677972436420, 757479906797596221435636402381, 757479906814124457249644878260, 757479906830983257787167292391, 757479906848179234310584874213, 757479906865719130397475626276, 757479906883609824380089471417, 757479906901858332257757032409, 757479906920471810305103853574, 757479906939457557897338635249, 757479906958823020450402895053, 757479906978575792245797550659, 757479906998723619480786272741, 757479907019274403244672082103, 757479907040236202698308726627, 757479907061617238160051398841, 757479907083425894316204684908, 757479907105670723585681015669, 757479907128360449477477349042, 757479907151503969852751309685, 757479907175110360642242728752, 757479907199188879262445265053, 757479907223748968250697552725, 757479907248800259010629312832, 757479907274352575594707081910, 757479907300415938507674789000, 757479907327000568678100667047, 757479907354116891453402833361, 757479907381775540699280875746, 757479907409987362924663072171, 757479907438763421583267657609, 757479907468115001439787572397, 757479907498053612881972520903, 757479907528590996540862295284, 757479907559739127887566292811, 757479907591510221868012916140, 757479907623916737723082666737, 757479907656971383900362358960, 757479907690687123002144537261, 757479907725077176894657037347, 757479907760155031863690381794, 757479907795934443933598053628, 757479907832429444243725791604, 757479907869654344561922595345, 757479907907623742883994487127, 757479907946352529195059283658, 757479907985855891222487654758, 757479908026149320485106912464, 757479908067248618338170205230, 757479908109169902161072278927, 757479908151929611664000301426, 757479908195544515348934146082, 757479908240031717121764360973, 757479908285408662929743219080, 757479908331693147655171034859, 757479908378903322086799173357, 757479908427057700004059998672, 757479908476175165491809413274, 757479908526274980279391998061, 757479908577376791374270227572, 757479908629500638697577863157, 757479908682666962971192798991, 757479908736896613739201898740, 757479908792210857525520501590, 757479908848631386191269155893, 757479908906180325434368559782, 757479908964880243476186254628, 757479909024754159877679453781, 757479909085825554613049407464, 757479909148118377256208490471, 757479909211657056360031328505, 757479909276466509044850283614, 757479909342572150792523706551, 757479909409999905387732811065, 757479909478776215085164507919, 757479909548928050977516391206, 757479909620482923600114553254, 757479909693468893686634730269, 757479909767914583179581893639, 757479909843849186474048925823, 757479909921302481846674746506, 757479910000304843140921428806, 757479910080887251666161027914, 757479910163081308374466633140, 757479910246919246229254997659, 757479910332433942860591623655, 757479910419658933431234150117, 757479910508628423828036635275, 757479910599377304047274529317, 757479910691941161889282266443, 757479910786356296896687521396, 757479910882659734626338377757, 757479910980889241124660843023, 757479911081083337770361242672, 757479911183281316365766310410, 757479911287523254556139460304, 757479911393850031528990015984, 757479911502303344061450461511, 757479911612925722865047042304, 757479911725760549265207124244, 757479911840852072221275425957, 757479911958245425655053456381, 757479912077986646187249840831, 757479912200122691150519970634, 757479912324701457046260827345, 757479912451771798282948793146, 757479912581383546377953626977, 757479912713587529462757091730, 757479912848435592242494327765, 757479912985980616308702671014, 757479913126276540894396655505, 757479913269378384003663495704, 757479913415342264011285743790, 757479913564225421660452240723, 757479913716086242503225514156, 757479913870984279804928766678, 757479914028980277892746533325, 757479914190136195989435336679, 757479914354515232496618915634, 757479914522181849781342438347, 757479914693201799464683509788, 757479914867642148191479944800, 757479915045571303951829052737, 757479915227059042880582444508, 757479915412176536650669607812, 757479915600996380356040263684, 757479915793592621001405188496, 757479915990040786527642672876, 757479916190417915435896822265, 757479916394802586992987747911, 757479916603274952055066020067, 757479916815916764499037412858, 757479917032811413273679910504, 757479917254043955109393950485, 757479917479701147872996615672, 757479917709871484581404575427, 757479917944645228120019916790, 757479918184114446628998465512, 757479918428373049614272565319, 757479918677516824764611459878, 757479918931643475533619644900, 757479919190852659432514698598, 757479919455246027133202825172, 757479919724927262313873086924, 757479920000002122328465960748, 757479920280578479683291822841, 757479920566766364326212612749, 757479920858678006811661549395, 757479921156427882299179275880, 757479921460132755460002170542, 757479921769911726248757703033, 757479922085886276628613610049, 757479922408180318198276230564, 757479922736920240786368225202, 757479923072234962021418962249, 757479923414255977886323826352, 757479923763117414279857204013, 757479924118956079622038181667, 757479924481911518501283814398, 757479924852126066397115973210, 757479925229744905498487582068, 757479925614916121641344296454, 757479926007790762376043958153, 757479926408522896205294104699, 757479926817269673002239874408, 757479927234191385637732485333, 757479927659451532840830630146, 757479928093216883316215854373, 757479928535657541142464195360, 757479928986947012480191559904, 757479929447262273614833761353, 757479929916783840355651262378, 757479930395695838830452929814, 757479930884186077691917833824, 757479931382446121762753038326, 757479931890671367165107552750, 757479932409061117943673547095, 757479932937818664225469520683, 757479933477151361938920796830, 757479934027270714135492669488, 757479934588392453924052905680, 757479935160736629079845489879, 757479935744527688332395983461, 757479936339994569388099008466, 757479936947370788707307802145, 757479937566894533083285106156, 757479938198808753041646682026, 757479938843361258123810140808, 757479939500804814060058223403, 757479940171397241899538442604, 757479940855401519111973563541, 757479941553085882716179390376, 757479942264723934475340464731, 757479942990594748188205929968, 757479943730982979130388579189, 757479944486178975685428696806, 757479945256478893206261707879, 757479946042184810153538081951, 757479946843604846558474712974, 757479947661053284857120846968, 757479948494850693132551748417, 757479949345324050835248660357, 757479950212806877002806645713, 757479951097639361058831446257, 757479952000168496215363110901, 757479952920748215552370634176, 757479953859739530812785878014, 757479954817510673976908538439, 757479955794437241668486944836, 757479956790902342444263405380, 757479957807296747035589638802, 757479958844019041592779956779, 757479959901475783989793712623, 757479960980081663262944929562, 757479962080259662230763145511, 757479963202441223372966456593, 757479964347066418021391693951, 757479965514584118938947189553, 757479966705452176346598409976, 757479967920137597474199710641, 757479969159116729699644416136, 757479970422875447353556279078, 757479971711909342256136839993, 757479973026723918070612667357, 757479974367834788535580488168, 757479975735767879671882914356, 757479977131059636024078366744, 757479978554257231033411283059, 757479980005918781616198853463, 757479981486613567031753185965, 757479982996922252131437185275, 757479984537437115069499334929, 757479986108762279569925391583, 757479987711513951837788847842, 757479989346320662209179917155, 757479991013823511634249917003, 757479992714676423090226042905, 757479994449546398021179683387, 757479996219113777908755771628, 757479998024072511072324852033, 757479999865130424806968007662, 757480001743009502962573172136, 757480003658446169076402369644, 757480005612191575165401407376, 757480007605011896298151210823, 757480009637688631054865199878, 757480011711018907999471638470, 757480013825815798277935942550, 757480015982908634472199513537, 757480018183143335828203814814, 757480020427382739989855235323, 757480022716506941367954897985, 757480025051413636276074600700, 757480027433018474968529498726, 757480029862255420720197031644, 757480032340077116088200615452, 757480034867455256496946932303, 757480037445380971297031444841, 757480040074865212444238343776, 757480042756939150952636354616, 757480045492654581275734889108, 757480048283084333776731361879, 757480051129322695447729165970, 757480054032485839042550941037, 757480056993712260793070221264, 757480060014163226879876111233, 757480063095023228832147704294, 757480066237500448035615987631, 757480069442827229530415702282, 757480072712260565286000201347, 757480076047082587140416844196, 757480079448601069598543966619, 757480082918149942687091454148, 757480086457089815066733731807, 757480090066808507604765662210, 757480093748721597622072180445, 757480097504272974022830490288, 757480101334935403527742089353, 757480105242211108232334794521, 757480109227632354715422417942, 757480113292762054931233148810, 757480117439194379118000366689, 757480121668555380965880259033, 757480125982503635287453974621, 757480130382730888442784256088, 757480134870962721771858916184, 757480139448959228296624547299, 757480144118515702956894709952, 757480148881463346650707559305, 757480153739669984356034456575, 757480158695040797615296400870, 757480163749519071668630391830, 757480168905086957530780864530, 757480174163766249309583464071, 757480179527619177070656573512, 757480184998749215559631354034, 757480190579301909098672602700, 757480196271465712981960782792, 757480202077472851697722072399, 757480207999600194316343824650, 757480214040170147385477809512, 757480220201551565683513379408, 757480226486160681188111464091, 757480232896462050624728216094, 757480239434969521965503557544, 757480246104247220258758457681, 757480252906910553175806524461, 757480259845627236667605541823, 757480266923118341135799172388, 757480274142159358527219145485, 757480281505581290770010900804, 757480289016271759979017693327, 757480296677176140865957863300, 757480304491298715796871030325, 757480312461703852952382312019, 757480320591517208050251642670, 757480328883926950103320124520, 757480337342185011692916928144, 757480345969608364247354729255, 757480354769580318827208213644, 757480363745551852925933526658, 757480372901042963807198031844, 757480382239644048909034599880, 757480391765017313856828100193, 757480401480898208636521093313, 757480411391096892491886440269, 757480421499499728120128032112, 757480431810070805751750137608, 757480442326853497712549113985, 757480453053972044077360230499, 757480463995633170036994552303, 757480475156127735613616634676, 757480486539832418370248765962, 757480498151211429775616779324, 757480509994818265896423664761, 757480522075297493104267865942, 757480534397386569497281367699, 757480546965917702750632279971, 757480559785819745124957718505, 757480572862120126375514733379, 757480586199946825320180079374, 757480599804530380839656708075, 757480613681205943098354816296, 757480627835415365790416822542, 757480642272709340231741565496, 757480656998749572134427212695, 757480672019311001917880501747, 757480687340284069426690564707, 757480702967677023944209005727, 757480718907618280407249309396, 757480735166358822746053569892, 757480751750274655292345460203, 757480768665869303216455212593, 757480785919776362974531094575, 757480803518762103765784902542, 757480821469728121020426871511, 757480839779714042958285148212, 757480858455900291280295278453, 757480877505610897075161603775, 757480896936316373045601908519, 757480916755636643180817165559, 757480936971344031023762686748, 757480957591366307705751401844, 757480978623789800943356042815, 757481000076862566216929085439, 757481021958997621375025531347, 757481044278776245932331745293, 757481067044951346356014197532, 757481090266450888659831735744, 757481113952381399652215849216, 757481138112031538211873537726, 757481162754875737990978568143, 757481187890577922975322314763, 757481213528995297357940433629, 757481239680182211213032932433, 757481266354394103486351233418, 757481293562091523848017289590, 757481321313944234985678941608, 757481349620835396946610160991, 757481378493865835170051167058, 757481407944358393883454717427, 757481437983862376570441738917, 757481468624158075251667186929, 757481499877261390355269942320, 757481531755428542988730645559, 757481564271160881460388250354, 757481597437209783935653519052, 757481631266581659150976283725, 757481665772543047146813978826, 757481700968625822020067765630, 757481736868632498736805871517, 757481773486641646086431731923, 757481810837013407900559227862, 757481848934395134701995827901, 757481887793727127992593933895, 757481927430248499433281757210, 757481967859503147213958365735, 757482009097345851957662674885, 757482051159948494549822693795, 757482094063806398331314664232, 757482137825744798143041946462, 757482182462925438759266352488, 757482227992853305297874471979, 757482274433383488247267938568, 757482321802728185802885226415, 757482370119463846259493562137, 757482419402538453261082510465, 757482469671278956765753034665, 757482520945398852640292356295, 757482573245005913857487881924, 757482626590610076328699196198, 757482681003131482464726710518, 757482736503908685620252122081, 757482793114707018639692129830, 757482850857727129787330299070, 757482909755613689409731520917, 757482969831464270745682575181, 757483031108838408367296154412, 757483093611766837805339031618, 757483157364760919983191666555, 757483222392822254156277567599, 757483288721452483127719973446, 757483356376663294586352526965, 757483425384986622490514945561, 757483495773485052499035991735, 757483567569762435531323536069, 757483640801974713619903650871, 757483715498840962302084236868, 757483791689654653882537226319, 757483869404295145984950323283, 757483948673239399899755666962, 757484029527573933324585614621, 757484111999007012186576807135, 757484196119881086329151553362, 757484281923185473941666247217, 757484369442569299708061553741, 757484458712354691750063276009, 757484549767550242542038696402, 757484642643864739078440598923, 757484737377721167680061880312, 757484834006270998933493761110, 757484932567408758367841649327, 757485033099786888585010556832, 757485135642830908674309535282, 757485240236754876858679643167, 757485346922577162438937253546, 757485455742136533223857436775, 757485566738108564757689850762, 757485679954022377782973507449, 757485795434277710505534029711, 757485913224162332359693619097, 757486033369869806106021423572, 757486155918517605230584616766, 757486280918165593754045239600, 757486408417834875701418223067, 757486538467527021628227419086, 757486671118243679746914027416, 757486806422006579348343047233, 757486944431877934367212464531, 757487085201981255097287895261, 757487228787522576222696011138, 757487375244812109494796515560, 757487524631286329551055280768, 757487677005530501542336394967, 757487832427301659408402270028, 757487990957552043818613853326, 757488152658453008974986463279, 757488317593419407659170782157, 757488485827134464092508864325, 757488657425575144370018224118, 757488832456038034424430271383, 757489010987165735675869352239, 757489193088973788725900826298, 757489378832878135662242225376, 757489568291723131751769807534, 757489761539810117515438920826, 757489958652926562398644543744, 757490159708375791475211565474, 757490364785007306852144995065, 757490573963247715675863942074, 757490787325132276879000743941, 757491004954337079049824820709, 757491226936211862054348944933, 757491453357813495294057744304, 757491684307940125740178072726, 757491919877166009148554591347, 757492160157877038127658669648, 757492405244306981005981653354, 757492655232574445724497343591, 757492910220720583264611338836, 757493170308747545412795573897, 757493435598657711959429601222, 757493706194493702731812694005, 757493982202379190169772448515, 757494263730560528466870936082, 757494550889449215621285283624, 757494843791665205067693391541, 757495142552081083895551661909, 757495447287867134999794221322, 757495758118537300857450295988, 757496075165996066978181854575, 757496398554586283438317702319, 757496728411137943276788563501, 757497064865017936907633164568, 757497408048180802087540519593, 757497758095220489368374014653, 757498115143423163363997789290, 757498479332821060568127161841, 757498850806247424875435385229, 757499229709392542382102361254, 757499616190860897474363077722, 757500010402229472654753904921, 757500412498107215005685655312, 757500822636195692648980714516, 757501240977350965028238156906, 757501667685646691318494352256, 757502102928438501754909462049, 757502546876429657169164068973, 757502999703738022529304111409, 757503461587964380795937603785, 757503932710262113935269036449, 757504413255408278467649883094, 757504903411876103479349984678, 757505403371908939585276729501, 757505913331595687901694990562, 757506433490947738670800529569, 757506964053977449773498902052, 757507505228778195973257540050, 757508057227606020352537999083, 757508620266962920034459776571, 757509194567681798926183355423, 757509780355013120877250335266, 757510377858713297316145723796, 757510987313134844111829425485, 757511608957318343104209427118, 757512243035086244458831604979, 757512889795138546726671810569, 757513549491150392230111294990, 757514222381871616151330989243, 757514908731228288469689072894, 757515608808426288680501909369, 757516322888056954029366276979, 757517051250204842813996339844, 757517794180557655139886566085, 757518551970518354367305331938, 757519324917319533355387352584, 757520113324140070494994518256, 757520917500224121425652554915, 757521737761002493253846022129, 757522574428216449030457055519, 757523427830043991204662389963, 757524298301228673750472736024, 757525186183210993660731818660, 757526091824262413522203712448, 757527015579622067924751336411, 757527957811636207517971725354, 757528918889900435610445106899, 757529899191404793310421953415, 757530899100681750332701659056, 757531919009957159745196668923, 757532959319304236100606557715, 757534020436800617594269250094, 757535102778688574109091344729, 757536206769538424252964684062, 757537332842415225763761123929, 757538481439048804952411397631, 757539653010007192176163468761, 757540848014873531682536409252, 757542066922426535540145786191, 757543310210824552776186317829, 757544578367793326272332028617, 757545871890817511431901601980, 757547191287336032121770747174, 757548537074941350913444169747, 757549909781582732199450514865, 757551309945773578344471469848, 757552738116802920646027174279, 757554194854951148527704030543, 757555680731710062069613804538, 757557196330007334696582404636, 757558742244435474595294342740, 757560319081485375217917556359, 757561927459784547052361289042, 757563568010340124699027346320, 757565241376786745191479022433, 757566948215639395434620134750, 757568689196551328609604106913, 757570465002577151410538050845, 757572276330441186034990418449, 757574123890811212949184909139, 757576008408577702590428282196, 757577930623138646354697580522, 757579891288690099447272101681, 757581891174522550449807764866, 757583931065323234779211015398, 757586011761484511583113589537, 757588134079418426034596808174, 757590298851877581456129927391, 757592506928282448220476414914, 757594759175055238945649538053, 757597056475960482122937039344, 757599399732452428992681379899, 757601789864029431212996398482, 757604227808595429653100874554, 757606714522828697486618901928, 757609250982557983662227195044, 757611838183146205790673288474, 757614477139881844509676070614, 757617168888378194472851332726, 757619914484980630256882017215, 757622715007182048694017246182, 757625571554046652416013072843, 757628485246642242742204559942, 757631457228481193459978168968, 757634488665970280531931580284, 757637580748869546321988909774, 757640734690760380564187059054, 757643951729523004004340800424, 757647233127823544427933998219, 757650580173610898648981776333, 757653994180623577975971074412, 757657476488906738693986845456, 757661028465339603208544693242, 757664651504173481688250071277, 757668347027580608322017521786, 757672116486214010674090777975, 757675961359778635078402735516, 757679883157613955564871850173, 757683883419288298456046005721, 757687963715205119515110993208, 757692125647221475367797391149, 757696370849278935863255163697, 757700700988047189084746114260, 757705117763580595872240966692, 757709622909987955978018056562, 757714218196115753345477372932, 757718905426245153483017529069, 757723686440803031501424144340, 757728563117087315097315127469, 757733537370006932599338581025, 757738611152836662150679646470, 757743786457987184183677285175, 757749065317790645552769314676, 757754449805302050033375727633, 757759942035116796369611425691, 757765544164204691665840204275, 757771258392760774669087315239, 757777086965073290384315554013, 757783032170409164505730381575, 757789096343917333337868572247, 757795281867550292223579118373, 757801591171004232995546441010, 757808026732678148627234637239, 757814591080652291081633386114, 757821286793686376345643461542, 757828116502237938798107792013, 757835082889501245394239122724, 757842188692467188662468619914, 757849436703004586205591116438, 757856829768963323280665060183, 757864370795299784105694673642, 757872062745225026810040119760, 757879908641376166414236561867, 757887911567011439898044974587, 757896074667229437297796982400, 757904401150212992870259422416, 757912894288498240675264488862, 757921557420269349468301665095, 757930393950679462562335711705, 757939407353198379320638029571, 757948601170987526184856730653, 757957979018302776630509530725, 757967544581925691181325038027, 757977301622623760610267854717, 757987253976640247714732688671, 757997405557214235582483280732, 758007760356131503069829092219, 758018322445306861300814262503, 758029095978398598372562633561, 758040085192455693124272512879, 758051294409598472802762289162, 758062728038733403743209669735, 758074390577302718787254623150, 758086286613069600089624434493, 758098420825939651226751063127, 758110797989819408124575300117, 758123422974512654276168732719, 758136300747655322031489453434, 758149436376689778420276909690, 758162835030879311023798606121, 758176501983363646851131742880, 758190442613256355010413933258, 758204662407785002204794620764, 758219166964474948736716032254, 758233961993377691782972837182, 758249053319344682217362471729, 758264446884347561218561859776, 758280148749845783319375231571, 758296165099202613441240228423, 758312502240150506826728506975, 758329166607306902644948491922, 758346164764741484412818438067, 758363503408595983262055482618, 758381189369757623500724939494, 758399229616587333883002450988, 758417631257703872525511684545, 758436401544825038507711937447, 758455547875667168882253230016, 758475077796904146114361420750, 758494999007187167882986024595, 758515319360226558726936127326, 758536046867936931223326367977, 758557189703647033260641125297, 758578756205375647532407506782, 758600754879174939648187541986, 758623194402542682255260065375, 758646083627904814306435369378, 758669431586169827117002583270, 758693247490356502147536243181, 758717540739296559550507100736, 758742320921413811449335349843, 758767597818581449701355257759, 758793381410059134554498745320, 758819681876511588165452880072, 758846509604110435429458535963, 758873875188721074004434269034, 758901789440176395821184134650, 758930263386639223784367770533, 758959308279055369813838686356, 758988935595699263881952396772, 759019157046814148299503384609, 759049984579348877222030980057, 759081430381793408221300551434, 759113506889115120826818782133, 759146226787798146223356559318, 759179603020987942827820322862, 759213648793743404298780363474, 759248377578398839692076102439, 759283803120038220004961547796, 759319939442084141289302973181, 759356800852004011902807225783, 759394401947136030348937148056, 759432757620637580575295288855, 759471883067558733602550056944, 759511793791043607988711291568, 759552505608662406945608810232, 759594034658877016966328035686, 759636397407643121646379682907, 759679610655151855041587036677, 759723691542714091457989022353, 759768657559790543071336615953, 759814526551170913285867870361, 759861316724305432325931573655, 759909046656792182273802865348, 759957735304023701689056379162, 760007402006996445137829002578, 760058066500286760495335203386, 760109748920197136835733899701, 760162469813076568166146476570, 760216250143818973275270637267, 760271111304543709633432341852, 760327075123462319684816380594, 760384163873935751101817173258, 760442400283726398716936098211, 760501807544449425003701422008, 760562409321227928242419346099, 760624229762556642980468742773, 760687293510378976185330701271, 760751625710382304700465735762, 760817252022516585362403622837, 760884198631741458539064015537, 760952492259007159025802531454, 761022160172474685312927724064, 761093230198980819347125171400, 761165730735753734184925754264, 761239690762385076519745723692, 761315139853064565101102064604, 761392108189083304706900792087, 761470626571612178734506966664, 761550726434761851806936442002, 761632439858931087216518751813, 761715799584450262725840966798, 761800839025527152397555230272, 761887592284502231920650961082, 761976094166420960538360583345, 762066380193930694366969071714, 762158486622510093838423323131, 762252450456039102424122860517, 762348309462717794932655551462, 762446102191342621759628511200, 762545867987948810751704437543, 762647647012827931087920693927, 762751480257929874048068678785, 762857409564658764009803716900, 762965477642072579783901286584, 763075728085496541763019322213, 763188205395560604638009521901, 763302954997671688954511311137, 763420023261931587881813254556, 763539457523511798600200943830, 763661306103496851051128605585, 763785618330208040820576231379, 763912444561019818039695927787, 764041836204681440804614167821, 764173845744156870172571904457, 764308526759996264735981155424, 764445933954252826579789396215, 764586123174959157580758869106, 764729151441177706020412284583, 764875076968640318888464044714, 765023959195992365604986087752, 765175858811657364765255080064, 765330837781338527513637643459, 765488959376174129910101420823, 765650288201564142819945112291, 765814890226686082117156197899, 765982832814718595056849182335, 766154184753791871285675263722, 766329016288684559896269534008, 766507399153287488001741048195, 766689406603855112353200527214, 766875113453066294428567668680, 767064596104916672104272370819, 767257932590465608443321456661, 767455202604461431296318492797, 767656487542869437363608571476, 767861870541327922200541788343, 768071436514558314506471095040, 768285272196756340115226300561, 768503466182992019647751687515, 768726108971647215099883942258, 768953293007920386082346054469, 769185112728429197430224591437, 769421664606942637944609005305, 769663047201275366676857796318, 769909361201378100044655010506, 770160709478658991882082243955, 770417197136572141055438625709, 770678931562510589387125060256, 770946022481042448272876011021, 771218582008530117595302454527, 771496724709173937467040623368, 771780567652523044218157066739, 772070230472497689218747693977, 772365835427968825053694187419, 772667507464942370813681217155, 772975374280397239528750709677, 773289566387827948870643254315, 773610217184544444146224259220, 773937463020783643397214645761, 774271443270689171361989590701, 774612300405217785551897122421, 774960180067033117321953134540, 775315231147449557323248973452, 775677605865491412045340360330, 776047459849134850418428297209, 776424952218802650978542618100, 776810245673184355450444623375, 777203506577457138545356597491, 777604905053985521315413378581, 778014615075580991817062985900, 778432814561405657639962722314, 778859685475607245864417930832, 779295413928776093322340797576, 779740190282318240068573346729, 780194209255842358464151547165, 780657670037662026320220700683, 781130776398518792606250882962, 781613736808635596130640822043, 782106764558214389605371226090, 782610077881496302289596111724, 783123900084507353105697781662, 783648459676617612352190112968, 784183990506046814026207624995, 784730731899454752976978894227, 785288928805760372871883927984, 785858831944339274100868832178, 786440697957755457741591784144, 787034789569189485698169985801, 787641375744731891964578499820, 788260731860717640257513868801, 788893139876284704419297796699, 789538888511347466261342156496, 790198273430183598051019427691, 790871597430841441737148341919, 791559170640583633365747810925, 792261310717591869129204954134, 792978343059167290420946735710, 793710601016671001636620583353, 794458426117459750047498670330, 795222168294082816999428681233, 796002186121017720522676627693, 796798847059234439259002755917, 797612527708890566124406271298, 798443614070473118749706758782, 799292501814716705723058388801, 800159596561642408186059765523, 801045314169077122659293469682, 801950081031029262539374379122, 802874334386313674297805925855, 803818522637836434286001133540, 804783105682968900118382227710, 805768555255460046588894067490, 806775355279356772695415051019, 807804002235423579514349549397, 808855005540575847699420555675, 809928887940864951216042801478, 811026185918578697373674837793, 812147450114047153214593563036, 813293245762771880188696062931, 814464153148526032814183725296, 815660768073103767727642063921, 816883702343430047548177548046, 818133584276776305416893064003, 819411059224863663127758116868, 820716790117673577165777013176, 822051458027826038414974716905, 823415762756427895952575340066, 824810423441338644346189451278, 826236179188848246895173924731, 827693789729811413122088414628, 829184036101335366127760527137, 830707721355173693258126208787, 832265671294037552207905027609, 833858735237097496558058842513, 835487786816014695070126162972, 837153724802909566943008425357, 838857473971749074630837703828, 840599985994711356618948308230, 842382240375168311768116189613, 844205245419013449856179615468, 846070039246154104911406600485, 847977690844084295210582354877, 849929301165557455596169447425, 851926004272487337787497349277, 853968968528320972768922531161, 856059397841250144709924100658, 858198532960757797395521448193, 860387652830133673980363060285, 862628075997739806717087784086, 864921162089961791141334410526, 867268313348946706318692457014, 869670976238403731029631045859, 872130643120929655134946415663, 874648854010519347697304257181, 877227198404131626686930532304, 879867317196404747823409426726, 882570904681853826359363767866, 885339710649135930294461530360, 888175542572238418159189086968, 891080267903733503616875075043, 894055816475548267006632819486, 897104183013025752190839768701, 900227429768400842719671397067, 903427689280185875739380002664, 906707167265357120602218818051, 910068145651656151687656661517, 913512985757771757493558234340, 917044131629650485232060087887, 920664113541699528992378215002, 924375551672196924449054702574, 928181159962813612370649367500, 932083750172782796890411807643, 936086236138927314167010901115, 940191638253478867210768601239, 944403088172397684379700721541, 948723833767731445897813105525, 953157244338442559048788463285, 957706816095087784697487543774, 962376177934758967811219532275, 967169097523793788615836490946, 972089487706947099695997216317, 977141413262983148698032746695, 982329098028013987374693970059, 987656932409377451602943069266, 993129481314427775312002386145, 998751492520312447783093914992, 1004527905512640448054046110602, 1010463860822920518557666821152, 1016564709896775705421911722238, 1022836025527235133169612277003, 1029283612889880249649302550787, 1035913521219296261266793330313, 1042732056169167336727119824893, 1049745792901475164857607082882, 1056961589953635165705580267326, 1064386603936055594745022548104, 1072028305116556634051612093411, 1079894493952366407803657788820, 1087993318635048407183449782385, 1096333293718742691779690402213, 1104923319907557304095996666981, 1113772705083866009493700792158, 1122891186665697121584623210966, 1132288955388383530578944006006, 1141976680613238703378777403722, 1151965537274285328488052451047, 1162267234583056361310050508757, 1172894046621283037657698054385, 1183858844961958881572585329274, 1195175133470908945252304188671, 1206857085453694708164302987663, 1218919583326552607540346896973, 1231378261005214769370519804706, 1244249549222023477552980658566, 1257550723999869669875690151399, 1271299958531319434440478188425, 1285516378733017846822936256457, 1300220122769272970585134262932, 1315432404864842916471129560767, 1331175583755618690060535348285, 1347473236157386019347225047793, 1364350235667462388550416781224, 1381832837552077967184114633876, 1399948769914277109644622510121, 1418727331783280853029979792844, 1438199498717140310487419032205, 1458398036566652012266389882589, 1479357624110488236188300656084, 1501114985339978665860948530928, 1523709032247705375946555406532, 1547181019057873356614304135203, 1571574708929228889599303843405, 1596936554264170268902291426614, 1623315891871814323199025167728, 1650765154359483047657419952928, 1679340099267863359491072697262, 1709100057621669826451195499060, 1740108203741926620578749137427, 1772431848360154354515080509370, 1806142757291260698614659428971, 1841317498163579699438571603668, 1878037817974447438918301733915, 1916391054541533964280514931070, 1956470585257957394789453716798, 1998376316937633034571054176429, 2042215220961651730987052796174, 2088101918412773635097464789449, 2136159320420255902584190146307, 2186519329539078896107065042041, 2239323608665201632996620053788, 2294724424752077964859056095818, 2352885575455125714403857872478, 2413983407803734958250359616608, 2478207939100326099683447044252, 2545764091490867349002367659631, 2616873053061802993711338151030, 2691773779918363017775699666546, 2770724655516240633814980224119, 2854005325584450092276210875229, 2941918729328634993472373868306, 3034793350283861473551908379614, 3132985713243520653121620410507, 3236883157183918324270498983264, 3346906918099389173671905757498, 3463515560238325727763197446569, 3587208799477337802924016627758, 3718531768595136900602765979163, 3858079781133999624652994400092, 4006503658510450438642255523943, 4164515694228979905950197503087, 4332896339663917757505870555044, 4512501708141194417382944492410, 4704272008251954028434880079325, 4909241033792259887411268202585, 5128546856835647919274087813310, 5363443892667566773986828210301, 5615316531187641782367438327661, 5885694559564255451636503737511, 6176270636175804528344521610618, 6488920117111191662208418869089, 6825723584823069969480172563921, 7188992485239474140249352406493, 7581298346309629522880093466685, 8005506129467674714535276212197, 8464812358102846806230710745239, 8962788776546243370108655865276, 9503432422603271655682807294918, 10091223150241799577184822229016, 10731189821488689691394692867062, 11428986603714241779423048081571, 12190981067371677792861822243257, 13024356088525102866437999671579, 13937227930660441287621756870526, 14938783324188151768076734460200, 16039438895469279428636726881561, 17251026939472727442733901540271, 18587012305105309119305023106818, 20062746099200798490414867762717, 21695763050387041392496700725053, 23506130752505437199723288739578, 25516860684718428552492266264108, 27754392951320796828017981114168, 30249169185143972053715997313731, 33036311122545854396921386661466, 36156426120958698028897509871712, 39656565522241534380696177526656, 43591367481286883649349184761810, 48024422950478467901954609189002, 53029912279773608605085397696382, 58694570794855741435470613971709, 65120055306160377601638882464997, 72425800486822257939335997918761, 80752475342663866450187228048644, 90266176743463101480103167987570, 101163530686213239365267742931592, 113677914546444405805871235338883, 128087067539142122090122405496267, 144722425197096786428104112533083, 163980601101703587990913818254774, 186337550881643747533011806138745, 212366096851511981783739548100356, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 237684487542793012780631851008000, 236555652226970570506898624061357, 231917306104873108340096690256233, 227369907945954027784408519859052, 222911674456817674298439725352012, 218540857310605563037686005247070, 214255742461378002978123534555951, 210054649471939218606003465250932, 205935930854842371182356338481306, 201897971426316050178780724001281, 197939187672858872724294827452236, 194058027130253796788524340639447, 190252967774758624302474843764164, 186522517426233945394583180160945, 182865213162974456269199196236221, 179279620748014172812940388466883, 175764334066680561581314106340081, 172317974575177021158151084647139, 168939190759977471723677533967783, 165626657607821050709487778399787, 162379076086099069323027233725282, 159195172633430460120614935024786, 156073698660225941294720524534104, 153013430059045040485020122092259, 150013166724553961259823649110057, 147071732082896040450807499127507, 144187972630290235736085783458341, 141360757480676701702044885743471, 138588977922232060492200868375952, 135871546982580451462942027819561, 133207399002529854375433360607413, 130595489218166523897483686870012, 128034793351143650879885967519620, 125524307207003579294005850509431, 123063046281376058131378284813168, 120650045373898096207233612561929, 118284358209704015889444718197970, 115965057068337270479847762939186, 113691232419938500470438983273712, 111461992568567157323959787523247, 109276463302516820905842928944360, 107133787551487079319453851906235, 105033125050477528744562599908074, 102973652010272087004473137164778, 100954560794384399023993271730175, 98975059602337646101954187970760, 97034372159154555001915870559568, 95131737410935838237172422117224, 93266409226407684546247472663945, 91437656104321259359066149670534, 89644760886589469959868774186798, 87887020477048499960655660967449, 86163745565733823490838883301421, 84474260358562572049842042452373, 82817902312316247107688276914092, 81194021874819850105576742072639, 79601982230215539319192884384940, 78041159049230920901169494495039, 76510940244344040099185778916705, 75010725729749058920770371486966, 73539927186028489138010168124476, 72097967829439695233343302082820, 70684282185725191405238531453745, 69298315868358030789449540640927, 67939525361135324303381902589144, 66607377805034631669982257440337, 65301350789249638892139468078762, 64020932146323175384450458900747, 62765619751297230769069077353673, 61534921324801206636342232699680, 60328354240001182976806110489882, 59145445333334493114515794597924, 57985730718955385406388033919533, 56848755606819005300380425411307, 55734074124332358137627868050301, 54641249141502311899635164755197, 53569852099512070489838396818821, 52519462842658892637096467469432, 51489669453587149644212223009247, 50480068091752107494325708832595, 49490262835051085778750694933917, 48519865524559888018383034248938, 47568495612313615704297092400920, 46635780012072172259114796471490, 45721352953011933587367447521068, 44824855836286209399379850510851, 43945937094398244509195931873384, 43084252053331612263917580268023, 42239462797383933592076059086297, 41411238036650915286349077535586, 40599252977108740476812821113319, 39803189193243863212561589326784, 39022734503180258051530969928219, 38257582846255154952481343066882, 37507434162995249953413081438119, 36771994277446323483738315135411, 36050974781810121062488544250403, 35344092923343255943616219853336, 34651071493473780336878646915036, 33971638719091941506743771485329, 33305528155972491673278207338558, 32652478584286756542429615037802, 32012233906163486806303544154708, 31384543045258320398336807994812, 30769159848292470978761576465501, 30165842988522030371334878887747, 29574355871100029775818508713477]
def winsorResidualPayData : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1676076622115331992326402477, 3499780771611071637885167776, 5287726016214737957060427874, 7040613510924214740565584833, 8759130662600172371452993616, 10443951399537385735068100266, 12095736435750340013122126393, 13715133530076765775920191224, 15302777740200712602192803803, 16859291671694778118146345548, 18385285722179156074963543336, 19881358320693252111058835286, 21348096162373738420956180334, 22786074438531077940463381363, 24195857062214744136058676488, 25577996889355593347426612886, 26933035935572112182101060334, 28261505588725562020017185284, 29563926817307375586601621509, 30840810374740526142076558985, 32092656999674987470973556510, 33319957612355831911068652123, 34523193507140973519005020371, 35702836541244053526785773555, 36859349319776484906962982559, 37993185377161221554195540406, 39104789354989394737756871629, 40194597176389564525562098318, 41263036216977966278312320562, 42310525472456791526106656095, 43337475722926228043552083089, 44344289693974695217518187984, 45331362214610447348857506509, 46299080372096478850170563887, 47247823663749450910281404453, 48177964145762168616272424616, 49089866579107970288812640462, 49983888572584246438361871684, 50860380723051183839880725823, 51719686752920730311958033802, 52562143644949697441445590644, 53388081774389861293884371863, 54197825038546884678628275017, 54991690983798868389161513405, 55769990930124342615174492216, 56533030093188533032834275364, 57281107704035778540343866685, 58014517126435038841823858177, 58733545971924509725627771404, 59438476212600461572494353000, 60129584291694532010598844760, 60807141231982836361681679819, 61471412742069409254900145563, 62122659320585657189428053155, 62761136358346684576220119422, 63387094238504554563271164781, 64000778434737760432929052389, 64602429607515413246319138279, 65192283698473896396701575426, 65770572022942997524527494197, 66337521360657802551807806718, 66893354044691925127572818993, 67438288048646947260675772205, 67972537072132263077443373392, 68496310624568847211529256909, 69009814107349812048868358396, 69513248894389973654102771619, 70006812411096014443548274779, 70490698211788211295945826896, 70965096055604090563002250541, 71430191980913776118939920781, 71886168378276212938486656310, 72333204061964876487061887221, 72771474340091017220959172427, 73201151083351939509093765767, 73622402792431275085696308258, 74035394664077682513738016581, 74440288655887885874563220820, 74837243549819457796940872035, 75226415014458253799271902637, 75607955666064916546655265973, 75982015128424389828403661400, 76348740091521912653647186329, 76708274369068503658787897044, 77060758954898494840298397744, 77406332078261231292759672941, 77745129258028619971643276074, 78077283355839785343097788951, 78402924628203672962170840790, 78722180777580033373026773966, 79035177002458818089552198648, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336]
def winsorPayChecks : Bool :=
  ((winsorMGFPayData.zip winsorResidualPayData).zipIdx).all (fun e =>
    let b := e.2
    let un := 1353 * 51 ^ b
    let ud := 2^70 * 50 ^ b
    let u := min winsorScale (winsorCeil (winsorScale * un) ud)
    (e.1.1 == 3000 * winsorScale ||
      winsorScale * (winsorExpNum u ^ 8 - winsorExpDen ^ 8) * ud * 51 ^ 9 ≤
        e.1.1 * winsorExpDen ^ 8 * un * 50 ^ 9) &&
    (e.1.2 == winsorScale ||
      winsorScale * (un - ud) * 51 ^ 9 ≤ e.1.2 * un * 50 ^ 9))
def winsorPackedSums : List Nat → List Nat → Nat → Nat × Nat × Nat
  | m :: ms, t :: ts, p =>
    let n := p % (2^4608)
    let v := winsorPackedSums ms ts (p / (2^4608))
    (n + v.1, n*m + v.2.1, n*t + v.2.2)
  | _, _, _ => (0,0,0)
end ClaudeWCT.Numerics.N600
namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
def coverageProfilePackWith (hs : Array Nat) (ms : List Nat) : Nat :=
  (ms.zipIdx 2).foldr (fun e s => if e.1=0 then s else (hs[e.2]?.getD 0) ^ e.1 * s) 1
def coveragePrepared (base : Nat) : List (List Nat × Nat) :=
  let hs := (List.range 8).map (coverageHPack base) |>.toArray
  coverageProfiles.map (fun ms => (ms, coverageProfilePackWith hs ms))
def coverageOtherPrepared (base : Nat) (prepared : List (List Nat × Nat)) (n : Nat) : Nat :=
  prepared.foldr (fun e acc =>
    if coverageProfileUsed e.1 ≤ n then
      coverageProfileCount n e.1 * 563 ^ (n - coverageProfileUsed e.1) *
        base ^ (n - coverageProfileUsed e.1) * e.2 + acc
    else acc) 0
def coverageRetainedFastPack (base r : Nat) : Nat :=
  let prepared := coveragePrepared base
  (List.range 8).foldr (fun j acc =>
    if j+1≤r then (fact r / (fact (j+1) * fact (r-(j+1)))) * coverageMarkedPack base (j+1) *
      coverageOtherPrepared base prepared (r-(j+1)) + acc
    else acc) 0
end ClaudeWCT.Numerics.N600
namespace ClaudeWCT.Numerics.N600
def coverageFastBinnedPack (base r : Nat) : Nat :=
  let p := coverageRetainedFastPack (2^512) r
  (List.range 4096).foldr (fun c acc =>
    let n := (p >>> (512*c)) % (2^512)
    if n=0 then acc else n * base ^ coverageBin c + acc) 0
def coverageFastProductPack (r : Nat) : Nat := coverageFastBinnedPack (2^4608) r ^ 9
end ClaudeWCT.Numerics.N600
namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
def coverageHPackBits (bits j : Nat) : Nat :=
  (coverageHData j).foldr (fun e s => (e.2 <<< (bits*e.1)) + s) 0
def coverageMarkedPackBits (bits j : Nat) : Nat :=
  (coverageHData j).foldr (fun e s => ((e.1*e.2) <<< (bits*e.1)) + s) 0
def coveragePreparedBits (bits : Nat) : List (List Nat × Nat) :=
  let hs := (List.range 8).map (coverageHPackBits bits) |>.toArray
  coverageProfiles.map (fun ms => (ms, coverageProfilePackWith hs ms))
def coverageOtherBits (bits : Nat) (prepared : List (List Nat × Nat)) (n : Nat) : Nat :=
  prepared.foldr (fun e acc =>
    if coverageProfileUsed e.1 ≤ n then
      ((coverageProfileCount n e.1 * 563 ^ (n-coverageProfileUsed e.1) * e.2) <<<
        (bits*(n-coverageProfileUsed e.1))) + acc
    else acc) 0
def coverageRetainedBits (bits r : Nat) : Nat :=
  let prepared := coveragePreparedBits bits
  (List.range 8).foldr (fun j acc =>
    if j+1≤r then (fact r / (fact (j+1) * fact (r-(j+1)))) * coverageMarkedPackBits bits (j+1) *
      coverageOtherBits bits prepared (r-(j+1)) + acc
    else acc) 0
def coverageBinnedBits (bits r : Nat) : Nat :=
  let p := coverageRetainedBits 512 r
  (List.range 4096).foldr (fun c acc =>
    let n := (p >>> (512*c)) % (2^512)
    if n=0 then acc else (n <<< (bits*coverageBin c)) + acc) 0
def coverageProductBits (r : Nat) : Nat := coverageBinnedBits 4608 r ^ 9
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
def coverageBinnedLinear (bits r : Nat) : Nat :=
  let p := coverageRetainedBits 512 r
  coverageBinData.toList.zipIdx.foldr (fun e acc =>
    let n := (p >>> (512*e.2)) % (2^512)
    if n=0 then acc else (n <<< (bits*e.1))+acc) 0

def coverageProductLinear (r : Nat) : Nat := coverageBinnedLinear 4608 r ^ 9

end ClaudeWCT.Numerics.N600
end
-- ==== merged from ClaudeWCT_Numerics_N600Cover ====
section

section


namespace ClaudeWCT.Numerics.N600
inductive T6 where
  | leaf (z : Nat)
  | node (a b c d e f : T6)
def lookup : T6 → List Nat → Nat
  | .leaf z, _ => z
  | .node _ _ _ _ _ _, [] => 0
  | .node a _ _ _ _ _, 0 :: l => lookup a l
  | .node _ b _ _ _ _, 1 :: l => lookup b l
  | .node _ _ c _ _ _, 2 :: l => lookup c l
  | .node _ _ _ d _ _, 3 :: l => lookup d l
  | .node _ _ _ _ e _, 4 :: l => lookup e l
  | .node _ _ _ _ _ f, _ :: l => lookup f l
def sel (t : Nat) (P : List (List Nat)) : List (List Nat) :=
  P.filterMap fun p => match p with
    | [] => none
    | h :: r => if h = t then some r else none
def indT : Nat → List (List Nat) → T6
  | 0, P => .leaf P.length
  | n + 1, P => .node (indT n (sel 0 P)) (indT n (sel 1 P)) (indT n (sel 2 P)) (indT n (sel 3 P))
      (indT n (sel 4 P)) (indT n (sel 5 P))
def spair (b : Bool) (h : Nat) : Nat × Nat := cond b (0, h) (h, 0)
def padd (x y : Nat × Nat) : Nat × Nat := (Nat.add x.1 y.1, Nat.add x.2 y.2)
noncomputable section
def zipT (op : Nat → Nat → Nat) (x : T6) : T6 → T6 :=
  T6.rec (motive := fun _ => T6 → T6)
    (fun a y => T6.casesOn (motive := fun _ => T6) y (fun b => .leaf (op a b)) (fun _ _ _ _ _ _ => .leaf a))
    (fun _ _ _ _ _ _ ra rb rc rd re rf y => T6.casesOn (motive := fun _ => T6) y (fun _ => .leaf 0)
      (fun a' b' c' d' e' f' => .node (ra a') (rb b') (rc c') (rd d') (re e') (rf f')))
    x
def mapT (op : Nat → Nat) (x : T6) : T6 :=
  T6.rec (motive := fun _ => T6) (fun a => .leaf (op a))
    (fun _ _ _ _ _ _ ra rb rc rd re rf => .node ra rb rc rd re rf) x
def pT (x : T6) : T6 :=
  T6.rec (motive := fun _ => T6) (fun a => .leaf a)
    (fun _ _ _ _ _ _ a' b' c' d' e' _ =>
      let s2 := zipT Nat.add a' b'
      let s3 := zipT Nat.add s2 c'
      let s4 := zipT Nat.add s3 d'
      .node (mapT (fun _ => 0) a') a' s2 s3 s4 (zipT Nat.add s4 e')) x
def dT (x : T6) : T6 :=
  T6.rec (motive := fun _ => T6) (fun a => .leaf a)
    (fun _ _ _ _ _ _ a' b' c' d' e' f' =>
      .node (zipT Nat.sub b' a') (zipT Nat.sub c' b') (zipT Nat.sub d' c') (zipT Nat.sub e' d')
        (zipT Nat.sub f' e') f') x
def histT (hb : Nat) (c : T6) : List Bool → T6 → Bool → Nat × Nat :=
  T6.rec (motive := fun _ => List Bool → T6 → Bool → Nat × Nat)
    (fun cv _ g neg => T6.casesOn (motive := fun _ => Nat × Nat) g
      (fun gv => cond (Nat.beq gv 0) (0, 0) (spair neg (Nat.mul gv (Nat.pow hb cv))))
      (fun _ _ _ _ _ _ => (0, 0)))
    (fun _ _ _ _ _ _ r0 r1 r2 r3 r4 r5 fr g neg => List.casesOn (motive := fun _ => Nat × Nat) fr (0, 0)
      (fun f fs => T6.casesOn (motive := fun _ => Nat × Nat) g (fun _ => (0, 0))
        (fun g0 g1 g2 g3 g4 g5 => cond f (r5 fs g5 neg)
          (padd (r0 fs g0 (!neg)) (padd (r1 fs g1 (!neg)) (padd (r2 fs g2 (!neg))
            (padd (r3 fs g3 (!neg)) (padd (r4 fs g4 (!neg)) (r5 fs g5 neg)))))))))
    c
def cntT : T6 := pT (indT 6 words)
def g1T : T6 := dT cntT
def g2T : T6 := dT (mapT (fun z => Nat.mul z z) cntT)
end
def noFree : List Bool := [false, false, false, false, false, false]
def freeList (t : Nat) : List Bool := [t == 0, t == 1, t == 2, t == 3, t == 4, t == 5]
open ClaudeWCT.Numerics.Kernel (HB histEq massOk)
noncomputable section
def w1Check : Bool := histEq (histT HB cntT noFree g1T false) w1Data
def w1MassCheck : Bool := massOk (histT 1 cntT noFree g1T false) w1Data
def wfCheck (t : Nat) : Bool := histEq (histT HB cntT (freeList t) g1T false) (wfData t)
def wfMassCheck (t : Nat) : Bool := massOk (histT 1 cntT (freeList t) g1T false) (wfData t)
def w2Check : Bool := histEq (histT HB cntT noFree g2T false) w2Data
def w2MassCheck : Bool := massOk (histT 1 cntT noFree g2T false) w2Data
end
end ClaudeWCT.Numerics.N600
end

section




namespace ClaudeWCT.Numerics.N600
open Finset
def Full : ℕ → T6 → Prop
  | 0, .leaf _ => True
  | 0, .node _ _ _ _ _ _ => False
  | _ + 1, .leaf _ => False
  | n + 1, .node a b c d e f => Full n a ∧ Full n b ∧ Full n c ∧ Full n d ∧ Full n e ∧ Full n f
def pick (t : ℕ) (a b c d e f : T6) : T6 :=
  match t with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _ => f
theorem lookup_node_cons (a b c d e f : T6) (t : ℕ) (l : List ℕ) :
    lookup (.node a b c d e f) (t :: l) = lookup (pick t a b c d e f) l := by
  rcases t with _ | _ | _ | _ | _ | t <;> rfl
theorem full_pick {n : ℕ} {a b c d e f : T6} (h : Full (n + 1) (.node a b c d e f)) (t : ℕ) :
    Full n (pick t a b c d e f) := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  rcases t with _ | _ | _ | _ | _ | t <;> assumption
@[simp] theorem zipT_leaf_leaf (op : ℕ → ℕ → ℕ) (a b : ℕ) :
    zipT op (.leaf a) (.leaf b) = .leaf (op a b) := rfl
@[simp] theorem zipT_node_node (op : ℕ → ℕ → ℕ) (a b c d e f a' b' c' d' e' f' : T6) :
    zipT op (.node a b c d e f) (.node a' b' c' d' e' f') =
      .node (zipT op a a') (zipT op b b') (zipT op c c') (zipT op d d') (zipT op e e') (zipT op f f') := rfl
@[simp] theorem mapT_leaf (op : ℕ → ℕ) (a : ℕ) : mapT op (.leaf a) = .leaf (op a) := rfl
@[simp] theorem mapT_node (op : ℕ → ℕ) (a b c d e f : T6) :
    mapT op (.node a b c d e f) =
      .node (mapT op a) (mapT op b) (mapT op c) (mapT op d) (mapT op e) (mapT op f) := rfl
@[simp] theorem pT_leaf (a : ℕ) : pT (.leaf a) = .leaf a := rfl
theorem pT_node (a b c d e f : T6) :
    pT (.node a b c d e f) = .node (mapT (fun _ => 0) (pT a)) (pT a) (zipT Nat.add (pT a) (pT b))
      (zipT Nat.add (zipT Nat.add (pT a) (pT b)) (pT c))
      (zipT Nat.add (zipT Nat.add (zipT Nat.add (pT a) (pT b)) (pT c)) (pT d))
      (zipT Nat.add (zipT Nat.add (zipT Nat.add (zipT Nat.add (pT a) (pT b)) (pT c)) (pT d)) (pT e)) := rfl
@[simp] theorem dT_leaf (a : ℕ) : dT (.leaf a) = .leaf a := rfl
theorem dT_node (a b c d e f : T6) :
    dT (.node a b c d e f) = .node (zipT Nat.sub (dT b) (dT a)) (zipT Nat.sub (dT c) (dT b))
      (zipT Nat.sub (dT d) (dT c)) (zipT Nat.sub (dT e) (dT d)) (zipT Nat.sub (dT f) (dT e)) (dT f) := rfl
theorem full_zipT (op : ℕ → ℕ → ℕ) : ∀ n x y, Full n x → Full n y → Full n (zipT op x y)
  | 0, .leaf _, .leaf _, _, _ => trivial
  | n + 1, .node a b c d e f, .node a' b' c' d' e' f', ⟨ha, hb, hc, hd, he, hf⟩,
      ⟨ha', hb', hc', hd', he', hf'⟩ =>
    ⟨full_zipT op n a a' ha ha', full_zipT op n b b' hb hb', full_zipT op n c c' hc hc',
      full_zipT op n d d' hd hd', full_zipT op n e e' he he', full_zipT op n f f' hf hf'⟩
theorem full_mapT (op : ℕ → ℕ) : ∀ n x, Full n x → Full n (mapT op x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e f, ⟨ha, hb, hc, hd, he, hf⟩ =>
    ⟨full_mapT op n a ha, full_mapT op n b hb, full_mapT op n c hc, full_mapT op n d hd, full_mapT op n e he,
      full_mapT op n f hf⟩
theorem full_pT : ∀ n x, Full n x → Full n (pT x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e f, ⟨ha, hb, hc, hd, he, _⟩ => by
    have ha' := full_pT n a ha
    have hb' := full_pT n b hb
    have hc' := full_pT n c hc
    have hd' := full_pT n d hd
    have he' := full_pT n e he
    have s2 := full_zipT Nat.add n _ _ ha' hb'
    have s3 := full_zipT Nat.add n _ _ s2 hc'
    have s4 := full_zipT Nat.add n _ _ s3 hd'
    rw [pT_node]
    exact ⟨full_mapT _ n _ ha', ha', s2, s3, s4, full_zipT Nat.add n _ _ s4 he'⟩
theorem full_dT : ∀ n x, Full n x → Full n (dT x)
  | 0, .leaf _, _ => trivial
  | n + 1, .node a b c d e f, ⟨ha, hb, hc, hd, he, hf⟩ => by
    have ha' := full_dT n a ha
    have hb' := full_dT n b hb
    have hc' := full_dT n c hc
    have hd' := full_dT n d hd
    have he' := full_dT n e he
    have hf' := full_dT n f hf
    rw [dT_node]
    exact ⟨full_zipT _ n _ _ hb' ha', full_zipT _ n _ _ hc' hb', full_zipT _ n _ _ hd' hc',
      full_zipT _ n _ _ he' hd', full_zipT _ n _ _ hf' he', hf'⟩
theorem full_indT : ∀ n P, Full n (indT n P)
  | 0, _ => trivial
  | n + 1, _ => ⟨full_indT n _, full_indT n _, full_indT n _, full_indT n _, full_indT n _, full_indT n _⟩
theorem lookup_zipT (op : ℕ → ℕ → ℕ) : ∀ n x y l, Full n x → Full n y → l.length = n →
    lookup (zipT op x y) l = op (lookup x l) (lookup y l)
  | 0, .leaf _, .leaf _, [], _, _, _ => rfl
  | n + 1, .node a b c d e f, .node a' b' c' d' e' f', t :: l, hx, hy, hl => by
    have hl' : l.length = n := by simpa using hl
    rw [zipT_node_node, lookup_node_cons, lookup_node_cons, lookup_node_cons]
    rcases t with _ | _ | _ | _ | _ | t
    · exact lookup_zipT op n a a' l hx.1 hy.1 hl'
    · exact lookup_zipT op n b b' l hx.2.1 hy.2.1 hl'
    · exact lookup_zipT op n c c' l hx.2.2.1 hy.2.2.1 hl'
    · exact lookup_zipT op n d d' l hx.2.2.2.1 hy.2.2.2.1 hl'
    · exact lookup_zipT op n e e' l hx.2.2.2.2.1 hy.2.2.2.2.1 hl'
    · exact lookup_zipT op n f f' l hx.2.2.2.2.2 hy.2.2.2.2.2 hl'
theorem lookup_mapT (op : ℕ → ℕ) : ∀ n x l, Full n x → l.length = n → lookup (mapT op x) l = op (lookup x l)
  | 0, .leaf _, [], _, _ => rfl
  | n + 1, .node a b c d e f, t :: l, hx, hl => by
    have hl' : l.length = n := by simpa using hl
    rw [mapT_node, lookup_node_cons, lookup_node_cons]
    rcases t with _ | _ | _ | _ | _ | t
    · exact lookup_mapT op n a l hx.1 hl'
    · exact lookup_mapT op n b l hx.2.1 hl'
    · exact lookup_mapT op n c l hx.2.2.1 hl'
    · exact lookup_mapT op n d l hx.2.2.2.1 hl'
    · exact lookup_mapT op n e l hx.2.2.2.2.1 hl'
    · exact lookup_mapT op n f l hx.2.2.2.2.2 hl'
def ltB : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: p, b :: l => decide (a < b) && ltB p l
  | _, _ => false
def mtB : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: p, b :: l => (b == 5 || a == b) && mtB p l
  | _, _ => false
@[simp] theorem ltB_cons (a b : ℕ) (p l : List ℕ) : ltB (a :: p) (b :: l) = (decide (a < b) && ltB p l) := rfl
@[simp] theorem mtB_cons (a b : ℕ) (p l : List ℕ) : mtB (a :: p) (b :: l) = ((b == 5 || a == b) && mtB p l) := rfl
@[simp] theorem ltB_nil_cons (b : ℕ) (l : List ℕ) : ltB [] (b :: l) = false := rfl
@[simp] theorem mtB_nil_cons (b : ℕ) (l : List ℕ) : mtB [] (b :: l) = false := rfl
theorem mem_sel {t : ℕ} {P : List (List ℕ)} {r : List ℕ} : r ∈ sel t P ↔ t :: r ∈ P := by
  unfold sel
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    rcases p with _ | ⟨hd, tl⟩
    · simp at h
    · by_cases hh : hd = t
      · subst hh
        simp only [if_true, Option.some.injEq] at h
        rw [← h]; exact hp
      · simp [hh] at h
  · intro h
    exact ⟨t :: r, h, by simp⟩
theorem sel_cons_cons (t h : ℕ) (r : List ℕ) (P : List (List ℕ)) :
    sel t ((h :: r) :: P) = if h = t then r :: sel t P else sel t P := by
  unfold sel; by_cases hh : h = t <;> simp [hh]
theorem sel_cons_nil (t : ℕ) (P : List (List ℕ)) : sel t ([] :: P) = sel t P := by
  unfold sel; simp
theorem countP_sel_succ (s : ℕ) (m : List ℕ) : ∀ P : List (List ℕ),
    P.countP (fun p => ltB p ((s + 1) :: m)) = P.countP (fun p => ltB p (s :: m)) + (sel s P).countP (ltB · m)
  | [] => rfl
  | [] :: P => by
    have h := countP_sel_succ s m P
    rw [sel_cons_nil, List.countP_cons, List.countP_cons]
    simpa using h
  | (h :: r) :: P => by
    have ih := countP_sel_succ s m P
    rw [sel_cons_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hh : h = s
    · subst hh
      rw [if_pos rfl, List.countP_cons]
      cases hb : ltB r m <;> simp [hb]
      omega
    · rw [if_neg hh]
      have hlt : (h < s + 1) ↔ (h < s) := by omega
      by_cases hs : h < s <;> cases hb : ltB r m <;> simp [hb, hs, hlt]
      all_goals omega
theorem countP_sel_zero (m : List ℕ) (P : List (List ℕ)) : P.countP (fun p => ltB p (0 :: m)) = 0 := by
  rw [List.countP_eq_zero]
  intro p _
  rcases p with _ | ⟨h, r⟩ <;> simp
theorem sel_length {n t : ℕ} {P : List (List ℕ)} (hP : ∀ p ∈ P, p.length = n + 1) :
    ∀ p ∈ sel t P, p.length = n := by
  intro p hp
  have := hP _ (mem_sel.mp hp)
  simpa using this
theorem lookup_mapT_zero : ∀ n x l, Full n x → l.length = n → lookup (mapT (fun _ => 0) x) l = 0 :=
  fun n x l hx hl => lookup_mapT _ n x l hx hl
theorem lookup_cnt : ∀ n (P : List (List ℕ)), (∀ p ∈ P, p.length = n) →
    ∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 5) → lookup (pT (indT n P)) l = P.countP (fun p => ltB p l)
  | 0, P, hP, [], _, _ => by
    show P.length = _
    rw [eq_comm, List.countP_eq_length]
    intro p hp
    rw [List.length_eq_zero_iff.mp (hP p hp)]
    rfl
  | n + 1, P, hP, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 5 := hv s (by simp)
    have IH : ∀ t, lookup (pT (indT n (sel t P))) m = (sel t P).countP (ltB · m) := fun t =>
      lookup_cnt n (sel t P) (sel_length hP) m hm (fun v hv' => hv v (by simp [hv']))
    have F : ∀ t, Full n (pT (indT n (sel t P))) := fun t => full_pT n _ (full_indT n _)
    have h1 := countP_sel_succ 0 m P
    have h2 := countP_sel_succ 1 m P
    have h3 := countP_sel_succ 2 m P
    have h4 := countP_sel_succ 3 m P
    have h5 := countP_sel_succ 4 m P
    have h0 := countP_sel_zero m P
    show lookup (pT (.node _ _ _ _ _ _)) (s :: m) = _
    rw [pT_node, lookup_node_cons]
    interval_cases s
    · exact (lookup_mapT_zero n _ m (F 0) hm).trans h0.symm
    · show lookup (pT (indT n (sel 0 P))) m = _
      rw [IH, h1, h0, zero_add]
    · show lookup (zipT Nat.add _ _) m = _
      rw [lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
    · show lookup (zipT Nat.add (zipT Nat.add _ _) _) m = _
      rw [lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
    · show lookup (zipT Nat.add (zipT Nat.add (zipT Nat.add _ _) _) _) m = _
      rw [lookup_zipT _ n _ _ m (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, IH, h4, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
    · show lookup (zipT Nat.add (zipT Nat.add (zipT Nat.add (zipT Nat.add _ _) _) _) _) m = _
      rw [lookup_zipT _ n _ _ m
          (full_zipT _ n _ _ (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3)) (F 4) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (full_zipT _ n _ _ (F 0) (F 1)) (F 2)) (F 3) hm,
        lookup_zipT _ n _ _ m (full_zipT _ n _ _ (F 0) (F 1)) (F 2) hm,
        lookup_zipT _ n _ _ m (F 0) (F 1) hm, IH, IH, IH, IH, IH, h5, h4, h3, h2, h1, h0]
      first | omega | simp [Nat.add_eq]
section DT
variable {ι : Type*}
abbrev hd (p : List ℕ) : ℕ := p.headD 0
theorem filter_ltB_cons (X : Finset ι) (pt : ι → List ℕ) (n : ℕ) (hX : ∀ i ∈ X, (pt i).length = n + 1)
    (t : ℕ) (m : List ℕ) :
    #{i ∈ X | ltB (pt i) (t :: m)} = #{i ∈ X.filter (fun i => hd (pt i) < t) | ltB (pt i).tail m} := by
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hlen := hX i hi
  rcases h : pt i with _ | ⟨a, r⟩
  · rw [h] at hlen; simp at hlen
  · simp [hd]
theorem lookup_dT : ∀ (n : ℕ) (X : Finset ι) (pt : ι → List ℕ) (x : T6), Full n x →
    (∀ i ∈ X, (pt i).length = n ∧ ∀ v ∈ pt i, v ≤ 4) →
    (∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 5) → lookup x l = #{i ∈ X | ltB (pt i) l}) →
    ∀ l : List ℕ, l.length = n → (∀ v ∈ l, v ≤ 5) → lookup (dT x) l = #{i ∈ X | mtB (pt i) l}
  | 0, X, pt, .leaf z, _, hX, hx, [], _, _ => by
    have h := hx [] rfl (by simp)
    show z = _
    rw [show z = lookup (.leaf z) [] from rfl, h]
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    rw [List.length_eq_zero_iff.mp (hX i hi).1]
    rfl
  | n + 1, X, pt, .node a b c d e f, hfull, hX, hx, s :: m, hl, hv => by
    have hm : m.length = n := by simpa using hl
    have hs : s ≤ 5 := hv s (by simp)
    have hmv : ∀ v ∈ m, v ≤ 5 := fun v hv' => hv v (by simp [hv'])
    have hchild : ∀ t, t ≤ 5 → lookup (dT (pick t a b c d e f)) m =
        #{i ∈ X.filter (fun i => hd (pt i) < t) | mtB (pt i).tail m} := by
      intro t ht
      refine lookup_dT n (X.filter (fun i => hd (pt i) < t)) (fun i => (pt i).tail) _ (full_pick hfull t) ?_ ?_ m hm hmv
      · intro i hi
        have h := hX i (Finset.mem_filter.mp hi).1
        refine ⟨by simp [h.1], fun v hv' => h.2 v (List.mem_of_mem_tail hv')⟩
      · intro l hl' hlv
        rw [← lookup_node_cons a b c d e f t l, hx (t :: l) (by simp [hl']) (by
          intro v hv'; rcases List.mem_cons.mp hv' with rfl | hv'; exact ht; exact hlv v hv')]
        exact filter_ltB_cons X pt n (fun i hi => (hX i hi).1) t l
    have F : ∀ t, Full n (dT (pick t a b c d e f)) := fun t => full_dT n _ (full_pick hfull t)
    have hsplit : ∀ t, t ≤ 4 → #{i ∈ X.filter (fun i => hd (pt i) < t + 1) | mtB (pt i).tail m} =
        #{i ∈ X.filter (fun i => hd (pt i) < t) | mtB (pt i).tail m} +
          #{i ∈ X | mtB (pt i) (t :: m)} := by
      intro t ht3
      classical
      haveI : DecidableEq ι := Classical.decEq ι
      simp only [Finset.filter_filter]
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext i
        simp only [Finset.mem_union, Finset.mem_filter]
        have hlen := (hX i)
        constructor
        · rintro ⟨hi, hlt, hmt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inl ⟨hi, hlt', hmt⟩
          · refine Or.inr ⟨hi, ?_⟩
            rcases h : pt i with _ | ⟨a', r⟩
            · rw [h] at hlen; simp at hlen; exact absurd (hlen hi) (by simp)
            · rw [h] at heq hmt; simp only [hd, List.headD_cons] at heq
              simp only [List.tail_cons] at hmt
              simp [heq, hmt]
        · rintro (⟨hi, hlt, hmt⟩ | ⟨hi, hmt⟩)
          · exact ⟨hi, by omega, hmt⟩
          · rcases h : pt i with _ | ⟨a', r⟩
            · rw [h] at hmt; simp at hmt
            · rw [h] at hmt
              simp only [mtB_cons, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmt
              have ha3 : a' ≤ 4 := (hX i hi).2 a' (by simp [h])
              refine ⟨hi, ?_, ?_⟩
              · simp only [hd, List.headD_cons]
                rcases hmt.1 with h4 | h4 <;> omega
              · simpa using hmt.2
      · rw [Finset.disjoint_filter]
        intro i hi ⟨hlt, _⟩ hmt
        rcases h : pt i with _ | ⟨a', r⟩
        · rw [h] at hmt; simp at hmt
        · rw [h] at hmt hlt
          simp only [mtB_cons, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmt
          simp only [hd, List.headD_cons] at hlt
          have ha3 : a' ≤ 4 := (hX i hi).2 a' (by simp [h])
          rcases hmt.1 with h4 | h4 <;> omega
    have hfive : #{i ∈ X.filter (fun i => hd (pt i) < 5) | mtB (pt i).tail m} = #{i ∈ X | mtB (pt i) (5 :: m)} := by
      rw [Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun i hi => ?_
      rcases h : pt i with _ | ⟨a', r⟩
      · have := (hX i hi).1; rw [h] at this; simp at this
      · have ha3 : a' ≤ 4 := (hX i hi).2 a' (by simp [h])
        have h5 : a' < 5 := by omega
        simp [hd, h5]
    have hc : ∀ t, t ≤ 4 → lookup (dT (pick (t + 1) a b c d e f)) m - lookup (dT (pick t a b c d e f)) m =
        #{i ∈ X | mtB (pt i) (t :: m)} := by
      intro t ht
      rw [hchild (t + 1) (by omega), hchild t (by omega), hsplit t ht]
      omega
    rw [dT_node, lookup_node_cons]
    interval_cases s
    · exact (lookup_zipT _ n _ _ m (F 1) (F 0) hm).trans (hc 0 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 2) (F 1) hm).trans (hc 1 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 3) (F 2) hm).trans (hc 2 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 4) (F 3) hm).trans (hc 3 (by norm_num))
    · exact (lookup_zipT _ n _ _ m (F 5) (F 4) hm).trans (hc 4 (by norm_num))
    · exact (hchild 5 le_rfl).trans hfive
end DT
def digitsOf {n : ℕ} (u : Fin n → Fin 6) : List ℕ := List.ofFn fun i => (u i : ℕ)
theorem digitsOf_length {n : ℕ} (u : Fin n → Fin 6) : (digitsOf u).length = n := List.length_ofFn
theorem digitsOf_le {n : ℕ} (u : Fin n → Fin 6) : ∀ v ∈ digitsOf u, v ≤ 5 := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact Nat.lt_succ_iff.mp (u i).isLt
theorem digitsOf_cons {n : ℕ} (t : Fin 6) (u : Fin n → Fin 6) :
    digitsOf (Fin.cons t u : Fin (n + 1) → Fin 6) = (t : ℕ) :: digitsOf u := by
  simp [digitsOf, List.ofFn_succ]
def parU {n : ℕ} (u : Fin n → Fin 6) : Bool := #{i | u i ≠ 5} % 2 == 1
theorem parU_cons {n : ℕ} (t : Fin 6) (u : Fin n → Fin 6) :
    parU (Fin.cons t u : Fin (n + 1) → Fin 6) = (decide (t ≠ 5) ^^ parU u) := by
  unfold parU
  rw [Fin.card_filter_univ_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases ht : t = 5
  · simp [ht]
  · simp only [ht, ne_eq, not_false_eq_true, if_true, decide_true, Bool.true_xor]
    rcases Nat.mod_two_eq_zero_or_one (#{i | u i ≠ 5}) with h | h <;> simp [h, Nat.add_mod]
def FrOk {n : ℕ} (fr : List Bool) (u : Fin n → Fin 6) : Prop := ∀ i : Fin n, fr.getD i false = true → u i = 5
instance {n : ℕ} (fr : List Bool) : DecidablePred (FrOk (n := n) fr) := fun _ => Fintype.decidableForallFintype
theorem frOk_cons {n : ℕ} (f : Bool) (fs : List Bool) (t : Fin 6) (u : Fin n → Fin 6) :
    FrOk (f :: fs) (Fin.cons t u : Fin (n + 1) → Fin 6) ↔ (f = true → t = 5) ∧ FrOk fs u := by
  unfold FrOk
  rw [Fin.forall_fin_succ]
  simp
theorem spair_eq (b : Bool) (h : ℕ) : spair b h = Kernel.signedPair b h := by
  cases b <;> rfl
theorem padd_eq (x y : ℕ × ℕ) : padd x y = x + y := by
  cases x; cases y; rfl
theorem histT_leaf_leaf (hb cv gv : ℕ) (fr : List Bool) (neg : Bool) :
    histT hb (.leaf cv) fr (.leaf gv) neg = cond (Nat.beq gv 0) (0, 0) (spair neg (Nat.mul gv (Nat.pow hb cv))) :=
  rfl
theorem histT_node_node (hb : ℕ) (c0 c1 c2 c3 c4 c5 g0 g1 g2 g3 g4 g5 : T6) (f : Bool) (fs : List Bool)
    (neg : Bool) :
    histT hb (.node c0 c1 c2 c3 c4 c5) (f :: fs) (.node g0 g1 g2 g3 g4 g5) neg =
      cond f (histT hb c5 fs g5 neg) (padd (histT hb c0 fs g0 (!neg)) (padd (histT hb c1 fs g1 (!neg))
        (padd (histT hb c2 fs g2 (!neg)) (padd (histT hb c3 fs g3 (!neg))
          (padd (histT hb c4 fs g4 (!neg)) (histT hb c5 fs g5 neg)))))) := rfl
theorem sum_fin_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → Fin 6) → M) :
    ∑ u, F u = ∑ t : Fin 6, ∑ u : Fin n → Fin 6, F (Fin.cons t u) := by
  rw [← (Fin.consEquiv fun _ => Fin 6).sum_comp, Fintype.sum_prod_type]
  rfl
theorem histT_eq (hb : ℕ) : ∀ (n : ℕ) (c g : T6) (fr : List Bool) (neg : Bool), Full n c → Full n g →
    fr.length = n →
    histT hb c fr g neg = ∑ u : Fin n → Fin 6,
      if FrOk fr u then Kernel.signedPair (neg ^^ parU u) (lookup g (digitsOf u) * hb ^ lookup c (digitsOf u))
      else 0
  | 0, .leaf cv, .leaf gv, [], neg, _, _, _ => by
    rw [histT_leaf_leaf, Fintype.sum_unique, if_pos (show FrOk _ _ from fun i => i.elim0)]
    have hpar : ∀ u : Fin 0 → Fin 6, parU u = false := fun u => by simp [parU]
    rw [hpar, Bool.xor_false]
    show _ = Kernel.signedPair neg (gv * hb ^ cv)
    by_cases hg : gv = 0
    · subst hg; cases neg <;> simp [Kernel.signedPair]
    · have : Nat.beq gv 0 = false := Bool.eq_false_iff.mpr fun h => hg (Nat.eq_of_beq_eq_true h)
      rw [this, cond_false, spair_eq]; rfl
  | n + 1, .node c0 c1 c2 c3 c4 c5, .node g0 g1 g2 g3 g4 g5, f :: fs, neg, hc, hg, hfr => by
    have hfs : fs.length = n := by simpa using hfr
    have IH : ∀ (t : Fin 6) (neg' : Bool), histT hb (pick t c0 c1 c2 c3 c4 c5) fs (pick t g0 g1 g2 g3 g4 g5) neg' =
        ∑ u : Fin n → Fin 6, if FrOk fs u then Kernel.signedPair (neg' ^^ parU u)
          (lookup (pick t g0 g1 g2 g3 g4 g5) (digitsOf u) * hb ^ lookup (pick t c0 c1 c2 c3 c4 c5) (digitsOf u))
          else 0 :=
      fun t neg' => histT_eq hb n _ _ fs neg' (full_pick hc t) (full_pick hg t) hfs
    have e0 : histT hb c0 fs g0 (!neg) = _ := IH 0 (!neg)
    have e1 : histT hb c1 fs g1 (!neg) = _ := IH 1 (!neg)
    have e2 : histT hb c2 fs g2 (!neg) = _ := IH 2 (!neg)
    have e3 : histT hb c3 fs g3 (!neg) = _ := IH 3 (!neg)
    have e4 : histT hb c4 fs g4 (!neg) = _ := IH 4 (!neg)
    have e5 : histT hb c5 fs g5 neg = _ := IH 5 neg
    rw [sum_fin_cons, Fin.sum_univ_six]
    simp only [frOk_cons, parU_cons, digitsOf_cons, lookup_node_cons]
    rw [histT_node_node, e0, e1, e2, e3, e4, e5]
    have d0 : decide ((0 : Fin 6) ≠ 5) = true := rfl
    have d1 : decide ((1 : Fin 6) ≠ 5) = true := rfl
    have d2 : decide ((2 : Fin 6) ≠ 5) = true := rfl
    have d3 : decide ((3 : Fin 6) ≠ 5) = true := rfl
    have d4 : decide ((4 : Fin 6) ≠ 5) = true := rfl
    have d5 : decide ((5 : Fin 6) ≠ 5) = false := rfl
    have q0 : ((0 : Fin 6) = 5) = False := eq_false (by decide)
    have q1 : ((1 : Fin 6) = 5) = False := eq_false (by decide)
    have q2 : ((2 : Fin 6) = 5) = False := eq_false (by decide)
    have q3 : ((3 : Fin 6) = 5) = False := eq_false (by decide)
    have q4 : ((4 : Fin 6) = 5) = False := eq_false (by decide)
    cases f
    · simp only [cond_false, padd_eq, Bool.false_eq_true, false_implies, true_and, d0, d1, d2, d3, d4, d5,
        Bool.true_xor, Bool.false_xor, Bool.xor_not, Bool.not_xor, add_assoc]
    · simp only [cond_true, q0, q1, q2, q3, q4, imp_false, not_true_eq_false, false_and, if_false,
        Finset.sum_const_zero, zero_add, d5, Bool.false_xor, implies_true, true_and]
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem w1_group0 : (w1Check && w1MassCheck && wfCheck 0 && wfMassCheck 0) = true := by decide +kernel
theorem w1_group1 : (wfCheck 1 && wfMassCheck 1 && wfCheck 2 && wfMassCheck 2) = true := by decide +kernel
theorem w1_group2 : (wfCheck 3 && wfMassCheck 3 && wfCheck 4 && wfMassCheck 4) = true := by decide +kernel
theorem w1_group3 : (wfCheck 5 && wfMassCheck 5) = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem w2_all : (w2Check && w2MassCheck) = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

section





namespace ClaudeWCT.Numerics.N600
open Finset
section IE
variable {β : Type*} [Fintype β] (val : β → Fin 6 → ℕ)
def CovMask {p : ℕ} (free : Fin 6 → Bool) (v : Fin 6 → ℕ) (E : Fin p → β) : Prop :=
  ∀ j, free j = false → ∃ e, v j ≤ val (E e) j
instance {p : ℕ} (free : Fin 6 → Bool) (v : Fin 6 → ℕ) : DecidablePred (CovMask val (p := p) free v) :=
  fun _ => Fintype.decidableForallFintype
def cntU (u : Fin 6 → Fin 6) : ℕ := #{x : β | ∀ j, val x j < u j}
def sgnU (u : Fin 6 → Fin 6) : ℤ := (-1) ^ #{j | u j ≠ 5}
def Compat (free : Fin 6 → Bool) (v : Fin 6 → ℕ) (u : Fin 6 → Fin 6) : Prop :=
  ∀ j, u j = 5 ∨ (free j = false ∧ (u j : ℕ) = v j)
instance (free : Fin 6 → Bool) (v : Fin 6 → ℕ) : DecidablePred (Compat free v) :=
  fun _ => Fintype.decidableForallFintype
theorem sum_fin6_single (v : ℕ) (hv : v ≤ 4) (b : Prop) [Decidable b] (X : ℕ → ℤ) :
    ∑ t : Fin 6, (if t = 5 then 1 else if b ∧ (t : ℕ) = v then X t else 0) = 1 + if b then X v else 0 := by
  rw [Fin.sum_univ_six]
  by_cases hb : b <;> interval_cases v <;> simp [hb] <;> ring
omit [Fintype β] in
theorem indicator_covMask {p : ℕ} (free : Fin 6 → Bool) (v : Fin 6 → ℕ) (hv : ∀ j, v j ≤ 4)
    (h3 : ∀ x j, val x j ≤ 4) (E : Fin p → β) :
    (if CovMask val free v E then (1 : ℤ) else 0) =
      ∑ u : Fin 6 → Fin 6, if Compat free v u then
        sgnU u * ∏ e, (if ∀ j, val (E e) j < u j then (1 : ℤ) else 0) else 0 := by
  set A : Fin 6 → ℕ → ℤ := fun j t => ∏ e, (if val (E e) j < t then (1 : ℤ) else 0) with hA
  have h1 : (if CovMask val free v E then (1 : ℤ) else 0) =
      ∏ j, (if free j = false then 1 - A j (v j) else 1) := by
    by_cases hc : CovMask val free v E
    · rw [if_pos hc]
      symm
      refine prod_eq_one fun j _ => ?_
      split_ifs with hf
      · obtain ⟨e, he⟩ := hc j hf
        simp only [hA]
        rw [prod_eq_zero (mem_univ e) (if_neg (Nat.not_lt.mpr he)), sub_zero]
      · rfl
    · rw [if_neg hc]
      have : ∃ j, free j = false ∧ ∀ e, val (E e) j < v j := by
        by_contra hn
        push Not at hn
        exact hc fun j hj => by
          obtain ⟨e, he⟩ := hn j hj
          exact ⟨e, he⟩
      obtain ⟨j, hj, hlt⟩ := this
      symm
      refine prod_eq_zero (mem_univ j) ?_
      rw [if_pos hj, hA]
      simp only
      rw [prod_eq_one (fun e _ => by rw [if_pos (hlt e)]), sub_self]
  have h2 : ∀ j, (if free j = false then 1 - A j (v j) else 1) =
      ∑ t : Fin 6, (if t = 5 then 1 else if free j = false ∧ (t : ℕ) = v j then -A j t else 0) := by
    intro j
    rw [sum_fin6_single (v j) (hv j) (free j = false) (fun t => -A j t)]
    split_ifs <;> ring
  rw [h1]
  simp_rw [h2]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  by_cases hc : Compat free v u
  · rw [if_pos hc]
    have h4 : ∀ j, (if u j = 5 then (1 : ℤ) else if free j = false ∧ (u j : ℕ) = v j then -A j (u j) else 0) =
        (if u j ≠ 5 then (-1 : ℤ) else 1) * A j (u j) := by
      intro j
      by_cases hu : u j = 5
      · rw [if_pos hu, if_neg (not_not.mpr hu), one_mul, hA]
        symm
        refine prod_eq_one fun e _ => ?_
        rw [if_pos]
        rw [hu]
        have := h3 (E e) j
        show val (E e) j < 5
        omega
      · rw [if_neg hu, if_pos ((hc j).resolve_left hu), if_pos hu]
        ring
    rw [prod_congr rfl fun j _ => h4 j, prod_mul_distrib]
    congr 1
    · rw [sgnU, prod_ite, prod_const_one, mul_one, prod_const]
    · rw [hA]
      simp only
      rw [prod_comm]
      refine prod_congr rfl fun e _ => ?_
      by_cases hall : ∀ j, val (E e) j < u j
      · rw [if_pos hall]
        exact prod_eq_one fun j _ => by rw [if_pos (hall j)]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact prod_eq_zero (mem_univ j) (by rw [if_neg (by omega)])
  · rw [if_neg hc]
    have : ∃ j, u j ≠ 5 ∧ ¬(free j = false ∧ (u j : ℕ) = v j) := by
      by_contra hn
      push Not at hn
      exact hc fun j => by
        by_cases hu : u j = 5
        · exact Or.inl hu
        · exact Or.inr (hn j hu)
    obtain ⟨j, hu, hn⟩ := this
    exact prod_eq_zero (mem_univ j) (by rw [if_neg hu, if_neg hn])
theorem card_covMask (p : ℕ) (free : Fin 6 → Bool) (v : Fin 6 → ℕ) (hv : ∀ j, v j ≤ 4)
    (h3 : ∀ x j, val x j ≤ 4) :
    (#{E : Fin p → β | CovMask val free v E} : ℤ) =
      ∑ u : Fin 6 → Fin 6, if Compat free v u then sgnU u * (cntU val u : ℤ) ^ p else 0 := by
  rw [natCast_card_filter]
  simp_rw [indicator_covMask val free v hv h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  split_ifs
  · rw [← mul_sum, cntU, natCast_card_filter, Fintype.sum_pow]
  · exact sum_const_zero
def M1 (u : Fin 6 → Fin 6) : ℕ := #{a : β | ∀ j, u j ≠ 5 → val a j = u j}
def M2 (u : Fin 6 → Fin 6) : ℕ := #{ab : β × β | ∀ j, u j ≠ 5 → max (val ab.1 j) (val ab.2 j) = u j}
def FreeOk (free : Fin 6 → Bool) (u : Fin 6 → Fin 6) : Prop := ∀ j, free j = true → u j = 5
instance (free : Fin 6 → Bool) : DecidablePred (FreeOk free) := fun _ => Fintype.decidableForallFintype
theorem compat_iff (free : Fin 6 → Bool) (v : Fin 6 → ℕ) (u : Fin 6 → Fin 6) :
    Compat free v u ↔ FreeOk free u ∧ ∀ j, u j ≠ 5 → v j = u j := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases h j with h' | ⟨h', _⟩
      · exact h'
      · rw [hj] at h'; exact absurd h' (by simp)
    · exact ((h j).resolve_left hj).2.symm
  · rintro ⟨hf, hv⟩ j
    by_cases hu : u j = 5
    · exact Or.inl hu
    · refine Or.inr ⟨?_, (hv j hu).symm⟩
      by_contra hfj
      exact hu (hf j (by simpa using hfj))
theorem sum_card_covMask (p : ℕ) (free : Fin 6 → Bool) (h3 : ∀ x j, val x j ≤ 4) :
    ∑ a : β, (#{E : Fin p → β | CovMask val free (val a) E} : ℤ) =
      ∑ u : Fin 6 → Fin 6, if FreeOk free u then sgnU u * (M1 val u : ℤ) * (cntU val u : ℤ) ^ p else 0 := by
  simp_rw [card_covMask val p free _ (fun j => h3 _ j) h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  simp_rw [compat_iff]
  by_cases hf : FreeOk free u
  · simp only [hf, true_and, if_true]
    rw [← sum_filter, sum_const, nsmul_eq_mul, M1]
    ring
  · simp [hf]
theorem sum_card_covMask_pair (p : ℕ) (h3 : ∀ x j, val x j ≤ 4) :
    ∑ ab : β × β, (#{E : Fin p → β | CovMask val (fun _ => false) (fun j => max (val ab.1 j) (val ab.2 j)) E} : ℤ) =
      ∑ u : Fin 6 → Fin 6, sgnU u * (M2 val u : ℤ) * (cntU val u : ℤ) ^ p := by
  simp_rw [card_covMask val p (fun _ => false) _ (fun j => max_le (h3 _ j) (h3 _ j)) h3]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  have hfree : FreeOk (fun _ => false) u := fun j hj => absurd hj (by simp)
  simp_rw [compat_iff, hfree, true_and]
  rw [← sum_filter, sum_const, nsmul_eq_mul, M2]
  ring
omit [Fintype β] in
theorem coversT_max' {p : ℕ} (v₁ v₂ : Fin 6 → ℕ) (E : Fin p → β) :
    CoversT val (fun i => max (v₁ i) (v₂ i)) E ↔ CoversT val v₁ E ∧ CoversT val v₂ E := by
  unfold CoversT
  constructor
  · intro h
    exact ⟨fun i => (h i).imp fun m hm => le_trans (le_max_left _ _) hm,
      fun i => (h i).imp fun m hm => le_trans (le_max_right _ _) hm⟩
  · rintro ⟨h₁, h₂⟩ i
    rcases le_total (v₁ i) (v₂ i) with hle | hle
    · obtain ⟨m, hm⟩ := h₂ i
      exact ⟨m, max_le (hle.trans hm) hm⟩
    · obtain ⟨m, hm⟩ := h₁ i
      exact ⟨m, max_le hm (hle.trans hm)⟩
omit [Fintype β] in
theorem covMask_false_iff {p : ℕ} (v : Fin 6 → ℕ) (E : Fin p → β) :
    CovMask val (fun _ => false) v E ↔ CoversT val v E := by
  unfold CovMask CoversT
  simp
omit [Fintype β] in
theorem covMask_free_iff {p : ℕ} (i : Fin 6) (v : Fin 6 → ℕ) (E : Fin p → β) :
    CovMask val (fun j => decide (j = i)) v E ↔ CoversExcept val i v E := by
  unfold CovMask CoversExcept
  simp
end IE
section Bridge
variable {β : Type*} [Fintype β] (val : β → Fin 6 → ℕ)
def WordsOf : Prop := (Finset.univ.val.map fun x => List.ofFn (val x)) = (words : Multiset (List ℕ))
theorem countP_words {val : β → Fin 6 → ℕ} (hW : WordsOf val) (q : List ℕ → Bool) :
    words.countP q = #{x : β | q (List.ofFn (val x)) = true} := by
  have h : words.countP q = Multiset.countP (fun l => q l = true) (words : Multiset (List ℕ)) := by
    rw [Multiset.coe_countP]; simp
  rw [h, ← hW, Multiset.countP_map]
  rfl
theorem digitsOf_succ {n : ℕ} (u : Fin (n + 1) → Fin 6) : digitsOf u = (u 0 : ℕ) :: digitsOf (Fin.tail u) := by
  simp [digitsOf, List.ofFn_succ, Fin.tail]
theorem ltB_ofFn_iff : ∀ {n : ℕ} (f : Fin n → ℕ) (u : Fin n → Fin 6),
    ltB (List.ofFn f) (digitsOf u) = true ↔ ∀ j, f j < u j
  | 0, _, _ => by simp [digitsOf, ltB]
  | n + 1, f, u => by
    rw [List.ofFn_succ, digitsOf_succ u, ltB_cons, Bool.and_eq_true, decide_eq_true_iff,
      ltB_ofFn_iff (fun j => f j.succ) (Fin.tail u), Fin.forall_fin_succ]
    rfl
theorem mtB_ofFn_iff : ∀ {n : ℕ} (f : Fin n → ℕ) (u : Fin n → Fin 6),
    mtB (List.ofFn f) (digitsOf u) = true ↔ ∀ j, u j ≠ 5 → f j = u j
  | 0, _, _ => by simp [digitsOf, mtB]
  | n + 1, f, u => by
    rw [List.ofFn_succ, digitsOf_succ u, mtB_cons, Bool.and_eq_true,
      mtB_ofFn_iff (fun j => f j.succ) (Fin.tail u), Fin.forall_fin_succ]
    have h4 : ((u 0 : ℕ) = 5) ↔ u 0 = 5 := by rw [Fin.ext_iff]; rfl
    simp only [Bool.or_eq_true, beq_iff_eq, h4, Fin.tail]
    constructor
    · rintro ⟨h0 | h0, h⟩
      · exact ⟨fun h' => absurd h0 h', h⟩
      · exact ⟨fun _ => h0, h⟩
    · rintro ⟨h0, h⟩
      refine ⟨?_, h⟩
      by_cases hu : u 0 = 5
      · exact Or.inl hu
      · exact Or.inr (h0 hu)
theorem words_length : ∀ p ∈ words, p.length = 6 := by decide +kernel
theorem cntT_eq {val : β → Fin 6 → ℕ} (hW : WordsOf val) (u : Fin 6 → Fin 6) :
    lookup cntT (digitsOf u) = cntU val u := by
  rw [cntT, lookup_cnt 6 words words_length _ (digitsOf_length u) (digitsOf_le u), countP_words hW, cntU]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  exact ltB_ofFn_iff _ u
theorem lookup_cntT {val : β → Fin 6 → ℕ} (hW : WordsOf val) (l : List ℕ) (hl : l.length = 6)
    (hv : ∀ v ∈ l, v ≤ 5) : lookup cntT l = #{x : β | ltB (List.ofFn (val x)) l} := by
  rw [cntT, lookup_cnt 6 words words_length l hl hv, countP_words hW]
theorem full_cntT : Full 6 cntT := full_pT 6 _ (full_indT 6 _)
theorem g1T_eq {val : β → Fin 6 → ℕ} (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 4) (u : Fin 6 → Fin 6) :
    lookup g1T (digitsOf u) = M1 val u := by
  rw [g1T, lookup_dT 6 univ (fun x => List.ofFn (val x)) cntT full_cntT
    (fun x _ => ⟨List.length_ofFn, fun v hv => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv; exact h3 x j⟩)
    (fun l hl hv => lookup_cntT hW l hl hv) _ (digitsOf_length u) (digitsOf_le u), M1]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  exact mtB_ofFn_iff _ u
theorem ltB_max (p q l : List ℕ) (hp : p.length = l.length) (hq : q.length = l.length) :
    ltB (List.zipWith max p q) l = (ltB p l && ltB q l) := by
  induction l generalizing p q with
  | nil =>
    rw [List.length_eq_zero_iff.mp (show p.length = 0 by simpa using hp),
      List.length_eq_zero_iff.mp (show q.length = 0 by simpa using hq)]
    rfl
  | cons b l ih =>
    rcases p with _ | ⟨a, p⟩
    · simp at hp
    rcases q with _ | ⟨c, q⟩
    · simp at hq
    simp only [List.zipWith_cons_cons, ltB_cons]
    rw [ih p q (by simpa using hp) (by simpa using hq)]
    rw [show decide (max a c < b) = (decide (a < b) && decide (c < b)) by simp]
    cases decide (a < b) <;> cases decide (c < b) <;> cases ltB p l <;> cases ltB q l <;> rfl
theorem ofFn_max (f g : Fin 6 → ℕ) :
    List.ofFn (fun j => max (f j) (g j)) = List.zipWith max (List.ofFn f) (List.ofFn g) := by
  apply List.ext_getElem <;> simp
theorem g2T_eq {val : β → Fin 6 → ℕ} (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 4) (u : Fin 6 → Fin 6) :
    lookup g2T (digitsOf u) = M2 val u := by
  have hsq : ∀ l : List ℕ, l.length = 6 → (∀ v ∈ l, v ≤ 5) →
      lookup (mapT (fun z => Nat.mul z z) cntT) l =
        #{ab ∈ (univ : Finset (β × β)) | ltB (List.ofFn fun j => max (val ab.1 j) (val ab.2 j)) l} := by
    intro l hl hv
    rw [lookup_mapT _ 6 cntT l full_cntT hl, lookup_cntT hW l hl hv, Nat.mul_eq, ← card_product,
      ← Finset.filter_product, Finset.univ_product_univ]
    congr 1
    refine Finset.filter_congr fun ab _ => ?_
    rw [ofFn_max, ltB_max _ _ _ (by simp [hl]) (by simp [hl])]
    simp
  rw [g2T, lookup_dT 6 univ (fun ab : β × β => List.ofFn fun j => max (val ab.1 j) (val ab.2 j)) _
    (full_mapT _ 6 cntT full_cntT)
    (fun ab _ => ⟨List.length_ofFn, fun v hv => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv; exact max_le (h3 _ j) (h3 _ j)⟩)
    hsq _ (digitsOf_length u) (digitsOf_le u), M2]
  congr 1
  refine Finset.filter_congr fun ab _ => ?_
  exact mtB_ofFn_iff _ u
end Bridge
section Decode
variable {β : Type*} [Fintype β] {val : β → Fin 6 → ℕ}
theorem frOk_iff_freeOk (fr : List Bool) (free : Fin 6 → Bool) (hfr : ∀ j : Fin 6, fr.getD j false = free j)
    (u : Fin 6 → Fin 6) : FrOk fr u ↔ FreeOk free u := by
  unfold FrOk FreeOk
  simp only [hfr]
theorem sgnU_eq (u : Fin 6 → Fin 6) : sgnU u = if parU u then -1 else 1 := by
  rw [sgnU, parU, ClaudeWCT.Numerics.WCT9.neg_one_pow_eq]
theorem decode_hist (fr : List Bool) (hfr : fr.length = 6) (g : T6) (hg : Full 6 g) (d : List (ℕ × ℤ))
    (hEq : Kernel.histEq (histT Kernel.HB cntT fr g false) d = true)
    (hMass : Kernel.massOk (histT 1 cntT fr g false) d = true) (p : ℕ) :
    ∑ u : Fin 6 → Fin 6, (if FrOk fr u then (if parU u then (-1 : ℤ) else 1) * (lookup g (digitsOf u) : ℤ) *
        ((lookup cntT (digitsOf u) : ℕ) : ℤ) ^ p else 0) =
      (d.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  rw [histT_eq _ 6 cntT g fr false full_cntT hg hfr] at hEq hMass
  simp only [Bool.false_xor] at hEq hMass
  exact Kernel.decode univ (FrOk fr) parU (fun u => lookup g (digitsOf u)) (fun u => lookup cntT (digitsOf u)) d
    hEq hMass p
end Decode
section Tables
variable {β : Type*} [Fintype β] {val : β → Fin 6 → ℕ}
theorem checks_w1 : w1Check = true ∧ w1MassCheck = true := by
  have h := w1_group0
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩
theorem checks_wf : ∀ t : Fin 6, wfCheck t = true ∧ wfMassCheck t = true := by
  have h0 := w1_group0
  have h1 := w1_group1
  have h2 := w1_group2
  have h3 := w1_group3
  simp only [Bool.and_eq_true] at h0 h1 h2 h3
  intro t
  fin_cases t
  · exact ⟨h0.1.2, h0.2⟩
  · exact ⟨h1.1.1.1, h1.1.1.2⟩
  · exact ⟨h1.1.2, h1.2⟩
  · exact ⟨h2.1.1.1, h2.1.1.2⟩
  · exact ⟨h2.1.2, h2.2⟩
  · exact h3
theorem checks_w2 : w2Check = true ∧ w2MassCheck = true := by
  have h := w2_all
  simp only [Bool.and_eq_true] at h
  exact h
theorem full_g1T : Full 6 g1T := full_dT 6 _ full_cntT
theorem full_g2T : Full 6 g2T := full_dT 6 _ (full_mapT _ 6 _ full_cntT)
theorem w1_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 4) (p : ℕ) :
    (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) = (w1Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × (Fin p → β) | CoversT val (val x.1) x.2} : ℤ) =
      ∑ a : β, (#{E : Fin p → β | CovMask val (fun _ => false) (val a) E} : ℤ) := by
    rw [natCast_card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [natCast_card_filter]
    simp only [covMask_false_iff]
  rw [hcard, sum_card_covMask val p _ h3,
    ← decode_hist noFree rfl g1T full_g1T w1Data checks_w1.1 checks_w1.2 p]
  refine sum_congr rfl fun u _ => ?_
  refine if_congr (frOk_iff_freeOk noFree (fun _ => false) (fun j => by fin_cases j <;> rfl) u).symm ?_ rfl
  rw [g1T_eq hW h3, cntT_eq hW, sgnU_eq]
theorem wf_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 4) (i : Fin 6) (p : ℕ) :
    (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
      ((wfData i).map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × (Fin p → β) | CoversExcept val i (val x.1) x.2} : ℤ) =
      ∑ a : β, (#{E : Fin p → β | CovMask val (fun j => decide (j = i)) (val a) E} : ℤ) := by
    rw [natCast_card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [natCast_card_filter]
    simp only [covMask_free_iff]
  rw [hcard, sum_card_covMask val p _ h3,
    ← decode_hist (freeList i) rfl g1T full_g1T (wfData i) (checks_wf i).1 (checks_wf i).2 p]
  refine sum_congr rfl fun u _ => ?_
  refine if_congr (frOk_iff_freeOk (freeList i) (fun j => decide (j = i)) (fun j => by
      fin_cases i <;> fin_cases j <;> rfl) u).symm ?_ rfl
  rw [g1T_eq hW h3, cntT_eq hW, sgnU_eq]
theorem w2_table (hW : WordsOf val) (h3 : ∀ x j, val x j ≤ 4) (p : ℕ) :
    (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      (w2Data.map fun e => e.2 * (e.1 : ℤ) ^ p).sum := by
  have hcard : (#{x : β × β × (Fin p → β) | CoversT val (val x.1) x.2.2 ∧ CoversT val (val x.2.1) x.2.2} : ℤ) =
      ∑ ab : β × β, (#{E : Fin p → β |
        CovMask val (fun _ => false) (fun j => max (val ab.1 j) (val ab.2 j)) E} : ℤ) := by
    rw [natCast_card_filter, ← (Equiv.prodAssoc β β (Fin p → β)).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun ab _ => ?_
    rw [natCast_card_filter]
    refine sum_congr rfl fun E _ => ?_
    simp only [Equiv.prodAssoc_apply, covMask_false_iff, coversT_max']
  rw [hcard, sum_card_covMask_pair val p h3,
    ← decode_hist noFree rfl g2T full_g2T w2Data checks_w2.1 checks_w2.2 p]
  refine sum_congr rfl fun u _ => ?_
  have hok : FrOk noFree u := (frOk_iff_freeOk noFree (fun _ => false) (fun j => by fin_cases j <;> rfl) u).mpr
    (fun j hj => absurd hj (by simp))
  rw [if_pos hok, g2T_eq hW h3, cntT_eq hW, sgnU_eq]
end Tables
end ClaudeWCT.Numerics.N600
end
end
-- ==== merged from ClaudeWCT_Numerics_CoverageHistogramWork ====
section

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.Numerics.N600
open Finset
variable {β : Type*} [Fintype β]

def maxWord (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) (i : Fin 6) : ℕ :=
  Finset.univ.sup fun k => val (E k) i

theorem maxWord_le (val : β → Fin 6 → ℕ) (h4 : ∀ x i, val x i ≤ 4)
    {j : ℕ} (E : Fin j → β) (i : Fin 6) : maxWord val E i ≤ 4 := by
  exact Finset.sup_le fun k _ => h4 (E k) i

theorem maxWord_lt_iff (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j)
    (E : Fin j → β) (i : Fin 6) (a : ℕ) : maxWord val E i < a ↔ ∀ k, val (E k) i < a := by
  constructor
  · intro h k
    exact lt_of_le_of_lt (Finset.le_sup (f := fun k => val (E k) i) (Finset.mem_univ k)) h
  · intro h
    have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (h ⟨0, hj⟩)
    exact (Finset.sup_lt_iff ha).mpr (fun k _ => h k)

theorem maxWord_cdf (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 6) :
    #{E : Fin j → β | ∀ i, maxWord val E i < u i} = (cntU val u) ^ j := by
  classical
  have hset : ({E : Fin j → β | ∀ i, maxWord val E i < u i} : Finset (Fin j → β)) =
      Fintype.piFinset (fun _ : Fin j => {x : β | ∀ i, val x i < u i}) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    simp only [maxWord_lt_iff val hj]
    exact forall_comm
  rw [hset, Fintype.card_piFinset_const]
  rfl

noncomputable def maxCountTree (j : ℕ) : T6 := dT (mapT (fun z => z ^ j) cntT)

theorem maxCountTree_eq (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 6) :
    lookup (maxCountTree j) (digitsOf u) =
      #{E : Fin j → β | ∀ i, u i ≠ 5 → maxWord val E i = u i} := by
  classical
  have hcdf : ∀ l : List ℕ, l.length = 6 → (∀ v ∈ l, v ≤ 5) →
      lookup (mapT (fun z => z ^ j) cntT) l =
        #{E : Fin j → β | ltB (List.ofFn (maxWord val E)) l} := by
    intro l hl hv
    let u' : Fin 6 → Fin 6 := fun i => ⟨l[i.val]'(by omega), Nat.lt_succ_of_le (hv _ (List.getElem_mem _))⟩
    have he : digitsOf u' = l := by
      apply List.ext_getElem
      · simp [digitsOf, hl]
      · intro i hi hi'
        simp only [digitsOf, List.getElem_ofFn]
        rfl
    rw [← he, lookup_mapT _ 6 cntT _ full_cntT (digitsOf_length u'), cntT_eq hW]
    rw [← maxWord_cdf val hj u']
    congr 1
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ltB_ofFn_iff _ u').symm
  rw [maxCountTree, lookup_dT 6 univ (fun E : Fin j → β => List.ofFn (maxWord val E)) _
    (full_mapT _ 6 cntT full_cntT)
    (fun E _ => ⟨List.length_ofFn, fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact maxWord_le val h4 E i⟩)
    hcdf _ (digitsOf_length u) (digitsOf_le u)]
  congr 1
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mtB_ofFn_iff _ u

noncomputable def coverCount (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) : ℕ :=
  #{x : β | ∀ i, val x i ≤ maxWord val E i}

def gridUp {n : ℕ} (u : Fin n → Fin 5) : Fin n → Fin 6 := fun i => ⟨(u i).val + 1, by omega⟩
def gridCast {n : ℕ} (u : Fin n → Fin 5) : Fin n → Fin 6 := fun i => ⟨(u i).val, by omega⟩
noncomputable def gridCoverage (u : Fin 6 → Fin 5) : ℕ := lookup cntT (digitsOf (gridUp u))
noncomputable def coverageHistogram (j a : ℕ) : ℕ :=
  ∑ u : Fin 6 → Fin 5, if gridCoverage u = a then lookup (maxCountTree j) (digitsOf (gridCast u)) else 0

noncomputable def maxGrid (val : β → Fin 6 → ℕ) (h4 : ∀ x i, val x i ≤ 4)
    {j : ℕ} (E : Fin j → β) : Fin 6 → Fin 5 := fun i => ⟨maxWord val E i, Nat.lt_succ_of_le (maxWord_le val h4 E i)⟩

theorem coverCount_grid (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (E : Fin j → β) :
    coverCount val E = gridCoverage (maxGrid val h4 E) := by
  classical
  rw [gridCoverage, cntT_eq hW, cntU, coverCount]
  congr 1
  ext x
  simp [gridUp, maxGrid, Nat.lt_succ_iff]

theorem maxGrid_fiber (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (u : Fin 6 → Fin 5) :
    #{E : Fin j → β | maxGrid val h4 E = u} = lookup (maxCountTree j) (digitsOf (gridCast u)) := by
  classical
  rw [maxCountTree_eq val hW h4 hj]
  congr 1
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have H : ∀ i, gridCast u i ≠ 5 := by
    intro i
    intro h
    have := congrArg Fin.val h
    have := (u i).isLt
    simp [gridCast] at *
    omega
  constructor
  · intro h i _
    exact congrArg Fin.val (congrFun h i)
  · intro h
    funext i
    apply Fin.ext
    exact h i (H i)

theorem coverageHistogram_eq (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) (a : ℕ) :
    #{E : Fin j → β | coverCount val E = a} = coverageHistogram j a := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := maxGrid val h4)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _), coverageHistogram]
  apply Finset.sum_congr rfl
  intro u _
  by_cases ha : gridCoverage u = a
  · rw [if_pos ha, ← maxGrid_fiber val hW h4 hj u]
    congr 1
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [coverCount_grid val hW h4, h, ha], h⟩
  · rw [if_neg ha]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro E h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    apply ha
    rw [← h.2, ← coverCount_grid val hW h4]
    exact h.1

noncomputable def maxHistT (hb : ℕ) (c : T6) : T6 → ℕ :=
  T6.rec (motive := fun _ => T6 → ℕ)
    (fun cv g => T6.casesOn g (fun gv => gv * hb ^ cv) (fun _ _ _ _ _ _ => 0))
    (fun _ _ _ _ _ _ _ r1 r2 r3 r4 r5 g => T6.casesOn g (fun _ => 0)
      (fun g0 g1 g2 g3 g4 _ => r1 g0 + r2 g1 + r3 g2 + r4 g3 + r5 g4)) c

theorem maxHistT_leaf (hb cv gv : ℕ) : maxHistT hb (.leaf cv) (.leaf gv) = gv * hb ^ cv := rfl

theorem maxHistT_node (hb : ℕ) (c0 c1 c2 c3 c4 c5 g0 g1 g2 g3 g4 g5 : T6) :
    maxHistT hb (.node c0 c1 c2 c3 c4 c5) (.node g0 g1 g2 g3 g4 g5) =
      maxHistT hb c1 g0 + maxHistT hb c2 g1 + maxHistT hb c3 g2 + maxHistT hb c4 g3 + maxHistT hb c5 g4 := rfl

theorem sum_fin5_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → Fin 5) → M) :
    ∑ u, F u = ∑ t : Fin 5, ∑ u : Fin n → Fin 5, F (Fin.cons t u) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  rfl

theorem gridCast_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    gridCast (Fin.cons t u) = Fin.cons ⟨t.val, by omega⟩ (gridCast u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem gridUp_cons {n : ℕ} (t : Fin 5) (u : Fin n → Fin 5) :
    gridUp (Fin.cons t u) = Fin.cons ⟨t.val + 1, by omega⟩ (gridUp u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem maxHistT_eq (hb : ℕ) : ∀ n c g, Full n c → Full n g →
    maxHistT hb c g = ∑ u : Fin n → Fin 5,
      lookup g (digitsOf (gridCast u)) * hb ^ lookup c (digitsOf (gridUp u))
  | 0, .leaf cv, .leaf gv, _, _ => by
    rw [maxHistT_leaf, Fintype.sum_unique]
    rfl
  | n + 1, .node c0 c1 c2 c3 c4 c5, .node g0 g1 g2 g3 g4 g5, hc, hg => by
    have e0 := maxHistT_eq hb n c1 g0 hc.2.1 hg.1
    have e1 := maxHistT_eq hb n c2 g1 hc.2.2.1 hg.2.1
    have e2 := maxHistT_eq hb n c3 g2 hc.2.2.2.1 hg.2.2.1
    have e3 := maxHistT_eq hb n c4 g3 hc.2.2.2.2.1 hg.2.2.2.1
    have e4 := maxHistT_eq hb n c5 g4 hc.2.2.2.2.2 hg.2.2.2.2.1
    rw [sum_fin5_cons, Fin.sum_univ_five, maxHistT_node, e0, e1, e2, e3, e4]
    simp only [gridCast_cons, gridUp_cons, digitsOf_cons, lookup_node_cons]
    rfl

noncomputable def coveragePacked (hb j : ℕ) : ℕ := maxHistT hb cntT (maxCountTree j)

theorem coveragePacked_eq (hb j : ℕ) : coveragePacked hb j =
    ∑ u : Fin 6 → Fin 5,
      lookup (maxCountTree j) (digitsOf (gridCast u)) * hb ^ gridCoverage u := by
  exact maxHistT_eq hb 6 cntT (maxCountTree j) full_cntT
    (full_dT 6 _ (full_mapT _ 6 cntT full_cntT))

open ClaudeWCT.Numerics
noncomputable def coveredTargets (val : β → Fin 6 → ℕ) {j : ℕ} (E : Fin j → β) : ℕ :=
  #{x : β | CoversT val (val x) E}

theorem coversT_maxWord (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j)
    (E : Fin j → β) (v : Fin 6 → ℕ) : CoversT val v E ↔ ∀ i, v i ≤ maxWord val E i := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h i
    exact le_trans hk (Finset.le_sup (f := fun k => val (E k) i) (Finset.mem_univ k))
  · intro h i
    have hs : (Finset.univ : Finset (Fin j)).Nonempty := ⟨⟨0, hj⟩, Finset.mem_univ _⟩
    obtain ⟨k, _, hk⟩ := Finset.sup_mem_of_nonempty (f := fun k => val (E k) i) hs
    change val (E k) i = maxWord val E i at hk
    exact ⟨k, (h i).trans_eq hk.symm⟩

theorem coveredTargets_pos (val : β → Fin 6 → ℕ) {j : ℕ} (hj : 0 < j) (E : Fin j → β) :
    coveredTargets val E = coverCount val E := by
  classical
  unfold coveredTargets coverCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, coversT_maxWord val hj]

theorem coveredTargets_zero (val : β → Fin 6 → ℕ) (E : Fin 0 → β) : coveredTargets val E = 0 := by
  classical
  unfold coveredTargets
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x h
  obtain ⟨i, _⟩ := (Finset.mem_filter.mp h).2 0
  exact i.elim0

noncomputable def coverageLaw (j a : ℕ) : ℕ := if j = 0 then if a = 0 then 1 else 0 else coverageHistogram j a

def FullCoverageHistogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) : Prop :=
  ∀ j a, #{E : Fin j → β | coveredTargets val E = a} = H j a

theorem coverageLaw_correct (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) : FullCoverageHistogram val coverageLaw := by
  intro j a
  classical
  cases j with
  | zero =>
    by_cases ha : a = 0
    · subst a; simp [coverageLaw, coveredTargets_zero]
    · simp [coverageLaw, coveredTargets_zero, ha, Ne.symm ha]
  | succ j =>
    simp only [coverageLaw, Nat.succ_ne_zero, if_false]
    simp_rw [coveredTargets_pos val (Nat.succ_pos j)]
    exact coverageHistogram_eq val hW h4 (Nat.succ_pos j) a

section Occupancy
variable {C : Type*} [Fintype C] [DecidableEq C] {r : ℕ}
noncomputable def fiberIndex (o : Fin r → C) (c : C) : {i : Fin r // o i = c} ≃ Fin (occ o c) :=
  Fintype.equivFinOfCardEq (by simp [occ, Fintype.card_subtype])

noncomputable def splitRanks (o : Fin r → C) : (Fin r → β) ≃ ((c : C) → Fin (occ o c) → β) :=
  Equiv.piCongrFiberwise (fun c => Equiv.piCongrLeft (fun _ => β) (fiberIndex o c))

noncomputable def childCoverage (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) (c : C) : ℕ :=
  coveredTargets val (splitRanks o R c)

theorem childCoverage_histogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (o : Fin r → C) (a : C → ℕ) :
    #{R : Fin r → β | ∀ c, childCoverage val o R c = a c} = ∏ c, H (occ o c) (a c) := by
  classical
  have he : #{R : Fin r → β | ∀ c, childCoverage val o R c = a c} =
      #{S : (c : C) → Fin (occ o c) → β | ∀ c, coveredTargets val (S c) = a c} := by
    refine Finset.card_bij (fun R _ => splitRanks o R) ?_ ?_ ?_
    · intro R hR
      have hp := (Finset.mem_filter.mp hR).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · intro R hR S hS heq
      exact (splitRanks o).injective heq
    · intro S hS
      refine ⟨(splitRanks o).symm S, ?_, (splitRanks o).apply_symm_apply S⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro c
      change coveredTargets val ((splitRanks o) ((splitRanks o).symm S) c) = a c
      rw [Equiv.apply_symm_apply]
      exact (Finset.mem_filter.mp hS).2 c
  rw [he]
  have hs : ({S : (c : C) → Fin (occ o c) → β | ∀ c, coveredTargets val (S c) = a c} : Finset _) =
      Fintype.piFinset (fun c => {R : Fin (occ o c) → β | coveredTargets val R = a c}) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hs, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro c _
  exact hH (occ o c) (a c)

theorem splitRanks_apply (o : Fin r → C) (R : Fin r → β) (c : C) (k : Fin (occ o c)) :
    splitRanks o R c k = R ((fiberIndex o c).symm k).val := by
  simp [splitRanks, Equiv.piCongrLeft_apply]

theorem coversT_splitRanks (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β)
    (c : C) (v : Fin 6 → ℕ) :
    CoversT val v (splitRanks o R c) ↔ Thinning.CovAt val c v (fun i => (o i, R i)) := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h i
    let z := (fiberIndex o c).symm k
    exact ⟨z.val, z.property, by simpa only [splitRanks_apply] using hk⟩
  · intro h i
    obtain ⟨k, hk, hv⟩ := h i
    refine ⟨fiberIndex o c ⟨k, hk⟩, ?_⟩
    simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hv

theorem childCoverage_le (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) (c : C) :
    childCoverage val o R c ≤ Fintype.card β := Finset.card_filter_le _ _

noncomputable def childCoverageFin (val : β → Fin 6 → ℕ) (o : Fin r → C) (R : Fin r → β) :
    C → Fin (Fintype.card β + 1) := fun c =>
  ⟨childCoverage val o R c, Nat.lt_succ_of_le (childCoverage_le val o R c)⟩

theorem childCoverageFin_histogram (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (o : Fin r → C) (a : C → Fin (Fintype.card β + 1)) :
    #{R : Fin r → β | childCoverageFin val o R = a} = ∏ c, H (occ o c) (a c) := by
  classical
  rw [← childCoverage_histogram val H hH o (fun c => (a c).val)]
  congr 1
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff, childCoverageFin]

theorem sum_childCoverage {M : Type*} [AddCommMonoid M]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (o : Fin r → C) (F : (C → Fin (Fintype.card β + 1)) → M) :
    ∑ R : Fin r → β, F (childCoverageFin val o R) =
      ∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (occ o c) (a c)) • F a := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := childCoverageFin val o)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro a _
  rw [sum_congr rfl (g := fun _ => F a) (fun R hR => by rw [(mem_filter.mp hR).2]), sum_const,
    childCoverageFin_histogram val H hH o a]

theorem sum_occupancy_coverage {M : Type*} [AddCommMonoid M]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (F : (C → ℕ) → (C → Fin (Fintype.card β + 1)) → M) :
    ∑ o : Fin r → C, ∑ R : Fin r → β, F (occ o) (childCoverageFin val o R) =
      ∑ k ∈ piAntidiag univ r, Nat.multinomial univ k •
        (∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (k c) (a c)) • F k a) := by
  classical
  calc
    _ = ∑ o : Fin r → C, ∑ a : C → Fin (Fintype.card β + 1),
        (∏ c, H (occ o c) (a c)) • F (occ o) a :=
      sum_congr rfl fun o _ => sum_childCoverage val H hH o (F (occ o))
    _ = _ := sum_occ (α := C) (n := r) (M := M) (fun k =>
      ∑ a : C → Fin (Fintype.card β + 1), (∏ c, H (k c) (a c)) • F k a)
end Occupancy

section Profiles
open ClaudeWCT.Numerics

theorem sum_piAntidiag_bounded {M : Type*} [AddCommMonoid M] (n r : ℕ) (F : (Fin n → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ u : Fin n → Fin (r + 1), if (∑ i, (u i).val) = r then F (fun i => (u i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => fun i => (u i).val) ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_piAntidiag]
    exact ⟨(Finset.mem_filter.mp hu).2, fun i _ => Finset.mem_univ i⟩
  · intro u hu v hv h
    funext i
    apply Fin.ext
    exact congrFun h i
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hb : ∀ i, k i < r + 1 := by
      intro i
      have hi : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
      simpa only [hsum] using Nat.lt_succ_of_le hi
    refine ⟨fun i => ⟨k i, hb i⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩
  · intro u hu
    rfl

theorem occupancy_profile_sum {R : Type*} [CommSemiring R] (n r : ℕ) (P : ℕ → R) :
    (∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
      (Nat.multinomial univ k : R) * ∏ i, P (k i)) =
      ∑ m ∈ piAntidiag (univ : Finset (Fin (r + 1))) n,
        if (∑ a, m a * a.val) = r then
          (Nat.multinomial univ m : R) *
            (r.factorial / (∏ a : Fin (r + 1), a.val.factorial ^ m a) : ℕ) *
              ∏ a : Fin (r + 1), P a.val ^ m a
        else 0 := by
  classical
  rw [sum_piAntidiag_bounded n r]
  let Ψ : (Fin (r + 1) → ℕ) → R := fun m =>
    if (∑ a, m a * a.val) = r then
      (r.factorial / (∏ a : Fin (r + 1), a.val.factorial ^ m a) : ℕ) *
        ∏ a : Fin (r + 1), P a.val ^ m a
    else 0
  have ht : ∀ u : Fin n → Fin (r + 1),
      (if (∑ i, (u i).val) = r then
        (Nat.multinomial univ (fun i => (u i).val) : R) * ∏ i, P (u i).val else 0) = Ψ (occ u) := by
    intro u
    dsimp [Ψ]
    rw [← sum_eq_sum_mul_occ (fun a : Fin (r + 1) => a.val) u]
    by_cases hs : (∑ i, (u i).val) = r
    · rw [if_pos hs, if_pos hs, Nat.multinomial, hs,
        prod_eq_prod_pow_occ (fun a : Fin (r + 1) => a.val.factorial) u,
        prod_eq_prod_pow_occ (fun a : Fin (r + 1) => P a.val) u]
    · rw [if_neg hs, if_neg hs]
  rw [Finset.sum_congr rfl (fun u _ => ht u), sum_occ Ψ]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [Ψ]
  by_cases hs : (∑ a, m a * a.val) = r
  · rw [if_pos hs, if_pos hs]
    simp only [nsmul_eq_mul, Nat.cast_id, mul_assoc]
  · rw [if_neg hs, if_neg hs, smul_zero]
end Profiles

section HistogramReflection
open Polynomial
noncomputable def coveragePoly (j : ℕ) : ℕ[X] :=
  ∑ u : Fin 6 → Fin 5,
    Polynomial.C (lookup (maxCountTree j) (digitsOf (gridCast u))) * Polynomial.X ^ gridCoverage u

noncomputable def naturalDataPoly (d : List (ℕ × ℕ)) : ℕ[X] :=
  (d.map fun e => Polynomial.C e.2 * Polynomial.X ^ e.1).sum

theorem coveragePoly_eval (hb j : ℕ) : (coveragePoly j).eval hb = coveragePacked hb j := by
  simp only [coveragePoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, coveragePacked_eq]

theorem coveragePoly_coeff (j a : ℕ) : (coveragePoly j).coeff a = coverageHistogram j a := by
  simp only [coveragePoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    coverageHistogram, eq_comm]

theorem coveragePacked_mass (val : β → Fin 6 → ℕ) (hW : WordsOf val)
    (h4 : ∀ x i, val x i ≤ 4) {j : ℕ} (hj : 0 < j) :
    coveragePacked 1 j = Fintype.card β ^ j := by
  classical
  rw [coveragePacked_eq]
  simp only [one_pow, mul_one]
  simp_rw [← maxGrid_fiber val hW h4 hj]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

theorem naturalDataPoly_eval (d : List (ℕ × ℕ)) (hb : ℕ) :
    (naturalDataPoly d).eval hb = d.foldr (fun e s => e.2 * hb ^ e.1 + s) 0 := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e d ih => simp [naturalDataPoly, Polynomial.eval_add] at ih ⊢; exact ih

theorem foldl_add_snd (d : List (ℕ × ℕ)) (n : ℕ) :
    d.foldl (fun s e => s + e.2) n = n + (d.map Prod.snd).sum := by
  induction d generalizing n with
  | nil => simp
  | cons e d ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Nat.add_assoc]

theorem naturalDataPoly_coeff (d : List (ℕ × ℕ)) (a : ℕ) :
    (naturalDataPoly d).coeff a = (d.filter (fun e => e.1 == a)).foldl (fun s e => s + e.2) 0 := by
  rw [foldl_add_snd, zero_add]
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e d ih =>
    by_cases he : e.1 = a
    · simp [naturalDataPoly, Polynomial.coeff_C_mul_X_pow, he] at ih ⊢
      exact ih
    · simp [naturalDataPoly, Polynomial.coeff_C_mul_X_pow, he, Ne.symm he] at ih ⊢
      exact ih

theorem coverageHistogram_of_packed (j : ℕ)
    (hpacked : coveragePacked (2 ^ 128) j = coverageHPack (2 ^ 128) j)
    (hmass : coveragePacked 1 j < 2 ^ 127)
    (hdmass : coverageHPack 1 j < 2 ^ 127) (a : ℕ) :
    coverageHistogram j a = coverageHAt j a := by
  have hEval : (coveragePoly j).eval (2 ^ 128) = (naturalDataPoly (coverageHData j)).eval (2 ^ 128) := by
    rw [coveragePoly_eval, naturalDataPoly_eval]
    exact hpacked
  have hpol : coveragePoly j = naturalDataPoly (coverageHData j) :=
    ClaudeWCT.Numerics.eq_of_eval_eq (by norm_num [Kernel.HB]) (fun k => Kernel.coeff_lt_of_eval_one (by
      rw [coveragePoly_eval]; exact hmass) k) (fun k => Kernel.coeff_lt_of_eval_one (by
      rw [naturalDataPoly_eval]; exact hdmass) k) hEval
  rw [← coveragePoly_coeff, hpol, naturalDataPoly_coeff]
  rfl
end HistogramReflection

section CoordinateLaw
variable {C : Type*} [Fintype C] [DecidableEq C] {r : ℕ}

noncomputable def atChildCoverage (val : β → Fin 6 → ℕ) (E : Fin r → C × β) (c : C) : ℕ :=
  #{x : β | Thinning.CovAt val c (val x) E}

noncomputable def coordinateCoverage (val : β → Fin 6 → ℕ) (E : Fin r → C × β) : ℕ :=
  #{x : C × β | Thinning.CovAt val x.1 (val x.2) E}

theorem coordinateCoverage_sum (val : β → Fin 6 → ℕ) (E : Fin r → C × β) :
    coordinateCoverage val E = ∑ c, atChildCoverage val E c := by
  classical
  unfold coordinateCoverage atChildCoverage
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro c _
  rw [Finset.card_filter]

noncomputable def colorWordEquiv (e : C ≃ C) : (Fin r → C × β) ≃ (Fin r → C × β) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr e (Equiv.refl β))

theorem covAt_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β)
    (c : C) (v : Fin 6 → ℕ) :
    Thinning.CovAt val c v (colorWordEquiv e E) ↔ Thinning.CovAt val (e.symm c) v E := by
  unfold Thinning.CovAt
  apply forall_congr'
  intro i
  apply exists_congr
  intro k
  change (e (E k).1 = c ∧ v i ≤ val (E k).2 i) ↔ ((E k).1 = e.symm c ∧ v i ≤ val (E k).2 i)
  rw [Equiv.apply_eq_iff_eq_symm_apply]

theorem atChildCoverage_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β) (c : C) :
    atChildCoverage val (colorWordEquiv e E) c = atChildCoverage val E (e.symm c) := by
  classical
  unfold atChildCoverage
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, covAt_colorWord]

theorem coordinateCoverage_colorWord (val : β → Fin 6 → ℕ) (e : C ≃ C) (E : Fin r → C × β) :
    coordinateCoverage val (colorWordEquiv e E) = coordinateCoverage val E := by
  rw [coordinateCoverage_sum, coordinateCoverage_sum]
  simp_rw [atChildCoverage_colorWord]
  exact e.symm.sum_comp _

noncomputable def markedCoverageCount (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a : ℕ) : ℕ :=
  ∑ E : Fin r → C × β, if coordinateCoverage val E = a then atChildCoverage val E c else 0

theorem markedCoverageCount_color (val : β → Fin 6 → ℕ) (r : ℕ) (c d : C) (a : ℕ) :
    markedCoverageCount val r c a = markedCoverageCount val r d a := by
  classical
  have h := (colorWordEquiv (β := β) (r := r) (Equiv.swap c d)).sum_comp
    (fun E => if coordinateCoverage val E = a then atChildCoverage val E d else 0)
  simp only [coordinateCoverage_colorWord, atChildCoverage_colorWord, Equiv.symm_swap, Equiv.swap_apply_right] at h
  exact h

theorem markedCoverageCount_weighted (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a : ℕ) :
    Fintype.card C * markedCoverageCount val r c a =
      a * #{E : Fin r → C × β | coordinateCoverage val E = a} := by
  classical
  calc
    _ = ∑ d : C, markedCoverageCount val r d a := by
      rw [sum_congr rfl (g := fun _ => markedCoverageCount val r c a)
        (fun d _ => markedCoverageCount_color val r d c a), sum_const, card_univ, smul_eq_mul]
    _ = ∑ E : Fin r → C × β, if coordinateCoverage val E = a then coordinateCoverage val E else 0 := by
      unfold markedCoverageCount
      rw [sum_comm]
      apply sum_congr rfl
      intro E _
      by_cases he : coordinateCoverage val E = a
      · simp only [he, if_true, ← coordinateCoverage_sum]
      · simp only [he, if_false, sum_const_zero]
    _ = _ := by
      rw [Finset.card_filter, mul_sum]
      apply sum_congr rfl
      intro E _
      by_cases he : coordinateCoverage val E = a <;> simp [he]

theorem retainedCoverage_weighted (val : β → Fin 6 → ℕ) (r : ℕ) (c : C) (a D : ℕ)
    (hD : D ≤ markedCoverageCount val r c a) :
    Fintype.card C * D ≤ a * #{E : Fin r → C × β | coordinateCoverage val E = a} := by
  rw [← markedCoverageCount_weighted val r c a]
  exact Nat.mul_le_mul_left _ hD
end CoordinateLaw

section ProfileRefinement


theorem multinomial_fin_cons {n : ℕ} (j : ℕ) (k : Fin n → ℕ) :
    Nat.multinomial univ (Fin.cons j k) =
      (j + ∑ i, k i).choose j * Nat.multinomial univ k := by
  rw [Nat.multinomial, Nat.div_eq_iff_eq_mul_left _ (Nat.prod_factorial_dvd_factorial_sum _ _)]
  · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
    rw [Nat.multinomial, mul_assoc, mul_left_comm _ j.factorial,
      Nat.div_mul_cancel (Nat.prod_factorial_dvd_factorial_sum _ _), ← mul_assoc,
      Nat.choose_symm_add, Nat.add_choose_mul_factorial_mul_factorial]
  · positivity

theorem sum_piAntidiag_cons {M : Type*} [AddCommMonoid M] (n r : ℕ)
    (F : (Fin (n+1) → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ j ∈ range (r+1), ∑ k ∈ piAntidiag univ (r-j), F (Fin.cons j k) := by
  classical
  symm
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    have hjr : p.1 ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    rw [Finset.mem_piAntidiag]
    constructor
    · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum] using
        Nat.add_sub_of_le hjr
    · intro i _
      exact Finset.mem_univ i
  · intro p hp q hq he
    have hj : p.1 = q.1 := by simpa using congrFun he 0
    have hk : p.2 = q.2 := by funext i; simpa using congrFun he i.succ
    exact Sigma.ext hj (heq_of_eq hk)
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hs : k 0 + ∑ i : Fin n, k i.succ = r := by simpa [Fin.sum_univ_succ] using hsum
    refine ⟨⟨k 0, fun i : Fin n => k i.succ⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · apply Finset.mem_range.mpr
        change k 0 < r + 1
        omega
      · apply Finset.mem_piAntidiag.mpr
        exact ⟨by change (∑ i : Fin n, k i.succ) = r - k 0; omega, fun i _ => Finset.mem_univ i⟩
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  · intro p hp
    rfl

variable {β C : Type*} [Fintype β] [Fintype C] [DecidableEq C] {r : ℕ}
theorem sum_childCoverage_product {R : Type*} [CommSemiring R]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (o : Fin r → C) (G : C → Fin (Fintype.card β + 1) → R) :
    (∑ B : Fin r → β, ∏ c, G c (childCoverageFin val o B c)) =
      ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (occ o c) a : R) * G c a := by
  classical
  rw [sum_childCoverage val H hH o (fun a => ∏ c, G c (a c)), Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [nsmul_eq_mul, Nat.cast_prod, Finset.prod_mul_distrib]


noncomputable def atChildCoverageFin (val : β → Fin 6 → ℕ) (E : Fin r → C × β) :
    C → Fin (Fintype.card β + 1) := fun c =>
  ⟨atChildCoverage val E c, Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩

theorem childCoverage_pair (val : β → Fin 6 → ℕ) (o : Fin r → C) (B : Fin r → β) (c : C) :
    childCoverage val o B c = atChildCoverage val (fun i => (o i, B i)) c := by
  classical
  unfold childCoverage coveredTargets atChildCoverage
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, coversT_splitRanks]

theorem sum_word_product {R : Type*} [CommSemiring R]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (G : C → Fin (Fintype.card β + 1) → R) :
    (∑ E : Fin r → C × β, ∏ c, G c (atChildCoverageFin val E c)) =
      ∑ k ∈ piAntidiag univ r, (Nat.multinomial univ k : R) *
        ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (k c) a : R) * G c a := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin r) (fun _ => C) (fun _ => β)
  calc
    _ = ∑ o : Fin r → C, ∑ B : Fin r → β, ∏ c, G c (childCoverageFin val o B c) := by
      rw [← Fintype.sum_prod_type (fun p : (Fin r → C) × (Fin r → β) =>
        ∏ c, G c (childCoverageFin val p.1 p.2 c))]
      have he := e.symm.sum_comp (fun E => ∏ c, G c (atChildCoverageFin val E c))
      rw [← he]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro c _
      congr 1
      apply Fin.ext
      exact (childCoverage_pair val p.1 p.2 c).symm
    _ = ∑ o : Fin r → C, ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (occ o c) a : R) * G c a :=
      Finset.sum_congr rfl fun o _ => sum_childCoverage_product val H hH o G
    _ = _ := by
      simpa only [nsmul_eq_mul] using sum_occ (α := C) (n := r)
        (fun k => ∏ c, ∑ a : Fin (Fintype.card β + 1), (H (k c) a : R) * G c a)


open Polynomial
noncomputable def coverageProfilePoly (ms : List ℕ) : ℕ[X] :=
  (ms.zipIdx 2).foldr (fun e s => naturalDataPoly (coverageHData e.2) ^ e.1 * s) 1
noncomputable def coverageOtherPoly (n : ℕ) : ℕ[X] :=
  coverageProfiles.foldr (fun ms acc =>
    if coverageProfileUsed ms ≤ n then
      Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
        X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms + acc
    else acc) 0
noncomputable def coverageMarkedPoly (j : ℕ) : ℕ[X] :=
  (coverageHData j).foldr (fun e s => Polynomial.C (e.1 * e.2) * X ^ e.1 + s) 0
noncomputable def retainedCoveragePoly (r : ℕ) : ℕ[X] :=
  (List.range 8).foldr (fun j acc =>
    if j + 1 ≤ r then
      Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
        coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) + acc
    else acc) 0

theorem eval_foldr_sum {α : Type*} (l : List α) (f : α → ℕ[X]) (b : ℕ) :
    Polynomial.eval b (l.foldr (fun e s => f e + s) 0) =
      l.foldr (fun e s => Polynomial.eval b (f e) + s) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]
theorem eval_foldr_prod {α : Type*} (l : List α) (f : α → ℕ[X]) (b : ℕ) :
    Polynomial.eval b (l.foldr (fun e s => f e * s) 1) =
      l.foldr (fun e s => Polynomial.eval b (f e) * s) 1 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]
theorem coverageProfilePoly_eval (ms : List ℕ) (b : ℕ) :
    Polynomial.eval b (coverageProfilePoly ms) = coverageProfilePack b ms := by
  unfold coverageProfilePoly coverageProfilePack
  rw [eval_foldr_prod]
  simp only [Polynomial.eval_pow, naturalDataPoly_eval, coverageHPack]
theorem coverageMarkedPoly_eval (j b : ℕ) :
    Polynomial.eval b (coverageMarkedPoly j) = coverageMarkedPack b j := by
  unfold coverageMarkedPoly coverageMarkedPack
  rw [eval_foldr_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
theorem coverageOtherPoly_eval (n b : ℕ) :
    Polynomial.eval b (coverageOtherPoly n) = coverageOtherPack b n := by
  unfold coverageOtherPoly coverageOtherPack
  induction coverageProfiles with
  | nil => simp
  | cons ms xs ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, coverageProfilePoly_eval, ih]
    · exact ih
theorem retainedCoveragePoly_eval (r b : ℕ) :
    Polynomial.eval b (retainedCoveragePoly r) = coverageRetainedPack b r := by
  unfold retainedCoveragePoly coverageRetainedPack
  induction List.range 8 with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        coverageMarkedPoly_eval, coverageOtherPoly_eval, ih]
    · exact ih


end ProfileRefinement

section MoreProfiles
open Polynomial

variable {β : Type*} [Fintype β]
noncomputable def lawPoly (H : ℕ → ℕ → ℕ) (N j : ℕ) : ℕ[X] :=
  ∑ a : Fin (N+1), Polynomial.C (H j a) * X ^ a.val
noncomputable def markedLawPoly (H : ℕ → ℕ → ℕ) (N j : ℕ) : ℕ[X] :=
  ∑ a : Fin (N+1), Polynomial.C (a.val * H j a) * X ^ a.val
noncomputable def markedFullPoly (val : β → Fin 6 → ℕ) (n r : ℕ) : ℕ[X] :=
  ∑ E : Fin r → Fin (n+1) × β,
    Polynomial.C (atChildCoverage val E 0) * X ^ coordinateCoverage val E

theorem markedFullPoly_coeff (val : β → Fin 6 → ℕ) (n r a : ℕ) :
    (markedFullPoly val n r).coeff a = markedCoverageCount val r (0 : Fin (n+1)) a := by
  classical
  simp only [markedFullPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    markedCoverageCount, eq_comm]

theorem markedFullPoly_eq (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (n r : ℕ) :
    markedFullPoly val n r =
      ∑ k ∈ piAntidiag univ r, (Nat.multinomial univ k : ℕ[X]) *
        markedLawPoly H (Fintype.card β) (k 0) *
          ∏ i : Fin n, lawPoly H (Fintype.card β) (k i.succ) := by
  classical
  let G : Fin (n+1) → Fin (Fintype.card β+1) → ℕ[X] :=
    fun c a => if c = 0 then Polynomial.C a.val * X ^ a.val else X ^ a.val
  have h := sum_word_product (r := r) val H hH G
  have hG (a : Fin (n+1) → Fin (Fintype.card β+1)) :
      (∏ c, G c (a c)) = Polynomial.C (a 0).val * X ^ (∑ c, (a c).val) := by
    simp only [G, Fin.prod_univ_succ, if_pos rfl, Fin.succ_ne_zero, if_false, if_true]
    rw [Finset.prod_pow_eq_pow_sum, mul_assoc, ← pow_add, Fin.sum_univ_succ]
  have hl : (∑ E : Fin r → Fin (n+1) × β, ∏ c, G c (atChildCoverageFin val E c)) =
      markedFullPoly val n r := by
    apply Finset.sum_congr rfl
    intro E _
    rw [hG]
    simp only [atChildCoverageFin, coordinateCoverage_sum]
  rw [hl] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fin.prod_univ_succ]
  have hm : (∑ a : Fin (Fintype.card β+1), (H (k 0) a : ℕ[X]) * G 0 a) =
      markedLawPoly H (Fintype.card β) (k 0) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [G, if_pos rfl, markedLawPoly]
    have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
      simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
    rw [hc, Polynomial.C_mul]
    ring
  rw [hm, ← mul_assoc]
  congr 1

noncomputable def fullOtherPoly (H : ℕ → ℕ → ℕ) (N n r : ℕ) : ℕ[X] :=
  ∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
    (Nat.multinomial univ k : ℕ[X]) * ∏ i, lawPoly H N (k i)

theorem markedFullPoly_split (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : FullCoverageHistogram val H) (n r : ℕ) :
    markedFullPoly val n r =
      ∑ j ∈ range (r+1), (r.choose j : ℕ[X]) * markedLawPoly H (Fintype.card β) j *
        fullOtherPoly H (Fintype.card β) n (r-j) := by
  classical
  rw [markedFullPoly_eq val H hH, sum_piAntidiag_cons]
  apply Finset.sum_congr rfl
  intro j hj
  unfold fullOtherPoly
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs := (Finset.mem_piAntidiag.mp hk).1
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Fin.cons_zero, Fin.cons_succ, multinomial_fin_cons, hs,
    Nat.add_sub_of_le hjr, Nat.cast_mul]
  ring


end MoreProfiles

section MoreProfiles
open Polynomial

theorem sum_piAntidiag_bounded_by {M : Type*} [AddCommMonoid M] (n r b : ℕ) (hr : r ≤ b) (F : (Fin n → ℕ) → M) :
    ∑ k ∈ piAntidiag univ r, F k =
      ∑ u : Fin n → Fin (b + 1), if (∑ i, (u i).val) = r then F (fun i => (u i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => fun i => (u i).val) ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_piAntidiag]
    exact ⟨(Finset.mem_filter.mp hu).2, fun i _ => Finset.mem_univ i⟩
  · intro u hu v hv h
    funext i
    apply Fin.ext
    exact congrFun h i
  · intro k hk
    have hsum := (Finset.mem_piAntidiag.mp hk).1
    have hb : ∀ i, k i < b + 1 := by
      intro i
      have hi : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
      have hir : k i ≤ r := by simpa only [hsum] using hi
      exact Nat.lt_succ_of_le (hir.trans hr)
    refine ⟨fun i => ⟨k i, hb i⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩
  · intro u hu
    rfl

theorem occupancy_profile_sum_bounded {R : Type*} [CommSemiring R] (n r b : ℕ) (hr : r ≤ b) (P : ℕ → R) :
    (∑ k ∈ piAntidiag (univ : Finset (Fin n)) r,
      (Nat.multinomial univ k : R) * ∏ i, P (k i)) =
      ∑ m ∈ piAntidiag (univ : Finset (Fin (b + 1))) n,
        if (∑ a, m a * a.val) = r then
          (Nat.multinomial univ m : R) *
            (r.factorial / (∏ a : Fin (b + 1), a.val.factorial ^ m a) : ℕ) *
              ∏ a : Fin (b + 1), P a.val ^ m a
        else 0 := by
  classical
  rw [sum_piAntidiag_bounded_by n r b hr]
  let Ψ : (Fin (b + 1) → ℕ) → R := fun m =>
    if (∑ a, m a * a.val) = r then
      (r.factorial / (∏ a : Fin (b + 1), a.val.factorial ^ m a) : ℕ) *
        ∏ a : Fin (b + 1), P a.val ^ m a
    else 0
  have ht : ∀ u : Fin n → Fin (b + 1),
      (if (∑ i, (u i).val) = r then
        (Nat.multinomial univ (fun i => (u i).val) : R) * ∏ i, P (u i).val else 0) = Ψ (occ u) := by
    intro u
    dsimp [Ψ]
    rw [← sum_eq_sum_mul_occ (fun a : Fin (b + 1) => a.val) u]
    by_cases hs : (∑ i, (u i).val) = r
    · rw [if_pos hs, if_pos hs, Nat.multinomial, hs,
        prod_eq_prod_pow_occ (fun a : Fin (b + 1) => a.val.factorial) u,
        prod_eq_prod_pow_occ (fun a : Fin (b + 1) => P a.val) u]
    · rw [if_neg hs, if_neg hs]
  rw [Finset.sum_congr rfl (fun u _ => ht u), sum_occ Ψ]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [Ψ]
  by_cases hs : (∑ a, m a * a.val) = r
  · rw [if_pos hs, if_pos hs]
    simp only [nsmul_eq_mul, Nat.cast_id, mul_assoc]
  · rw [if_neg hs, if_neg hs, smul_zero]


end MoreProfiles

section RetainedProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def retainedProfileList (i : Fin 30) : List ℕ := coverageProfiles[i.val]!
def retainedProfileVector (n : ℕ) (ms : List ℕ) (a : Fin 31) : ℕ :=
  if a.val = 0 then 127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)
  else if a.val = 1 then n - coverageProfileUsed ms else ms[a.val - 2]!

theorem retainedProfile_product {R : Type*} [CommMonoid R] (n : ℕ) (ms : List ℕ)
    (hms : ms.length = 6) (P : ℕ → R) :
    (∏ a : Fin 31, P a.val ^ retainedProfileVector n ms a) =
      P 0 ^ (127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)) *
        P 1 ^ (n - coverageProfileUsed ms) *
          (ms.zipIdx 2).foldr (fun e s => P e.2 ^ e.1 * s) 1 := by
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
              subst ms
              simp [Fin.prod_univ_succ, retainedProfileVector, coverageProfileUsed,
                coverageProfileGroups, List.zipIdx, mul_assoc]


theorem retainedProfile_factorials (n : ℕ) (ms : List ℕ)
    (hms : ms.length = 6)  :
    (∏ a : Fin 31, (retainedProfileVector n ms a).factorial) =
      (127 - ((n - coverageProfileUsed ms) + coverageProfileGroups ms)).factorial *
        (n - coverageProfileUsed ms).factorial *
          ms.foldr (fun m s => m.factorial * s) 1 := by
  cases ms with
  | nil => simp at hms
  | cons a ms =>
    cases ms with
    | nil => simp at hms
    | cons b ms =>
      cases ms with
      | nil => simp at hms
      | cons c ms =>
        cases ms with
        | nil => simp at hms
        | cons d ms =>
          cases ms with
          | nil => simp at hms
          | cons e ms =>
            cases ms with
            | nil => simp at hms
            | cons f ms =>
              have hn : ms = [] := List.eq_nil_of_length_eq_zero (by simpa using hms)
              subst ms
              simp [Fin.prod_univ_succ, retainedProfileVector, coverageProfileUsed,
                coverageProfileGroups, List.zipIdx, mul_assoc]


theorem retainedProfile_small_checks : ∀ n : Fin 31, ∀ i : Fin 30,
    let ms := retainedProfileList i
    coverageProfileUsed ms ≤ n.val →
      (∑ a, retainedProfileVector n.val ms a) = 127 ∧
      (∑ a, retainedProfileVector n.val ms a * a.val) = n.val := by decide +kernel

theorem retainedProfile_length (i : Fin 30) : (retainedProfileList i).length = 6 := by
  fin_cases i <;> decide +kernel

theorem retainedProfile_checks (n : Fin 31) (i : Fin 30)
    (hu : coverageProfileUsed (retainedProfileList i) ≤ n.val) :
      (∑ a, retainedProfileVector n.val (retainedProfileList i) a) = 127 ∧
      (∑ a, retainedProfileVector n.val (retainedProfileList i) a * a.val) = n.val ∧
      Nat.multinomial univ (retainedProfileVector n.val (retainedProfileList i)) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^ retainedProfileVector n.val (retainedProfileList i) a) =
          coverageProfileCount n.val (retainedProfileList i) := by
  have hs := retainedProfile_small_checks n i hu
  refine ⟨hs.1, hs.2, ?_⟩
  unfold Nat.multinomial
  rw [hs.1, retainedProfile_factorials n.val _ (retainedProfile_length i),
    retainedProfile_product n.val _ (retainedProfile_length i) Nat.factorial]
  simp only [Nat.factorial_zero, Nat.factorial_one, one_pow, one_mul]
  simp only [coverageProfileCount, coverageProfileMultiplicity, coverageProfilePositions, Kernel.fact_eq]

theorem retainedProfile_injective : ∀ n : Fin 31,
    Function.Injective (fun i : Fin 30 => retainedProfileVector n.val (retainedProfileList i)) := by
  decide +kernel


end RetainedProfiles

section RetainedCountBound
open Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
noncomputable def coverageOtherTerm (n : ℕ) (ms : List ℕ) : ℕ[X] :=
  if coverageProfileUsed ms ≤ n then
    Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
      X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms else 0

theorem coverageOtherPoly_eq_sum (n : ℕ) :
    coverageOtherPoly n = ∑ i : Fin 30, coverageOtherTerm n (retainedProfileList i) := by
  have hf (l : List (List ℕ)) :
      l.foldr (fun ms acc => if coverageProfileUsed ms ≤ n then
        Polynomial.C (coverageProfileCount n ms * 563 ^ (n - coverageProfileUsed ms)) *
          X ^ (n - coverageProfileUsed ms) * coverageProfilePoly ms + acc else acc) 0 =
        (l.map (coverageOtherTerm n)).sum := by
    induction l with
    | nil => simp
    | cons ms xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, coverageOtherTerm]
      split_ifs with h <;> rw [ih] <;> simp only [zero_add]
  rw [coverageOtherPoly, hf]
  have hlist : coverageProfiles = List.ofFn retainedProfileList := by decide +kernel
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

theorem profileLawPoly_eq_data (H : ℕ → ℕ → ℕ) (i : Fin 30)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    ((retainedProfileList i).zipIdx 2).foldr (fun e s => lawPoly H 563 e.2 ^ e.1 * s) 1 =
      coverageProfilePoly (retainedProfileList i) := by
  have h2 := hP 2 (by decide) (by decide)
  have h3 := hP 3 (by decide) (by decide)
  have h4 := hP 4 (by decide) (by decide)
  have h5 := hP 5 (by decide) (by decide)
  have h6 := hP 6 (by decide) (by decide)
  have h7 := hP 7 (by decide) (by decide)
  fin_cases i <;> simp [retainedProfileList, coverageProfiles, coverageProfilePoly,
    List.zipIdx, h2, h3, h4, h5, h6, h7]

theorem coverageOtherTerm_profile (H : ℕ → ℕ → ℕ) (n : Fin 31) (i : Fin 30)
    (hu : coverageProfileUsed (retainedProfileList i) ≤ n.val)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    coverageOtherTerm n.val (retainedProfileList i) =
      (Nat.multinomial univ (retainedProfileVector n.val (retainedProfileList i)) : ℕ[X]) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^
          retainedProfileVector n.val (retainedProfileList i) a : ℕ) *
        ∏ a : Fin 31, lawPoly H 563 a.val ^ retainedProfileVector n.val (retainedProfileList i) a := by
  have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
    simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
  have hn := (retainedProfile_checks n i hu).2.2
  rw [← Nat.cast_mul, hn, hc,
    retainedProfile_product n.val (retainedProfileList i) (retainedProfile_length i),
    h0, h1, one_pow, one_mul, profileLawPoly_eq_data H i hP]
  simp only [coverageOtherTerm, if_pos hu, Polynomial.C_mul, mul_pow, Polynomial.C_pow]
  ring



def CoeffLE (p q : ℕ[X]) : Prop := ∀ a, p.coeff a ≤ q.coeff a

theorem CoeffLE.refl (p : ℕ[X]) : CoeffLE p p := fun _ => le_rfl

theorem CoeffLE.mul (p p' q q' : ℕ[X]) (hp : CoeffLE p p') (hq : CoeffLE q q') :
    CoeffLE (p*q) (p'*q') := by
  intro a
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_le_sum
  intro ij hij
  exact Nat.mul_le_mul (hp ij.1) (hq ij.2)

theorem CoeffLE.sum {α : Type*} (s : Finset α) (p q : α → ℕ[X])
    (h : ∀ i ∈ s, CoeffLE (p i) (q i)) : CoeffLE (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  intro a
  simp only [Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum fun i hi => h i hi a

theorem coeffSum_subset {α : Type*} [DecidableEq α] (s t : Finset α) (h : s ⊆ t)
    (p : α → ℕ[X]) : CoeffLE (∑ i ∈ s, p i) (∑ i ∈ t, p i) := by
  intro a
  simp only [Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

theorem coeffSum_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (hf : Function.Injective f)
    (ht : ∀ i ∈ s, f i ∈ t) (p : β → ℕ[X]) :
    CoeffLE (∑ i ∈ s, p (f i)) (∑ j ∈ t, p j) := by
  rw [← Finset.sum_image (fun a _ b _ h => hf h)]
  apply coeffSum_subset
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  exact ht a ha


attribute [local irreducible] Finset.piAntidiag

set_option maxHeartbeats 200000 in
theorem coverageOtherPoly_below (H : ℕ → ℕ → ℕ) (n : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j)) :
    CoeffLE (coverageOtherPoly n.val) (fullOtherPoly H 563 127 n.val) := by
  classical
  let v : Fin 30 → Fin 31 → ℕ := fun i => retainedProfileVector n.val (retainedProfileList i)
  let F : (Fin 31 → ℕ) → ℕ[X] := fun m =>
    if (∑ a, m a * a.val) = n.val then
      (Nat.multinomial univ m : ℕ[X]) *
        (n.val.factorial / ∏ a : Fin 31, a.val.factorial ^ m a : ℕ) *
          ∏ a : Fin 31, lawPoly H 563 a.val ^ m a else 0
  let s : Finset (Fin 30) := univ.filter (fun i => coverageProfileUsed (retainedProfileList i) ≤ n.val)
  run_tac Lean.logInfo "coverageOtherPoly_below: entering hf"
  have hf : fullOtherPoly H 563 127 n.val = ∑ m ∈ piAntidiag univ 127, F m := by
    exact occupancy_profile_sum_bounded 127 n.val 30 (by omega) (lawPoly H 563)
  run_tac Lean.logInfo "coverageOtherPoly_below: entering he"
  have he : coverageOtherPoly n.val = ∑ i ∈ s, F (v i) := by
    rw [coverageOtherPoly_eq_sum]
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hu : coverageProfileUsed (retainedProfileList i) ≤ n.val
    · rw [if_pos hu]
      dsimp [F, v]
      rw [if_pos (retainedProfile_checks n i hu).2.1]
      exact coverageOtherTerm_profile H n i hu h0 h1 hP
    · rw [if_neg hu]
      simp only [coverageOtherTerm, if_neg hu]
  run_tac Lean.logInfo "coverageOtherPoly_below: entering final bound"
  have hmem : ∀ i ∈ s, v i ∈ piAntidiag univ 127 := by
    intro i hi
    have hu := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_piAntidiag]
    exact ⟨(retainedProfile_checks n i hu).1, fun _ _ => Finset.mem_univ _⟩
  run_tac Lean.logInfo "coverageOtherPoly_below: membership complete"
  have hinj : Function.Injective v := retainedProfile_injective n
  run_tac Lean.logInfo "coverageOtherPoly_below: injection complete"
  rw [he, hf]
  intro a
  simp only [Polynomial.finsetSum_coeff]
  rw [← Finset.sum_image (f := fun m => (F m).coeff a) (s := s) (g := v) hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact hmem i hi
  · intros
    exact Nat.zero_le _

noncomputable def retainedCoverageTerm (r j : ℕ) : ℕ[X] :=
  if j + 1 ≤ r then
    Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
      coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) else 0

theorem retainedCoveragePoly_eq_sum (r : ℕ) :
    retainedCoveragePoly r = ∑ j : Fin 8, retainedCoverageTerm r j.val := by
  have hf (l : List ℕ) :
      l.foldr (fun j acc => if j + 1 ≤ r then
        Polynomial.C (Kernel.fact r / (Kernel.fact (j+1) * Kernel.fact (r-(j+1)))) *
          coverageMarkedPoly (j+1) * coverageOtherPoly (r-(j+1)) + acc else acc) 0 =
        (l.map (retainedCoverageTerm r)).sum := by
    induction l with
    | nil => simp
    | cons j xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, retainedCoverageTerm]
      split_ifs with h <;> rw [ih] <;> simp only [zero_add]
  rw [retainedCoveragePoly, hf]
  have hlist : List.range 8 = List.ofFn (fun j : Fin 8 => j.val) := by decide +kernel
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

theorem CoeffLE.trans {p q r : ℕ[X]} (hp : CoeffLE p q) (hq : CoeffLE q r) : CoeffLE p r :=
  fun a => (hp a).trans (hq a)

theorem retainedCoveragePoly_below {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (hcard : Fintype.card β = 563) (r : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (hM : ∀ j, 1 ≤ j → j ≤ 8 → markedLawPoly H 563 j = coverageMarkedPoly j) :
    CoeffLE (retainedCoveragePoly r.val) (markedFullPoly val 127 r.val) := by
  classical
  let F : ℕ → ℕ[X] := fun j => (r.val.choose j : ℕ[X]) * markedLawPoly H 563 j *
    fullOtherPoly H 563 127 (r.val-j)
  let s : Finset (Fin 8) := univ.filter (fun j => j.val + 1 ≤ r.val)
  have he : retainedCoveragePoly r.val = ∑ j ∈ s, retainedCoverageTerm r.val j.val := by
    rw [retainedCoveragePoly_eq_sum]
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j.val + 1 ≤ r.val
    · rw [if_pos h]
    · simp [retainedCoverageTerm, h]
  have ht : ∀ j ∈ s, CoeffLE (retainedCoverageTerm r.val j.val) (F (j.val+1)) := by
    intro j hj
    have hu := (Finset.mem_filter.mp hj).2
    have hn : r.val-(j.val+1) < 31 := lt_of_le_of_lt (Nat.sub_le _ _) r.isLt
    have hm := hM (j.val+1) (by omega) (by omega)
    simp only [retainedCoverageTerm, if_pos hu, Kernel.fact_eq,
      ← Nat.choose_eq_factorial_div_factorial hu]
    have hc (m : ℕ) : (m : ℕ[X]) = Polynomial.C m := by
      simpa using (Polynomial.C_eq_natCast (R := ℕ) m).symm
    dsimp [F]
    rw [hc, hm]
    exact CoeffLE.mul _ _ _ _ (CoeffLE.refl _) (coverageOtherPoly_below H ⟨_, hn⟩ h0 h1 hP)
  rw [he]
  apply (CoeffLE.sum s _ _ ht).trans
  have hinj : Function.Injective (fun j : Fin 8 => j.val+1) := by
    intro a b h
    apply Fin.ext
    change a.val + 1 = b.val + 1 at h
    omega
  have hsub := coeffSum_injective s (range (r.val+1)) (fun j : Fin 8 => j.val+1) hinj
    (fun j hj => Finset.mem_range.mpr (by have h := (Finset.mem_filter.mp hj).2; omega)) F
  have hf : markedFullPoly val 127 r.val = ∑ j ∈ range (r.val+1), F j := by
    simpa only [hcard] using markedFullPoly_split val H hH 127 r.val
  rw [hf]
  exact hsub

theorem retainedCoverage_count_bound {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (H : ℕ → ℕ → ℕ) (hH : FullCoverageHistogram val H)
    (hcard : Fintype.card β = 563) (r : Fin 31)
    (h0 : lawPoly H 563 0 = 1) (h1 : lawPoly H 563 1 = Polynomial.C 563 * X)
    (hP : ∀ j, 2 ≤ j → j ≤ 7 → lawPoly H 563 j = naturalDataPoly (coverageHData j))
    (hM : ∀ j, 1 ≤ j → j ≤ 8 → markedLawPoly H 563 j = coverageMarkedPoly j) (a : ℕ) :
    128 * (retainedCoveragePoly r.val).coeff a ≤
      a * #{E : Fin r.val → Fin 128 × β | coordinateCoverage val E = a} := by
  have h := retainedCoveragePoly_below val H hH hcard r h0 h1 hP hM a
  rw [markedFullPoly_coeff] at h
  exact retainedCoverage_weighted val r.val (0 : Fin 128) a _ h

end RetainedCountBound
end ClaudeWCT.Numerics.N600

open Finset Polynomial
namespace ClaudeWCT.Numerics.N600
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem lawPoly_coeff (H : ℕ → ℕ → ℕ) (N j a : ℕ) :
    (lawPoly H N j).coeff a = if a ≤ N then H j a else 0 := by
  classical
  simp only [lawPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a ≤ N
  · rw [if_pos ha]
    let v : Fin (N+1) := ⟨a, by omega⟩
    rw [Finset.sum_eq_single v]
    · simp [v]
    · intro b hb hne
      have hab : a ≠ b.val := fun he => hne (Fin.ext he.symm)
      simp [hab]
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    have hab : a ≠ b.val := by have := b.isLt; omega
    simp [hab]

theorem markedLawPoly_coeff (H : ℕ → ℕ → ℕ) (N j a : ℕ) :
    (markedLawPoly H N j).coeff a = a * (lawPoly H N j).coeff a := by
  classical
  simp only [markedLawPoly, lawPoly, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases ha : a = b.val <;> simp [ha]

theorem weightedDataPoly_coeff (d : List (ℕ × ℕ)) (a : ℕ) :
    ((d.foldr (fun e s => Polynomial.C (e.1 * e.2) * X ^ e.1 + s) 0 : ℕ[X]).coeff a) =
      a * (naturalDataPoly d).coeff a := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e es ih =>
    simp only [List.foldr_cons, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      naturalDataPoly, List.map_cons, List.sum_cons, mul_add]
    rw [ih]
    by_cases ha : a = e.1 <;> simp [ha, naturalDataPoly]

theorem coverageMarkedPoly_coeff (j a : ℕ) :
    (coverageMarkedPoly j).coeff a = a * (naturalDataPoly (coverageHData j)).coeff a :=
  weightedDataPoly_coeff (coverageHData j) a

theorem naturalDataPoly_high_coeff (d : List (ℕ × ℕ)) (N : ℕ)
    (hd : ∀ e ∈ d, e.1 ≤ N) (a : ℕ) (ha : N < a) :
    (naturalDataPoly d).coeff a = 0 := by
  induction d with
  | nil => simp [naturalDataPoly]
  | cons e es ih =>
    have he := hd e (by simp)
    have hne : a ≠ e.1 := by omega
    have hdes : ∀ e ∈ es, e.1 ≤ N := by intro z hz; exact hd z (by simp [hz])
    simp only [naturalDataPoly, List.map_cons, List.sum_cons, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, if_neg hne, zero_add]
    exact ih hdes

theorem lawPoly_eq_data (H : ℕ → ℕ → ℕ) (N j : ℕ)
    (heq : ∀ a, H j a = coverageHAt j a)
    (hd : ∀ e ∈ coverageHData j, e.1 ≤ N) :
    lawPoly H N j = naturalDataPoly (coverageHData j) := by
  apply Polynomial.ext
  intro a
  rw [lawPoly_coeff]
  by_cases ha : a ≤ N
  · rw [if_pos ha, heq a, naturalDataPoly_coeff]
    rfl
  · rw [if_neg ha, naturalDataPoly_high_coeff _ N hd a (by omega)]

theorem markedLawPoly_eq_data (H : ℕ → ℕ → ℕ) (N j : ℕ)
    (h : lawPoly H N j = naturalDataPoly (coverageHData j)) :
    markedLawPoly H N j = coverageMarkedPoly j := by
  apply Polynomial.ext
  intro a
  rw [markedLawPoly_coeff, coverageMarkedPoly_coeff, h]

theorem coverageHData_bounds : ∀ j : Fin 9, ∀ e ∈ coverageHData j.val, e.1 ≤ 563 := by
  decide +kernel

theorem coverageHData_mass_bounds : ∀ j : Fin 9, coverageHPack 1 j.val < 2^127 := by
  decide +kernel

theorem coverageLaw_zero_poly : lawPoly coverageLaw 563 0 = 1 := by
  apply Polynomial.ext
  intro a
  rw [lawPoly_coeff]
  by_cases ha : a = 0
  · subst a; simp [coverageLaw]
  · simp [coverageLaw, ha, Polynomial.coeff_one]

theorem coverageH1_poly : naturalDataPoly (coverageHData 1) = Polynomial.C 563 * X := by
  simp [coverageHData, coverageH1Data, naturalDataPoly]

theorem coverageLaw_eq_packed {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i ≤ 4)
    (hcard : Fintype.card β = 563)
    (hpacked : ∀ j, 1 ≤ j → j ≤ 8 → coveragePacked (2^128) j = coverageHPack (2^128) j)
    (j : ℕ) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (a : ℕ) :
    coverageLaw j a = coverageHAt j a := by
  rw [coverageLaw, if_neg (by omega)]
  apply coverageHistogram_of_packed j (hpacked j hj1 hj8) ?_ ?_ a
  · rw [coveragePacked_mass val hW h4 (by omega), hcard]
    calc
      563 ^ j ≤ 563 ^ 8 := Nat.pow_le_pow_right (by omega) hj8
      _ < 2^127 := by norm_num
  · exact coverageHData_mass_bounds ⟨j, by omega⟩

theorem retainedCoverage_count_bound_of_packed {β : Type*} [Fintype β]
    (val : β → Fin 6 → ℕ) (hW : WordsOf val) (h4 : ∀ x i, val x i ≤ 4)
    (hcard : Fintype.card β = 563)
    (hpacked : ∀ j, 1 ≤ j → j ≤ 8 → coveragePacked (2^128) j = coverageHPack (2^128) j)
    (r : Fin 31) (a : ℕ) :
    128 * (retainedCoveragePoly r.val).coeff a ≤
      a * #{E : Fin r.val → Fin 128 × β | coordinateCoverage val E = a} := by
  have hpoly (j : ℕ) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
      lawPoly coverageLaw 563 j = naturalDataPoly (coverageHData j) :=
    lawPoly_eq_data coverageLaw 563 j (coverageLaw_eq_packed val hW h4 hcard hpacked j hj1 hj8)
      (coverageHData_bounds ⟨j, by omega⟩)
  exact retainedCoverage_count_bound val coverageLaw (coverageLaw_correct val hW h4) hcard r
    coverageLaw_zero_poly ((hpoly 1 (by decide) (by decide)).trans coverageH1_poly)
    (fun j hj1 hj8 => hpoly j (by omega) (by omega))
    (fun j hj1 hj8 => markedLawPoly_eq_data _ _ _ (hpoly j hj1 hj8)) a
end ClaudeWCT.Numerics.N600
end
-- ==== merged from ClaudeWCT_Numerics_N600PriceChecksRows ====
section

-- Keep the independent kernel certificates sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

section


namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (wpos wneg fact HB packPos packNeg)
def Nn : Nat := 563
def Kc : Nat := 128
def Q : Nat := 72064
def B1 : Nat := 71501
def B2 : Nat := 70938
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xfNum (t r : Nat) : Nat := wpos (wfData t) B1 r - wneg (wfData t) B1 r
def xfSum (r : Nat) : Nat := xfNum 0 r + xfNum 1 r + xfNum 2 r + xfNum 3 r + xfNum 4 r + xfNum 5 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wpos wwData B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wneg wwData B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def poissonCheckQ (Qv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Qv ^ (9 * (R - r)) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R)) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Qv ^ (9 * R)
def A : Nat := 1353 * 2 ^ 24 * 563 ^ 9
def LN : Nat := 203317755
def LD : Nat := 100000000
def MN : Nat := 675
def MD : Nat := 1000
def DN : Nat := 3200
def DD : Nat := 1000000
def NN : Nat := 291
def ND : Nat := 1
def meanCheck : Bool := poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 9) (Nn ^ 9) A 1 MN MD 80
def diagCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => yNum r ^ 9) ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) DN DD 80
def nearCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 8 * xfSum r) (6 * Nn ^ 9) (54 * A) 1 NN ND 80
def convCheck : Bool :=
  Nat.beq (packPos w1Data ^ 2 + packNeg w1Data ^ 2 + packNeg wwData) (packPos wwData + 2 * packPos w1Data * packNeg w1Data)
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem mean_ok : meanCheck = true := by decide +kernel
theorem near_ok : nearCheck = true := by decide +kernel
theorem diag_ok : diagCheck = true := by decide +kernel
theorem conv_ok : convCheck = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end


namespace ClaudeWCT.Numerics.N600
-- Certify the shared prefix-count tree once for the eight finite histogram checks.
private def cntCached0 : T6 := .leaf 0
private def cntCached1 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached0
private def cntCached2 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached1 cntCached1 cntCached1
private def cntCached3 : T6 := .node cntCached2 cntCached2 cntCached2 cntCached2 cntCached2 cntCached2
private def cntCached4 : T6 := .node cntCached3 cntCached3 cntCached3 cntCached3 cntCached3 cntCached3
private def cntCached5 : T6 := .node cntCached4 cntCached4 cntCached4 cntCached4 cntCached4 cntCached4
private def cntCached6 : T6 := .leaf 1
private def cntCached7 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached6
private def cntCached8 : T6 := .leaf 2
private def cntCached9 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached8
private def cntCached10 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached1 cntCached7 cntCached9
private def cntCached11 : T6 := .leaf 3
private def cntCached12 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached11
private def cntCached13 : T6 := .leaf 5
private def cntCached14 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached11 cntCached13
private def cntCached15 : T6 := .node cntCached1 cntCached1 cntCached1 cntCached7 cntCached12 cntCached14
private def cntCached16 : T6 := .leaf 6
private def cntCached17 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached11 cntCached16
private def cntCached18 : T6 := .leaf 9
private def cntCached19 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached16 cntCached18
private def cntCached20 : T6 := .node cntCached1 cntCached1 cntCached7 cntCached12 cntCached17 cntCached19
private def cntCached21 : T6 := .leaf 10
private def cntCached22 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached16 cntCached21
private def cntCached23 : T6 := .leaf 14
private def cntCached24 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached16 cntCached21 cntCached23
private def cntCached25 : T6 := .node cntCached1 cntCached7 cntCached12 cntCached17 cntCached22 cntCached24
private def cntCached26 : T6 := .leaf 18
private def cntCached27 : T6 := .node cntCached0 cntCached8 cntCached13 cntCached18 cntCached23 cntCached26
private def cntCached28 : T6 := .node cntCached1 cntCached9 cntCached14 cntCached19 cntCached24 cntCached27
private def cntCached29 : T6 := .node cntCached2 cntCached10 cntCached15 cntCached20 cntCached25 cntCached28
private def cntCached30 : T6 := .leaf 4
private def cntCached31 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached30
private def cntCached32 : T6 := .leaf 8
private def cntCached33 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached30 cntCached32
private def cntCached34 : T6 := .leaf 12
private def cntCached35 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached32 cntCached34
private def cntCached36 : T6 := .node cntCached1 cntCached1 cntCached7 cntCached31 cntCached33 cntCached35
private def cntCached37 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached30 cntCached18
private def cntCached38 : T6 := .leaf 15
private def cntCached39 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached18 cntCached38
private def cntCached40 : T6 := .leaf 21
private def cntCached41 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached38 cntCached40
private def cntCached42 : T6 := .node cntCached1 cntCached7 cntCached31 cntCached37 cntCached39 cntCached41
private def cntCached43 : T6 := .leaf 16
private def cntCached44 : T6 := .leaf 23
private def cntCached45 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached43 cntCached44
private def cntCached46 : T6 := .leaf 30
private def cntCached47 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached38 cntCached44 cntCached46
private def cntCached48 : T6 := .node cntCached1 cntCached12 cntCached33 cntCached39 cntCached45 cntCached47
private def cntCached49 : T6 := .leaf 37
private def cntCached50 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached40 cntCached46 cntCached49
private def cntCached51 : T6 := .node cntCached1 cntCached14 cntCached35 cntCached41 cntCached47 cntCached50
private def cntCached52 : T6 := .node cntCached2 cntCached15 cntCached36 cntCached42 cntCached48 cntCached51
private def cntCached53 : T6 := .leaf 17
private def cntCached54 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached21 cntCached53
private def cntCached55 : T6 := .leaf 26
private def cntCached56 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached26 cntCached55
private def cntCached57 : T6 := .leaf 34
private def cntCached58 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached55 cntCached57
private def cntCached59 : T6 := .node cntCached1 cntCached12 cntCached37 cntCached54 cntCached56 cntCached58
private def cntCached60 : T6 := .leaf 28
private def cntCached61 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached60 cntCached49
private def cntCached62 : T6 := .leaf 46
private def cntCached63 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached55 cntCached49 cntCached62
private def cntCached64 : T6 := .node cntCached1 cntCached17 cntCached39 cntCached56 cntCached61 cntCached63
private def cntCached65 : T6 := .leaf 55
private def cntCached66 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached62 cntCached65
private def cntCached67 : T6 := .node cntCached1 cntCached19 cntCached41 cntCached58 cntCached63 cntCached66
private def cntCached68 : T6 := .node cntCached2 cntCached20 cntCached42 cntCached59 cntCached64 cntCached67
private def cntCached69 : T6 := .leaf 40
private def cntCached70 : T6 := .leaf 50
private def cntCached71 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached60 cntCached69 cntCached70
private def cntCached72 : T6 := .leaf 60
private def cntCached73 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached70 cntCached72
private def cntCached74 : T6 := .node cntCached1 cntCached22 cntCached45 cntCached61 cntCached71 cntCached73
private def cntCached75 : T6 := .leaf 70
private def cntCached76 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached62 cntCached72 cntCached75
private def cntCached77 : T6 := .node cntCached1 cntCached24 cntCached47 cntCached63 cntCached73 cntCached76
private def cntCached78 : T6 := .node cntCached2 cntCached25 cntCached48 cntCached64 cntCached74 cntCached77
private def cntCached79 : T6 := .leaf 80
private def cntCached80 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached65 cntCached75 cntCached79
private def cntCached81 : T6 := .node cntCached1 cntCached27 cntCached50 cntCached66 cntCached76 cntCached80
private def cntCached82 : T6 := .node cntCached2 cntCached28 cntCached51 cntCached67 cntCached77 cntCached81
private def cntCached83 : T6 := .node cntCached3 cntCached29 cntCached52 cntCached68 cntCached78 cntCached82
private def cntCached84 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached13
private def cntCached85 : T6 := .leaf 11
private def cntCached86 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached30 cntCached85
private def cntCached87 : T6 := .leaf 19
private def cntCached88 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached85 cntCached87
private def cntCached89 : T6 := .leaf 27
private def cntCached90 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached85 cntCached87 cntCached89
private def cntCached91 : T6 := .node cntCached1 cntCached7 cntCached84 cntCached86 cntCached88 cntCached90
private def cntCached92 : T6 := .leaf 20
private def cntCached93 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached21 cntCached92
private def cntCached94 : T6 := .leaf 32
private def cntCached95 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached40 cntCached94
private def cntCached96 : T6 := .leaf 43
private def cntCached97 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached92 cntCached94 cntCached96
private def cntCached98 : T6 := .node cntCached1 cntCached31 cntCached86 cntCached93 cntCached95 cntCached97
private def cntCached99 : T6 := .leaf 35
private def cntCached100 : T6 := .leaf 47
private def cntCached101 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached40 cntCached99 cntCached100
private def cntCached102 : T6 := .leaf 59
private def cntCached103 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached94 cntCached100 cntCached102
private def cntCached104 : T6 := .node cntCached1 cntCached33 cntCached88 cntCached95 cntCached101 cntCached103
private def cntCached105 : T6 := .leaf 71
private def cntCached106 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached96 cntCached102 cntCached105
private def cntCached107 : T6 := .node cntCached1 cntCached35 cntCached90 cntCached97 cntCached103 cntCached106
private def cntCached108 : T6 := .node cntCached2 cntCached36 cntCached91 cntCached98 cntCached104 cntCached107
private def cntCached109 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached32 cntCached40 cntCached57
private def cntCached110 : T6 := .leaf 51
private def cntCached111 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached40 cntCached49 cntCached110
private def cntCached112 : T6 := .leaf 65
private def cntCached113 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached110 cntCached112
private def cntCached114 : T6 := .node cntCached1 cntCached37 cntCached93 cntCached109 cntCached111 cntCached113
private def cntCached115 : T6 := .leaf 56
private def cntCached116 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached49 cntCached115 cntCached105
private def cntCached117 : T6 := .leaf 86
private def cntCached118 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached110 cntCached105 cntCached117
private def cntCached119 : T6 := .node cntCached1 cntCached39 cntCached95 cntCached111 cntCached116 cntCached118
private def cntCached120 : T6 := .leaf 101
private def cntCached121 : T6 := .node cntCached0 cntCached40 cntCached96 cntCached112 cntCached117 cntCached120
private def cntCached122 : T6 := .node cntCached1 cntCached41 cntCached97 cntCached113 cntCached118 cntCached121
private def cntCached123 : T6 := .node cntCached2 cntCached42 cntCached98 cntCached114 cntCached119 cntCached122
private def cntCached124 : T6 := .leaf 78
private def cntCached125 : T6 := .leaf 94
private def cntCached126 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached115 cntCached124 cntCached125
private def cntCached127 : T6 := .leaf 110
private def cntCached128 : T6 := .node cntCached0 cntCached44 cntCached100 cntCached105 cntCached125 cntCached127
private def cntCached129 : T6 := .node cntCached1 cntCached45 cntCached101 cntCached116 cntCached126 cntCached128
private def cntCached130 : T6 := .leaf 126
private def cntCached131 : T6 := .node cntCached0 cntCached46 cntCached102 cntCached117 cntCached127 cntCached130
private def cntCached132 : T6 := .node cntCached1 cntCached47 cntCached103 cntCached118 cntCached128 cntCached131
private def cntCached133 : T6 := .node cntCached2 cntCached48 cntCached104 cntCached119 cntCached129 cntCached132
private def cntCached134 : T6 := .leaf 142
private def cntCached135 : T6 := .node cntCached0 cntCached49 cntCached105 cntCached120 cntCached130 cntCached134
private def cntCached136 : T6 := .node cntCached1 cntCached50 cntCached106 cntCached121 cntCached131 cntCached135
private def cntCached137 : T6 := .node cntCached2 cntCached51 cntCached107 cntCached122 cntCached132 cntCached136
private def cntCached138 : T6 := .node cntCached3 cntCached52 cntCached108 cntCached123 cntCached133 cntCached137
private def cntCached139 : T6 := .leaf 39
private def cntCached140 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached92 cntCached139 cntCached65
private def cntCached141 : T6 := .leaf 61
private def cntCached142 : T6 := .node cntCached0 cntCached21 cntCached40 cntCached139 cntCached141 cntCached124
private def cntCached143 : T6 := .leaf 95
private def cntCached144 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached65 cntCached124 cntCached143
private def cntCached145 : T6 := .node cntCached1 cntCached54 cntCached109 cntCached140 cntCached142 cntCached144
private def cntCached146 : T6 := .leaf 104
private def cntCached147 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached141 cntCached117 cntCached146
private def cntCached148 : T6 := .leaf 122
private def cntCached149 : T6 := .node cntCached0 cntCached55 cntCached110 cntCached124 cntCached146 cntCached148
private def cntCached150 : T6 := .node cntCached1 cntCached56 cntCached111 cntCached142 cntCached147 cntCached149
private def cntCached151 : T6 := .leaf 140
private def cntCached152 : T6 := .node cntCached0 cntCached57 cntCached112 cntCached143 cntCached148 cntCached151
private def cntCached153 : T6 := .node cntCached1 cntCached58 cntCached113 cntCached144 cntCached149 cntCached152
private def cntCached154 : T6 := .node cntCached2 cntCached59 cntCached114 cntCached145 cntCached150 cntCached153
private def cntCached155 : T6 := .leaf 114
private def cntCached156 : T6 := .leaf 133
private def cntCached157 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached117 cntCached155 cntCached156
private def cntCached158 : T6 := .leaf 152
private def cntCached159 : T6 := .node cntCached0 cntCached49 cntCached105 cntCached146 cntCached156 cntCached158
private def cntCached160 : T6 := .node cntCached1 cntCached61 cntCached116 cntCached147 cntCached157 cntCached159
private def cntCached161 : T6 := .leaf 171
private def cntCached162 : T6 := .node cntCached0 cntCached62 cntCached117 cntCached148 cntCached158 cntCached161
private def cntCached163 : T6 := .node cntCached1 cntCached63 cntCached118 cntCached149 cntCached159 cntCached162
private def cntCached164 : T6 := .node cntCached2 cntCached64 cntCached119 cntCached150 cntCached160 cntCached163
private def cntCached165 : T6 := .leaf 190
private def cntCached166 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached151 cntCached161 cntCached165
private def cntCached167 : T6 := .node cntCached1 cntCached66 cntCached121 cntCached152 cntCached162 cntCached166
private def cntCached168 : T6 := .node cntCached2 cntCached67 cntCached122 cntCached153 cntCached163 cntCached167
private def cntCached169 : T6 := .node cntCached3 cntCached68 cntCached123 cntCached154 cntCached164 cntCached168
private def cntCached170 : T6 := .leaf 145
private def cntCached171 : T6 := .leaf 165
private def cntCached172 : T6 := .node cntCached0 cntCached69 cntCached124 cntCached155 cntCached170 cntCached171
private def cntCached173 : T6 := .leaf 185
private def cntCached174 : T6 := .node cntCached0 cntCached70 cntCached125 cntCached156 cntCached171 cntCached173
private def cntCached175 : T6 := .node cntCached1 cntCached71 cntCached126 cntCached157 cntCached172 cntCached174
private def cntCached176 : T6 := .leaf 205
private def cntCached177 : T6 := .node cntCached0 cntCached72 cntCached127 cntCached158 cntCached173 cntCached176
private def cntCached178 : T6 := .node cntCached1 cntCached73 cntCached128 cntCached159 cntCached174 cntCached177
private def cntCached179 : T6 := .node cntCached2 cntCached74 cntCached129 cntCached160 cntCached175 cntCached178
private def cntCached180 : T6 := .leaf 225
private def cntCached181 : T6 := .node cntCached0 cntCached75 cntCached130 cntCached161 cntCached176 cntCached180
private def cntCached182 : T6 := .node cntCached1 cntCached76 cntCached131 cntCached162 cntCached177 cntCached181
private def cntCached183 : T6 := .node cntCached2 cntCached77 cntCached132 cntCached163 cntCached178 cntCached182
private def cntCached184 : T6 := .node cntCached3 cntCached78 cntCached133 cntCached164 cntCached179 cntCached183
private def cntCached185 : T6 := .leaf 245
private def cntCached186 : T6 := .node cntCached0 cntCached79 cntCached134 cntCached165 cntCached180 cntCached185
private def cntCached187 : T6 := .node cntCached1 cntCached80 cntCached135 cntCached166 cntCached181 cntCached186
private def cntCached188 : T6 := .node cntCached2 cntCached81 cntCached136 cntCached167 cntCached182 cntCached187
private def cntCached189 : T6 := .node cntCached3 cntCached82 cntCached137 cntCached168 cntCached183 cntCached188
private def cntCached190 : T6 := .node cntCached4 cntCached83 cntCached138 cntCached169 cntCached184 cntCached189
private def cntCached191 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached30
private def cntCached192 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached11 cntCached21
private def cntCached193 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached18 cntCached53
private def cntCached194 : T6 := .leaf 25
private def cntCached195 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached53 cntCached194
private def cntCached196 : T6 := .node cntCached1 cntCached7 cntCached191 cntCached192 cntCached193 cntCached195
private def cntCached197 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached18 cntCached87
private def cntCached198 : T6 := .leaf 29
private def cntCached199 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached32 cntCached26 cntCached198
private def cntCached200 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached198 cntCached69
private def cntCached201 : T6 := .node cntCached1 cntCached31 cntCached192 cntCached197 cntCached199 cntCached200
private def cntCached202 : T6 := .leaf 7
private def cntCached203 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached11 cntCached202
private def cntCached204 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached32 cntCached43
private def cntCached205 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached202 cntCached53 cntCached60
private def cntCached206 : T6 := .leaf 41
private def cntCached207 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached198 cntCached206
private def cntCached208 : T6 := .leaf 53
private def cntCached209 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached89 cntCached206 cntCached208
private def cntCached210 : T6 := .node cntCached1 cntCached203 cntCached204 cntCached205 cntCached207 cntCached209
private def cntCached211 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached202 cntCached85
private def cntCached212 : T6 := .leaf 24
private def cntCached213 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached43 cntCached212
private def cntCached214 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached60 cntCached139
private def cntCached215 : T6 := .leaf 38
private def cntCached216 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached215 cntCached208 cntCached112
private def cntCached217 : T6 := .node cntCached1 cntCached211 cntCached213 cntCached214 cntCached209 cntCached216
private def cntCached218 : T6 := .node cntCached2 cntCached36 cntCached196 cntCached201 cntCached210 cntCached217
private def cntCached219 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached34
private def cntCached220 : T6 := .leaf 22
private def cntCached221 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached32 cntCached220
private def cntCached222 : T6 := .leaf 36
private def cntCached223 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached40 cntCached222
private def cntCached224 : T6 := .leaf 13
private def cntCached225 : T6 := .node cntCached0 cntCached13 cntCached224 cntCached44 cntCached222 cntCached110
private def cntCached226 : T6 := .node cntCached1 cntCached191 cntCached219 cntCached221 cntCached223 cntCached225
private def cntCached227 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached26 cntCached222
private def cntCached228 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached49 cntCached115
private def cntCached229 : T6 := .leaf 75
private def cntCached230 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached222 cntCached115 cntCached229
private def cntCached231 : T6 := .node cntCached1 cntCached192 cntCached221 cntCached227 cntCached228 cntCached230
private def cntCached232 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached18 cntCached53
private def cntCached233 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached32 cntCached92 cntCached99
private def cntCached234 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached53 cntCached222 cntCached65
private def cntCached235 : T6 := .leaf 79
private def cntCached236 : T6 := .node cntCached0 cntCached32 cntCached92 cntCached222 cntCached102 cntCached235
private def cntCached237 : T6 := .leaf 99
private def cntCached238 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached65 cntCached235 cntCached237
private def cntCached239 : T6 := .node cntCached1 cntCached232 cntCached233 cntCached234 cntCached236 cntCached238
private def cntCached240 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached21 cntCached53 cntCached194
private def cntCached241 : T6 := .node cntCached0 cntCached30 cntCached224 cntCached220 cntCached99 cntCached70
private def cntCached242 : T6 := .leaf 74
private def cntCached243 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached99 cntCached65 cntCached242
private def cntCached244 : T6 := .leaf 119
private def cntCached245 : T6 := .node cntCached0 cntCached212 cntCached70 cntCached242 cntCached237 cntCached244
private def cntCached246 : T6 := .node cntCached1 cntCached240 cntCached241 cntCached243 cntCached238 cntCached245
private def cntCached247 : T6 := .node cntCached2 cntCached196 cntCached226 cntCached231 cntCached239 cntCached246
private def cntCached248 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached87 cntCached46
private def cntCached249 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached46 cntCached206
private def cntCached250 : T6 := .node cntCached1 cntCached31 cntCached192 cntCached197 cntCached248 cntCached249
private def cntCached251 : T6 := .leaf 57
private def cntCached252 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached215 cntCached251
private def cntCached253 : T6 := .leaf 76
private def cntCached254 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached49 cntCached251 cntCached253
private def cntCached255 : T6 := .node cntCached1 cntCached192 cntCached221 cntCached227 cntCached252 cntCached254
private def cntCached256 : T6 := .node cntCached0 cntCached8 cntCached11 cntCached34 cntCached99 cntCached251
private def cntCached257 : T6 := .leaf 62
private def cntCached258 : T6 := .leaf 85
private def cntCached259 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached99 cntCached257 cntCached258
private def cntCached260 : T6 := .leaf 108
private def cntCached261 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached251 cntCached258 cntCached260
private def cntCached262 : T6 := .node cntCached1 cntCached197 cntCached227 cntCached256 cntCached259 cntCached261
private def cntCached263 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached87 cntCached46
private def cntCached264 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached49 cntCached115
private def cntCached265 : T6 := .leaf 84
private def cntCached266 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached141 cntCached265
private def cntCached267 : T6 := .leaf 92
private def cntCached268 : T6 := .leaf 116
private def cntCached269 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached141 cntCached267 cntCached268
private def cntCached270 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached265 cntCached268 cntCached151
private def cntCached271 : T6 := .node cntCached1 cntCached263 cntCached264 cntCached266 cntCached269 cntCached270
private def cntCached272 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached87 cntCached46 cntCached206
private def cntCached273 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached222 cntCached115 cntCached229
private def cntCached274 : T6 := .leaf 107
private def cntCached275 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached265 cntCached274
private def cntCached276 : T6 := .leaf 164
private def cntCached277 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached274 cntCached151 cntCached276
private def cntCached278 : T6 := .node cntCached1 cntCached272 cntCached273 cntCached275 cntCached270 cntCached277
private def cntCached279 : T6 := .node cntCached2 cntCached250 cntCached255 cntCached262 cntCached271 cntCached278
private def cntCached280 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached21 cntCached26
private def cntCached281 : T6 := .leaf 31
private def cntCached282 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached21 cntCached92 cntCached281
private def cntCached283 : T6 := .leaf 33
private def cntCached284 : T6 := .leaf 45
private def cntCached285 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached92 cntCached283 cntCached284
private def cntCached286 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached281 cntCached284 cntCached251
private def cntCached287 : T6 := .node cntCached1 cntCached33 cntCached280 cntCached282 cntCached285 cntCached286
private def cntCached288 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached18 cntCached40 cntCached222
private def cntCached289 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached87 cntCached215 cntCached251
private def cntCached290 : T6 := .leaf 82
private def cntCached291 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached139 cntCached257 cntCached290
private def cntCached292 : T6 := .leaf 58
private def cntCached293 : T6 := .leaf 102
private def cntCached294 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached292 cntCached290 cntCached293
private def cntCached295 : T6 := .node cntCached1 cntCached193 cntCached288 cntCached289 cntCached291 cntCached294
private def cntCached296 : T6 := .leaf 63
private def cntCached297 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached222 cntCached296 cntCached117
private def cntCached298 : T6 := .leaf 118
private def cntCached299 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached296 cntCached125 cntCached298
private def cntCached300 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached117 cntCached298 cntCached134
private def cntCached301 : T6 := .node cntCached1 cntCached248 cntCached289 cntCached297 cntCached299 cntCached300
private def cntCached302 : T6 := .leaf 44
private def cntCached303 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached94 cntCached302
private def cntCached304 : T6 := .leaf 81
private def cntCached305 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached215 cntCached141 cntCached304
private def cntCached306 : T6 := .leaf 93
private def cntCached307 : T6 := .leaf 117
private def cntCached308 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached257 cntCached306 cntCached307
private def cntCached309 : T6 := .leaf 128
private def cntCached310 : T6 := .leaf 153
private def cntCached311 : T6 := .node cntCached0 cntCached281 cntCached141 cntCached306 cntCached309 cntCached310
private def cntCached312 : T6 := .leaf 178
private def cntCached313 : T6 := .node cntCached0 cntCached96 cntCached304 cntCached307 cntCached310 cntCached312
private def cntCached314 : T6 := .node cntCached1 cntCached303 cntCached305 cntCached308 cntCached311 cntCached313
private def cntCached315 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached46 cntCached302 cntCached115
private def cntCached316 : T6 := .node cntCached0 cntCached53 cntCached49 cntCached251 cntCached304 cntCached120
private def cntCached317 : T6 := .leaf 141
private def cntCached318 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached258 cntCached307 cntCached317
private def cntCached319 : T6 := .leaf 203
private def cntCached320 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached317 cntCached312 cntCached319
private def cntCached321 : T6 := .node cntCached1 cntCached315 cntCached316 cntCached318 cntCached313 cntCached320
private def cntCached322 : T6 := .node cntCached2 cntCached287 cntCached295 cntCached301 cntCached314 cntCached321
private def cntCached323 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached85 cntCached26 cntCached55
private def cntCached324 : T6 := .leaf 42
private def cntCached325 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached92 cntCached281 cntCached324
private def cntCached326 : T6 := .leaf 69
private def cntCached327 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached324 cntCached251 cntCached326
private def cntCached328 : T6 := .node cntCached1 cntCached35 cntCached323 cntCached325 cntCached286 cntCached327
private def cntCached329 : T6 := .node cntCached0 cntCached30 cntCached224 cntCached44 cntCached222 cntCached110
private def cntCached330 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached251 cntCached253
private def cntCached331 : T6 := .leaf 52
private def cntCached332 : T6 := .leaf 77
private def cntCached333 : T6 := .node cntCached0 cntCached55 cntCached331 cntCached332 cntCached293 cntCached148
private def cntCached334 : T6 := .node cntCached1 cntCached195 cntCached329 cntCached330 cntCached294 cntCached333
private def cntCached335 : T6 := .leaf 109
private def cntCached336 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached292 cntCached117 cntCached335
private def cntCached337 : T6 := .leaf 166
private def cntCached338 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached335 cntCached134 cntCached337
private def cntCached339 : T6 := .node cntCached1 cntCached249 cntCached330 cntCached336 cntCached300 cntCached338
private def cntCached340 : T6 := .leaf 68
private def cntCached341 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached206 cntCached115 cntCached340
private def cntCached342 : T6 := .leaf 121
private def cntCached343 : T6 := .node cntCached0 cntCached194 cntCached331 cntCached253 cntCached120 cntCached342
private def cntCached344 : T6 := .node cntCached0 cntCached69 cntCached253 cntCached260 cntCached317 cntCached171
private def cntCached345 : T6 := .leaf 67
private def cntCached346 : T6 := .leaf 228
private def cntCached347 : T6 := .node cntCached0 cntCached345 cntCached342 cntCached171 cntCached319 cntCached346
private def cntCached348 : T6 := .node cntCached1 cntCached341 cntCached343 cntCached344 cntCached320 cntCached347
private def cntCached349 : T6 := .node cntCached2 cntCached328 cntCached334 cntCached339 cntCached321 cntCached348
private def cntCached350 : T6 := .node cntCached3 cntCached218 cntCached247 cntCached279 cntCached322 cntCached349
private def cntCached351 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached0 cntCached11
private def cntCached352 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached18
private def cntCached353 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached32 cntCached26
private def cntCached354 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached18 cntCached26 cntCached198
private def cntCached355 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached198 cntCached69
private def cntCached356 : T6 := .node cntCached1 cntCached351 cntCached352 cntCached353 cntCached354 cntCached355
private def cntCached357 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached202
private def cntCached358 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached202 cntCached53
private def cntCached359 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached16 cntCached53 cntCached46
private def cntCached360 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached53 cntCached281 cntCached284
private def cntCached361 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached46 cntCached284 cntCached102
private def cntCached362 : T6 := .node cntCached1 cntCached357 cntCached358 cntCached359 cntCached360 cntCached361
private def cntCached363 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached8 cntCached16 cntCached34
private def cntCached364 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached202 cntCached43 cntCached89
private def cntCached365 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached46 cntCached302
private def cntCached366 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached46 cntCached100 cntCached257
private def cntCached367 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached302 cntCached257 cntCached332
private def cntCached368 : T6 := .node cntCached1 cntCached363 cntCached364 cntCached365 cntCached366 cntCached367
private def cntCached369 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached202 cntCached34 cntCached26
private def cntCached370 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached89 cntCached215
private def cntCached371 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached198 cntCached302 cntCached292
private def cntCached372 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached292 cntCached332 cntCached267
private def cntCached373 : T6 := .node cntCached1 cntCached369 cntCached370 cntCached371 cntCached367 cntCached372
private def cntCached374 : T6 := .node cntCached2 cntCached42 cntCached356 cntCached362 cntCached368 cntCached373
private def cntCached375 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached202 cntCached40
private def cntCached376 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached11 cntCached53 cntCached99
private def cntCached377 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached222 cntCached65
private def cntCached378 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached222 cntCached65 cntCached242
private def cntCached379 : T6 := .node cntCached1 cntCached352 cntCached375 cntCached376 cntCached377 cntCached378
private def cntCached380 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached43 cntCached57
private def cntCached381 : T6 := .leaf 54
private def cntCached382 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached21 cntCached94 cntCached381
private def cntCached383 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached94 cntCached292 cntCached304
private def cntCached384 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached381 cntCached304 cntCached146
private def cntCached385 : T6 := .node cntCached1 cntCached358 cntCached380 cntCached382 cntCached383 cntCached384
private def cntCached386 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached32 cntCached53 cntCached60
private def cntCached387 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached53 cntCached99 cntCached381
private def cntCached388 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached94 cntCached292 cntCached304
private def cntCached389 : T6 := .leaf 88
private def cntCached390 : T6 := .leaf 112
private def cntCached391 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached292 cntCached389 cntCached390
private def cntCached392 : T6 := .leaf 136
private def cntCached393 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached304 cntCached390 cntCached392
private def cntCached394 : T6 := .node cntCached1 cntCached386 cntCached387 cntCached388 cntCached391 cntCached393
private def cntCached395 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached60 cntCached139
private def cntCached396 : T6 := .leaf 73
private def cntCached397 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached99 cntCached381 cntCached396
private def cntCached398 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached381 cntCached304 cntCached146
private def cntCached399 : T6 := .leaf 160
private def cntCached400 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached146 cntCached392 cntCached399
private def cntCached401 : T6 := .node cntCached1 cntCached395 cntCached397 cntCached398 cntCached393 cntCached400
private def cntCached402 : T6 := .node cntCached2 cntCached201 cntCached379 cntCached385 cntCached394 cntCached401
private def cntCached403 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached202 cntCached87 cntCached94
private def cntCached404 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached26 cntCached283 cntCached100
private def cntCached405 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached281 cntCached100 cntCached141
private def cntCached406 : T6 := .node cntCached1 cntCached37 cntCached197 cntCached403 cntCached404 cntCached405
private def cntCached407 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached85 cntCached283 cntCached65
private def cntCached408 : T6 := .leaf 83
private def cntCached409 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached57 cntCached72 cntCached408
private def cntCached410 : T6 := .leaf 106
private def cntCached411 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached115 cntCached408 cntCached410
private def cntCached412 : T6 := .node cntCached1 cntCached353 cntCached376 cntCached407 cntCached409 cntCached411
private def cntCached413 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached202 cntCached26 cntCached281
private def cntCached414 : T6 := .node cntCached0 cntCached8 cntCached11 cntCached85 cntCached283 cntCached65
private def cntCached415 : T6 := .node cntCached0 cntCached16 cntCached21 cntCached89 cntCached292 cntCached265
private def cntCached416 : T6 := .leaf 120
private def cntCached417 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached292 cntCached306 cntCached416
private def cntCached418 : T6 := .leaf 147
private def cntCached419 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached265 cntCached416 cntCached418
private def cntCached420 : T6 := .node cntCached1 cntCached413 cntCached414 cntCached415 cntCached417 cntCached419
private def cntCached421 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached283 cntCached100
private def cntCached422 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached57 cntCached72 cntCached408
private def cntCached423 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached292 cntCached306 cntCached416
private def cntCached424 : T6 := .leaf 132
private def cntCached425 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached306 cntCached424 cntCached399
private def cntCached426 : T6 := .leaf 188
private def cntCached427 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached416 cntCached399 cntCached426
private def cntCached428 : T6 := .node cntCached1 cntCached421 cntCached422 cntCached423 cntCached425 cntCached427
private def cntCached429 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached94 cntCached100 cntCached141
private def cntCached430 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached115 cntCached408 cntCached410
private def cntCached431 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached265 cntCached416 cntCached418
private def cntCached432 : T6 := .leaf 105
private def cntCached433 : T6 := .leaf 216
private def cntCached434 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached418 cntCached426 cntCached433
private def cntCached435 : T6 := .node cntCached1 cntCached429 cntCached430 cntCached431 cntCached427 cntCached434
private def cntCached436 : T6 := .node cntCached2 cntCached406 cntCached412 cntCached420 cntCached428 cntCached435
private def cntCached437 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached18 cntCached87 cntCached46
private def cntCached438 : T6 := .leaf 48
private def cntCached439 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached87 cntCached57 cntCached438
private def cntCached440 : T6 := .leaf 66
private def cntCached441 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached283 cntCached110 cntCached440
private def cntCached442 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached100 cntCached440 cntCached304
private def cntCached443 : T6 := .node cntCached1 cntCached39 cntCached437 cntCached439 cntCached441 cntCached442
private def cntCached444 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached26 cntCached222 cntCached65
private def cntCached445 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached57 cntCached72 cntCached408
private def cntCached446 : T6 := .leaf 91
private def cntCached447 : T6 := .leaf 115
private def cntCached448 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached141 cntCached446 cntCached447
private def cntCached449 : T6 := .leaf 139
private def cntCached450 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached265 cntCached447 cntCached449
private def cntCached451 : T6 := .node cntCached1 cntCached354 cntCached444 cntCached445 cntCached448 cntCached450
private def cntCached452 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached283 cntCached100
private def cntCached453 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached72 cntCached408
private def cntCached454 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached102 cntCached125 cntCached342
private def cntCached455 : T6 := .leaf 161
private def cntCached456 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached125 cntCached156 cntCached455
private def cntCached457 : T6 := .leaf 189
private def cntCached458 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached342 cntCached455 cntCached457
private def cntCached459 : T6 := .node cntCached1 cntCached452 cntCached453 cntCached454 cntCached456 cntCached458
private def cntCached460 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached110 cntCached440
private def cntCached461 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached141 cntCached446 cntCached447
private def cntCached462 : T6 := .node cntCached0 cntCached281 cntCached72 cntCached125 cntCached156 cntCached455
private def cntCached463 : T6 := .leaf 90
private def cntCached464 : T6 := .leaf 176
private def cntCached465 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached156 cntCached464 cntCached176
private def cntCached466 : T6 := .leaf 234
private def cntCached467 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached455 cntCached176 cntCached466
private def cntCached468 : T6 := .node cntCached1 cntCached460 cntCached461 cntCached462 cntCached465 cntCached467
private def cntCached469 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached438 cntCached440 cntCached304
private def cntCached470 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached265 cntCached447 cntCached449
private def cntCached471 : T6 := .node cntCached0 cntCached284 cntCached408 cntCached342 cntCached455 cntCached457
private def cntCached472 : T6 := .leaf 138
private def cntCached473 : T6 := .leaf 263
private def cntCached474 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached457 cntCached466 cntCached473
private def cntCached475 : T6 := .node cntCached1 cntCached469 cntCached470 cntCached471 cntCached467 cntCached474
private def cntCached476 : T6 := .node cntCached2 cntCached443 cntCached451 cntCached459 cntCached468 cntCached475
private def cntCached477 : T6 := .node cntCached0 cntCached11 cntCached21 cntCached87 cntCached46 cntCached206
private def cntCached478 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached438 cntCached257
private def cntCached479 : T6 := .leaf 96
private def cntCached480 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached141 cntCached304 cntCached479
private def cntCached481 : T6 := .node cntCached1 cntCached41 cntCached477 cntCached478 cntCached442 cntCached480
private def cntCached482 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached222 cntCached65 cntCached242
private def cntCached483 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached115 cntCached408 cntCached410
private def cntCached484 : T6 := .leaf 163
private def cntCached485 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached274 cntCached449 cntCached484
private def cntCached486 : T6 := .node cntCached1 cntCached355 cntCached482 cntCached483 cntCached450 cntCached485
private def cntCached487 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached100 cntCached141
private def cntCached488 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached408 cntCached410
private def cntCached489 : T6 := .leaf 148
private def cntCached490 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached258 cntCached342 cntCached489
private def cntCached491 : T6 := .leaf 217
private def cntCached492 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached489 cntCached457 cntCached491
private def cntCached493 : T6 := .node cntCached1 cntCached487 cntCached488 cntCached490 cntCached458 cntCached492
private def cntCached494 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached257 cntCached304 cntCached479
private def cntCached495 : T6 := .node cntCached0 cntCached69 cntCached253 cntCached274 cntCached449 cntCached484
private def cntCached496 : T6 := .node cntCached0 cntCached102 cntCached410 cntCached489 cntCached457 cntCached491
private def cntCached497 : T6 := .leaf 162
private def cntCached498 : T6 := .leaf 292
private def cntCached499 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached491 cntCached473 cntCached498
private def cntCached500 : T6 := .node cntCached1 cntCached494 cntCached495 cntCached496 cntCached474 cntCached499
private def cntCached501 : T6 := .node cntCached2 cntCached481 cntCached486 cntCached493 cntCached475 cntCached500
private def cntCached502 : T6 := .node cntCached3 cntCached374 cntCached402 cntCached436 cntCached476 cntCached501
private def cntCached503 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached8 cntCached16
private def cntCached504 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached11 cntCached32 cntCached43
private def cntCached505 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached26 cntCached198
private def cntCached506 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached281 cntCached96
private def cntCached507 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached46 cntCached96 cntCached65
private def cntCached508 : T6 := .node cntCached1 cntCached503 cntCached504 cntCached505 cntCached506 cntCached507
private def cntCached509 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached26 cntCached94 cntCached62
private def cntCached510 : T6 := .leaf 49
private def cntCached511 : T6 := .leaf 64
private def cntCached512 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached510 cntCached511
private def cntCached513 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached62 cntCached511 cntCached235
private def cntCached514 : T6 := .node cntCached1 cntCached363 cntCached386 cntCached509 cntCached512 cntCached513
private def cntCached515 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached34 cntCached87
private def cntCached516 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached198 cntCached206
private def cntCached517 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached281 cntCached438 cntCached296
private def cntCached518 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached438 cntCached340 cntCached265
private def cntCached519 : T6 := .leaf 100
private def cntCached520 : T6 := .node cntCached0 cntCached92 cntCached324 cntCached296 cntCached265 cntCached519
private def cntCached521 : T6 := .node cntCached1 cntCached515 cntCached516 cntCached517 cntCached518 cntCached520
private def cntCached522 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached34 cntCached87 cntCached55
private def cntCached523 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached60 cntCached206 cntCached208
private def cntCached524 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached284 cntCached296 cntCached124
private def cntCached525 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached124 cntCached519 cntCached268
private def cntCached526 : T6 := .node cntCached1 cntCached522 cntCached523 cntCached524 cntCached520 cntCached525
private def cntCached527 : T6 := .node cntCached2 cntCached48 cntCached508 cntCached514 cntCached521 cntCached526
private def cntCached528 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached26 cntCached281 cntCached96
private def cntCached529 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached198 cntCached96 cntCached65
private def cntCached530 : T6 := .node cntCached1 cntCached33 cntCached193 cntCached248 cntCached528 cntCached529
private def cntCached531 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached202 cntCached38
private def cntCached532 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached202 cntCached26 cntCached283
private def cntCached533 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached53 cntCached99 cntCached381
private def cntCached534 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached222 cntCached292 cntCached124
private def cntCached535 : T6 := .leaf 98
private def cntCached536 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached124 cntCached535
private def cntCached537 : T6 := .node cntCached1 cntCached531 cntCached532 cntCached533 cntCached534 cntCached536
private def cntCached538 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached43 cntCached57 cntCached208
private def cntCached539 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached94 cntCached292 cntCached304
private def cntCached540 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached292 cntCached389 cntCached390
private def cntCached541 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached304 cntCached390 cntCached392
private def cntCached542 : T6 := .node cntCached1 cntCached364 cntCached538 cntCached539 cntCached540 cntCached541
private def cntCached543 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached99 cntCached251 cntCached332
private def cntCached544 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached292 cntCached389 cntCached390
private def cntCached545 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached389 cntCached148 cntCached418
private def cntCached546 : T6 := .leaf 172
private def cntCached547 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached390 cntCached418 cntCached546
private def cntCached548 : T6 := .node cntCached1 cntCached516 cntCached543 cntCached544 cntCached545 cntCached547
private def cntCached549 : T6 := .leaf 97
private def cntCached550 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached381 cntCached332 cntCached549
private def cntCached551 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached304 cntCached390 cntCached392
private def cntCached552 : T6 := .leaf 197
private def cntCached553 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached392 cntCached546 cntCached552
private def cntCached554 : T6 := .node cntCached1 cntCached523 cntCached550 cntCached551 cntCached547 cntCached553
private def cntCached555 : T6 := .node cntCached2 cntCached530 cntCached537 cntCached542 cntCached548 cntCached554
private def cntCached556 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached94 cntCached70 cntCached112
private def cntCached557 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached62 cntCached112 cntCached79
private def cntCached558 : T6 := .node cntCached1 cntCached39 cntCached199 cntCached404 cntCached556 cntCached557
private def cntCached559 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached32 cntCached53 cntCached60
private def cntCached560 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached43 cntCached57 cntCached208
private def cntCached561 : T6 := .leaf 89
private def cntCached562 : T6 := .leaf 113
private def cntCached563 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached102 cntCached561 cntCached562
private def cntCached564 : T6 := .leaf 137
private def cntCached565 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached290 cntCached562 cntCached564
private def cntCached566 : T6 := .node cntCached1 cntCached559 cntCached560 cntCached383 cntCached563 cntCached565
private def cntCached567 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached94 cntCached62
private def cntCached568 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached251 cntCached267 cntCached244
private def cntCached569 : T6 := .leaf 131
private def cntCached570 : T6 := .leaf 159
private def cntCached571 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached267 cntCached569 cntCached570
private def cntCached572 : T6 := .leaf 187
private def cntCached573 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached244 cntCached570 cntCached572
private def cntCached574 : T6 := .node cntCached1 cntCached567 cntCached539 cntCached568 cntCached571 cntCached573
private def cntCached575 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached283 cntCached70 cntCached112
private def cntCached576 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached102 cntCached561 cntCached562
private def cntCached577 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached267 cntCached569 cntCached570
private def cntCached578 : T6 := .leaf 174
private def cntCached579 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached569 cntCached578 cntCached319
private def cntCached580 : T6 := .leaf 232
private def cntCached581 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached570 cntCached319 cntCached580
private def cntCached582 : T6 := .node cntCached1 cntCached575 cntCached576 cntCached577 cntCached579 cntCached581
private def cntCached583 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached100 cntCached112 cntCached79
private def cntCached584 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached290 cntCached562 cntCached564
private def cntCached585 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached244 cntCached570 cntCached572
private def cntCached586 : T6 := .leaf 261
private def cntCached587 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached572 cntCached580 cntCached586
private def cntCached588 : T6 := .node cntCached1 cntCached583 cntCached584 cntCached585 cntCached581 cntCached587
private def cntCached589 : T6 := .node cntCached2 cntCached558 cntCached566 cntCached574 cntCached582 cntCached588
private def cntCached590 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached26 cntCached281 cntCached96
private def cntCached591 : T6 := .leaf 87
private def cntCached592 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached70 cntCached105 cntCached591
private def cntCached593 : T6 := .leaf 103
private def cntCached594 : T6 := .node cntCached0 cntCached87 cntCached206 cntCached112 cntCached591 cntCached593
private def cntCached595 : T6 := .node cntCached1 cntCached45 cntCached590 cntCached441 cntCached592 cntCached594
private def cntCached596 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached46 cntCached324
private def cntCached597 : T6 := .node cntCached0 cntCached202 cntCached87 cntCached99 cntCached251 cntCached332
private def cntCached598 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached102 cntCached561 cntCached562
private def cntCached599 : T6 := .leaf 124
private def cntCached600 : T6 := .leaf 149
private def cntCached601 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached463 cntCached599 cntCached600
private def cntCached602 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached155 cntCached600 cntCached578
private def cntCached603 : T6 := .node cntCached1 cntCached596 cntCached597 cntCached598 cntCached601 cntCached602
private def cntCached604 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached283 cntCached70 cntCached112
private def cntCached605 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached102 cntCached561 cntCached562
private def cntCached606 : T6 := .leaf 175
private def cntCached607 : T6 := .leaf 204
private def cntCached608 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached424 cntCached606 cntCached607
private def cntCached609 : T6 := .leaf 233
private def cntCached610 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached399 cntCached607 cntCached609
private def cntCached611 : T6 := .node cntCached1 cntCached604 cntCached605 cntCached425 cntCached608 cntCached610
private def cntCached612 : T6 := .node cntCached0 cntCached43 cntCached283 cntCached110 cntCached105 cntCached591
private def cntCached613 : T6 := .node cntCached0 cntCached46 cntCached72 cntCached463 cntCached599 cntCached600
private def cntCached614 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached424 cntCached606 cntCached607
private def cntCached615 : T6 := .leaf 222
private def cntCached616 : T6 := .leaf 252
private def cntCached617 : T6 := .node cntCached0 cntCached340 cntCached599 cntCached606 cntCached615 cntCached616
private def cntCached618 : T6 := .leaf 282
private def cntCached619 : T6 := .node cntCached0 cntCached265 cntCached600 cntCached607 cntCached616 cntCached618
private def cntCached620 : T6 := .node cntCached1 cntCached612 cntCached613 cntCached614 cntCached617 cntCached619
private def cntCached621 : T6 := .node cntCached0 cntCached44 cntCached284 cntCached440 cntCached591 cntCached593
private def cntCached622 : T6 := .node cntCached0 cntCached324 cntCached79 cntCached155 cntCached600 cntCached578
private def cntCached623 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached399 cntCached607 cntCached609
private def cntCached624 : T6 := .leaf 312
private def cntCached625 : T6 := .node cntCached0 cntCached519 cntCached578 cntCached609 cntCached618 cntCached624
private def cntCached626 : T6 := .node cntCached1 cntCached621 cntCached622 cntCached623 cntCached619 cntCached625
private def cntCached627 : T6 := .node cntCached2 cntCached595 cntCached603 cntCached611 cntCached620 cntCached626
private def cntCached628 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached198 cntCached96 cntCached65
private def cntCached629 : T6 := .node cntCached0 cntCached55 cntCached208 cntCached79 cntCached593 cntCached244
private def cntCached630 : T6 := .node cntCached1 cntCached47 cntCached628 cntCached442 cntCached594 cntCached629
private def cntCached631 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached198 cntCached324 cntCached381
private def cntCached632 : T6 := .node cntCached0 cntCached38 cntCached57 cntCached381 cntCached332 cntCached549
private def cntCached633 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached290 cntCached562 cntCached564
private def cntCached634 : T6 := .leaf 199
private def cntCached635 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached472 cntCached578 cntCached634
private def cntCached636 : T6 := .node cntCached1 cntCached631 cntCached632 cntCached633 cntCached602 cntCached635
private def cntCached637 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached100 cntCached112 cntCached79
private def cntCached638 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached290 cntCached562 cntCached564
private def cntCached639 : T6 := .leaf 262
private def cntCached640 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached426 cntCached609 cntCached639
private def cntCached641 : T6 := .node cntCached1 cntCached637 cntCached638 cntCached427 cntCached610 cntCached640
private def cntCached642 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached304 cntCached593 cntCached244
private def cntCached643 : T6 := .node cntCached0 cntCached381 cntCached519 cntCached472 cntCached578 cntCached634
private def cntCached644 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached426 cntCached609 cntCached639
private def cntCached645 : T6 := .leaf 342
private def cntCached646 : T6 := .node cntCached0 cntCached268 cntCached634 cntCached639 cntCached624 cntCached645
private def cntCached647 : T6 := .node cntCached1 cntCached642 cntCached643 cntCached644 cntCached625 cntCached646
private def cntCached648 : T6 := .node cntCached2 cntCached630 cntCached636 cntCached641 cntCached626 cntCached647
private def cntCached649 : T6 := .node cntCached3 cntCached527 cntCached555 cntCached589 cntCached627 cntCached648
private def cntCached650 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached21 cntCached43 cntCached212
private def cntCached651 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached87 cntCached198 cntCached69
private def cntCached652 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached206 cntCached65 cntCached345
private def cntCached653 : T6 := .node cntCached1 cntCached22 cntCached650 cntCached651 cntCached507 cntCached652
private def cntCached654 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached281 cntCached62 cntCached72
private def cntCached655 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached72 cntCached235 cntCached125
private def cntCached656 : T6 := .node cntCached1 cntCached369 cntCached395 cntCached654 cntCached513 cntCached655
private def cntCached657 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached26 cntCached55 cntCached283
private def cntCached658 : T6 := .node cntCached0 cntCached34 cntCached55 cntCached139 cntCached208 cntCached112
private def cntCached659 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached102 cntCached124 cntCached306
private def cntCached660 : T6 := .node cntCached0 cntCached57 cntCached440 cntCached306 cntCached268 cntCached424
private def cntCached661 : T6 := .node cntCached1 cntCached657 cntCached658 cntCached659 cntCached525 cntCached660
private def cntCached662 : T6 := .node cntCached2 cntCached51 cntCached653 cntCached656 cntCached526 cntCached661
private def cntCached663 : T6 := .node cntCached0 cntCached85 cntCached212 cntCached69 cntCached65 cntCached345
private def cntCached664 : T6 := .node cntCached1 cntCached35 cntCached195 cntCached249 cntCached529 cntCached663
private def cntCached665 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached18 cntCached38 cntCached44
private def cntCached666 : T6 := .node cntCached0 cntCached30 cntCached34 cntCached40 cntCached283 cntCached438
private def cntCached667 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached99 cntCached381 cntCached396
private def cntCached668 : T6 := .node cntCached0 cntCached194 cntCached70 cntCached242 cntCached535 cntCached298
private def cntCached669 : T6 := .node cntCached1 cntCached665 cntCached666 cntCached667 cntCached536 cntCached668
private def cntCached670 : T6 := .leaf 72
private def cntCached671 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached57 cntCached208 cntCached670
private def cntCached672 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached304 cntCached146
private def cntCached673 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached146 cntCached392 cntCached399
private def cntCached674 : T6 := .node cntCached1 cntCached370 cntCached671 cntCached672 cntCached541 cntCached673
private def cntCached675 : T6 := .node cntCached0 cntCached194 cntCached110 cntCached396 cntCached549 cntCached307
private def cntCached676 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached146 cntCached392 cntCached399
private def cntCached677 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached399 cntCached552 cntCached615
private def cntCached678 : T6 := .node cntCached1 cntCached658 cntCached675 cntCached676 cntCached553 cntCached677
private def cntCached679 : T6 := .node cntCached2 cntCached664 cntCached669 cntCached674 cntCached554 cntCached678
private def cntCached680 : T6 := .node cntCached0 cntCached26 cntCached215 cntCached72 cntCached79 cntCached143
private def cntCached681 : T6 := .node cntCached1 cntCached41 cntCached200 cntCached405 cntCached557 cntCached680
private def cntCached682 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached26 cntCached60 cntCached139
private def cntCached683 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached208 cntCached670
private def cntCached684 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached432 cntCached564 cntCached455
private def cntCached685 : T6 := .node cntCached1 cntCached682 cntCached683 cntCached384 cntCached565 cntCached684
private def cntCached686 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached281 cntCached62 cntCached72
private def cntCached687 : T6 := .leaf 146
private def cntCached688 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached408 cntCached244 cntCached687
private def cntCached689 : T6 := .leaf 215
private def cntCached690 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached687 cntCached572 cntCached689
private def cntCached691 : T6 := .node cntCached1 cntCached686 cntCached672 cntCached688 cntCached573 cntCached690
private def cntCached692 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached141 cntCached79 cntCached143
private def cntCached693 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached432 cntCached564 cntCached455
private def cntCached694 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached687 cntCached572 cntCached689
private def cntCached695 : T6 := .leaf 290
private def cntCached696 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached689 cntCached586 cntCached695
private def cntCached697 : T6 := .node cntCached1 cntCached692 cntCached693 cntCached694 cntCached587 cntCached696
private def cntCached698 : T6 := .node cntCached2 cntCached681 cntCached685 cntCached691 cntCached588 cntCached697
private def cntCached699 : T6 := .node cntCached0 cntCached21 cntCached212 cntCached69 cntCached65 cntCached345
private def cntCached700 : T6 := .leaf 135
private def cntCached701 : T6 := .node cntCached0 cntCached283 cntCached112 cntCached143 cntCached244 cntCached700
private def cntCached702 : T6 := .node cntCached1 cntCached50 cntCached699 cntCached480 cntCached629 cntCached701
private def cntCached703 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached69 cntCached381 cntCached440
private def cntCached704 : T6 := .node cntCached0 cntCached44 cntCached510 cntCached396 cntCached549 cntCached307
private def cntCached705 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached432 cntCached564 cntCached455
private def cntCached706 : T6 := .leaf 224
private def cntCached707 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached497 cntCached634 cntCached706
private def cntCached708 : T6 := .node cntCached1 cntCached703 cntCached704 cntCached705 cntCached635 cntCached707
private def cntCached709 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached141 cntCached79 cntCached143
private def cntCached710 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached432 cntCached564 cntCached455
private def cntCached711 : T6 := .leaf 291
private def cntCached712 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached433 cntCached639 cntCached711
private def cntCached713 : T6 := .node cntCached1 cntCached709 cntCached710 cntCached434 cntCached640 cntCached712
private def cntCached714 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached479 cntCached244 cntCached700
private def cntCached715 : T6 := .node cntCached0 cntCached440 cntCached416 cntCached497 cntCached634 cntCached706
private def cntCached716 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached433 cntCached639 cntCached711
private def cntCached717 : T6 := .leaf 372
private def cntCached718 : T6 := .node cntCached0 cntCached424 cntCached706 cntCached711 cntCached645 cntCached717
private def cntCached719 : T6 := .node cntCached1 cntCached714 cntCached715 cntCached716 cntCached646 cntCached718
private def cntCached720 : T6 := .node cntCached2 cntCached702 cntCached708 cntCached713 cntCached647 cntCached719
private def cntCached721 : T6 := .node cntCached3 cntCached662 cntCached679 cntCached698 cntCached648 cntCached720
private def cntCached722 : T6 := .node cntCached4 cntCached138 cntCached350 cntCached502 cntCached649 cntCached721
private def cntCached723 : T6 := .node cntCached0 cntCached0 cntCached8 cntCached16 cntCached38 cntCached55
private def cntCached724 : T6 := .node cntCached0 cntCached6 cntCached16 cntCached38 cntCached198 cntCached96
private def cntCached725 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached198 cntCached62 cntCached141
private def cntCached726 : T6 := .node cntCached0 cntCached85 cntCached55 cntCached96 cntCached141 cntCached253
private def cntCached727 : T6 := .node cntCached1 cntCached363 cntCached723 cntCached724 cntCached725 cntCached726
private def cntCached728 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached43 cntCached55 cntCached49
private def cntCached729 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached60 cntCached96 cntCached251
private def cntCached730 : T6 := .node cntCached0 cntCached53 cntCached49 cntCached251 cntCached253 cntCached446
private def cntCached731 : T6 := .node cntCached1 cntCached369 cntCached728 cntCached729 cntCached726 cntCached730
private def cntCached732 : T6 := .node cntCached2 cntCached42 cntCached356 cntCached362 cntCached727 cntCached731
private def cntCached733 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached49 cntCached115
private def cntCached734 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached49 cntCached115 cntCached229
private def cntCached735 : T6 := .node cntCached1 cntCached352 cntCached375 cntCached376 cntCached733 cntCached734
private def cntCached736 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached283 cntCached102 cntCached290
private def cntCached737 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached290 cntCached432
private def cntCached738 : T6 := .node cntCached1 cntCached358 cntCached380 cntCached382 cntCached736 cntCached737
private def cntCached739 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached43 cntCached57 cntCached208
private def cntCached740 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached281 cntCached251 cntCached79
private def cntCached741 : T6 := .node cntCached1 cntCached386 cntCached739 cntCached740 cntCached391 cntCached393
private def cntCached742 : T6 := .node cntCached0 cntCached18 cntCached220 cntCached57 cntCached208 cntCached670
private def cntCached743 : T6 := .node cntCached0 cntCached43 cntCached57 cntCached208 cntCached79 cntCached593
private def cntCached744 : T6 := .node cntCached1 cntCached395 cntCached742 cntCached743 cntCached393 cntCached400
private def cntCached745 : T6 := .node cntCached2 cntCached250 cntCached735 cntCached738 cntCached741 cntCached744
private def cntCached746 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached87 cntCached57 cntCached438
private def cntCached747 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached94 cntCached438 cntCached257
private def cntCached748 : T6 := .node cntCached1 cntCached37 cntCached197 cntCached403 cntCached746 cntCached747
private def cntCached749 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached99 cntCached141 cntCached265
private def cntCached750 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached251 cntCached265 cntCached274
private def cntCached751 : T6 := .node cntCached1 cntCached353 cntCached376 cntCached407 cntCached749 cntCached750
private def cntCached752 : T6 := .node cntCached0 cntCached26 cntCached283 cntCached102 cntCached125 cntCached342
private def cntCached753 : T6 := .node cntCached0 cntCached281 cntCached65 cntCached258 cntCached342 cntCached489
private def cntCached754 : T6 := .node cntCached1 cntCached413 cntCached414 cntCached415 cntCached752 cntCached753
private def cntCached755 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached283 cntCached102 cntCached290
private def cntCached756 : T6 := .node cntCached0 cntCached43 cntCached94 cntCached251 cntCached267 cntCached244
private def cntCached757 : T6 := .node cntCached1 cntCached421 cntCached755 cntCached756 cntCached425 cntCached427
private def cntCached758 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached65 cntCached290 cntCached432
private def cntCached759 : T6 := .node cntCached0 cntCached198 cntCached381 cntCached408 cntCached244 cntCached687
private def cntCached760 : T6 := .node cntCached1 cntCached429 cntCached758 cntCached759 cntCached427 cntCached434
private def cntCached761 : T6 := .node cntCached2 cntCached748 cntCached751 cntCached754 cntCached757 cntCached760
private def cntCached762 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached92 cntCached99 cntCached510
private def cntCached763 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached99 cntCached208 cntCached340
private def cntCached764 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached510 cntCached340 cntCached408
private def cntCached765 : T6 := .node cntCached1 cntCached39 cntCached282 cntCached762 cntCached763 cntCached764
private def cntCached766 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached87 cntCached49 cntCached115
private def cntCached767 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached99 cntCached141 cntCached265
private def cntCached768 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached296 cntCached306 cntCached307
private def cntCached769 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached117 cntCached307 cntCached317
private def cntCached770 : T6 := .node cntCached1 cntCached354 cntCached766 cntCached767 cntCached768 cntCached769
private def cntCached771 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached99 cntCached141 cntCached265
private def cntCached772 : T6 := .node cntCached0 cntCached26 cntCached57 cntCached72 cntCached143 cntCached148
private def cntCached773 : T6 := .node cntCached0 cntCached283 cntCached141 cntCached479 cntCached700 cntCached484
private def cntCached774 : T6 := .leaf 123
private def cntCached775 : T6 := .leaf 191
private def cntCached776 : T6 := .node cntCached0 cntCached100 cntCached265 cntCached774 cntCached484 cntCached775
private def cntCached777 : T6 := .node cntCached1 cntCached452 cntCached771 cntCached772 cntCached773 cntCached776
private def cntCached778 : T6 := .leaf 134
private def cntCached779 : T6 := .leaf 177
private def cntCached780 : T6 := .leaf 206
private def cntCached781 : T6 := .node cntCached0 cntCached510 cntCached446 cntCached778 cntCached779 cntCached780
private def cntCached782 : T6 := .leaf 235
private def cntCached783 : T6 := .node cntCached0 cntCached511 cntCached447 cntCached497 cntCached780 cntCached782
private def cntCached784 : T6 := .node cntCached1 cntCached460 cntCached461 cntCached462 cntCached781 cntCached783
private def cntCached785 : T6 := .leaf 264
private def cntCached786 : T6 := .node cntCached0 cntCached235 cntCached449 cntCached165 cntCached782 cntCached785
private def cntCached787 : T6 := .node cntCached1 cntCached469 cntCached470 cntCached471 cntCached783 cntCached786
private def cntCached788 : T6 := .node cntCached2 cntCached765 cntCached770 cntCached777 cntCached784 cntCached787
private def cntCached789 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached283 cntCached510 cntCached296
private def cntCached790 : T6 := .node cntCached0 cntCached92 cntCached206 cntCached296 cntCached408 cntCached535
private def cntCached791 : T6 := .node cntCached1 cntCached41 cntCached325 cntCached789 cntCached764 cntCached790
private def cntCached792 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached49 cntCached115 cntCached229
private def cntCached793 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached251 cntCached265 cntCached274
private def cntCached794 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached335 cntCached317 cntCached171
private def cntCached795 : T6 := .node cntCached1 cntCached355 cntCached792 cntCached793 cntCached769 cntCached794
private def cntCached796 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached251 cntCached265 cntCached274
private def cntCached797 : T6 := .node cntCached0 cntCached281 cntCached115 cntCached117 cntCached148 cntCached600
private def cntCached798 : T6 := .leaf 150
private def cntCached799 : T6 := .leaf 219
private def cntCached800 : T6 := .node cntCached0 cntCached141 cntCached274 cntCached798 cntCached775 cntCached799
private def cntCached801 : T6 := .node cntCached1 cntCached487 cntCached796 cntCached797 cntCached776 cntCached800
private def cntCached802 : T6 := .leaf 218
private def cntCached803 : T6 := .leaf 293
private def cntCached804 : T6 := .node cntCached0 cntCached125 cntCached484 cntCached802 cntCached785 cntCached803
private def cntCached805 : T6 := .node cntCached1 cntCached494 cntCached495 cntCached496 cntCached786 cntCached804
private def cntCached806 : T6 := .node cntCached2 cntCached791 cntCached795 cntCached801 cntCached787 cntCached805
private def cntCached807 : T6 := .node cntCached3 cntCached732 cntCached745 cntCached761 cntCached788 cntCached806
private def cntCached808 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached0 cntCached6 cntCached16
private def cntCached809 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached6 cntCached16 cntCached43
private def cntCached810 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached202 cntCached53 cntCached46
private def cntCached811 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached94 cntCached62
private def cntCached812 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached62 cntCached72
private def cntCached813 : T6 := .node cntCached1 cntCached808 cntCached809 cntCached810 cntCached811 cntCached812
private def cntCached814 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached6 cntCached13 cntCached34
private def cntCached815 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached30 cntCached23 cntCached89
private def cntCached816 : T6 := .node cntCached0 cntCached6 cntCached13 cntCached23 cntCached46 cntCached62
private def cntCached817 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached281 cntCached70 cntCached345
private def cntCached818 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached100 cntCached345 cntCached265
private def cntCached819 : T6 := .node cntCached1 cntCached814 cntCached815 cntCached816 cntCached817 cntCached818
private def cntCached820 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached34 cntCached92
private def cntCached821 : T6 := .node cntCached0 cntCached8 cntCached202 cntCached23 cntCached89 cntCached206
private def cntCached822 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached198 cntCached438 cntCached112
private def cntCached823 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached510 cntCached105 cntCached561
private def cntCached824 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached440 cntCached561 cntCached274
private def cntCached825 : T6 := .node cntCached1 cntCached820 cntCached821 cntCached822 cntCached823 cntCached824
private def cntCached826 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached224 cntCached92 cntCached60
private def cntCached827 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached89 cntCached206 cntCached65
private def cntCached828 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached284 cntCached112 cntCached290
private def cntCached829 : T6 := .leaf 125
private def cntCached830 : T6 := .node cntCached0 cntCached60 cntCached251 cntCached408 cntCached274 cntCached829
private def cntCached831 : T6 := .node cntCached1 cntCached826 cntCached827 cntCached828 cntCached824 cntCached830
private def cntCached832 : T6 := .node cntCached2 cntCached59 cntCached813 cntCached819 cntCached825 cntCached831
private def cntCached833 : T6 := .node cntCached0 cntCached0 cntCached0 cntCached8 cntCached38 cntCached283
private def cntCached834 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached21 cntCached281 cntCached208
private def cntCached835 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached283 cntCached292 cntCached304
private def cntCached836 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached304 cntCached146
private def cntCached837 : T6 := .node cntCached1 cntCached809 cntCached833 cntCached834 cntCached835 cntCached836
private def cntCached838 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached13 cntCached38 cntCached60
private def cntCached839 : T6 := .node cntCached0 cntCached6 cntCached8 cntCached32 cntCached198 cntCached110
private def cntCached840 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached44 cntCached208 cntCached235
private def cntCached841 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached381 cntCached389 cntCached447
private def cntCached842 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached79 cntCached447 cntCached134
private def cntCached843 : T6 := .node cntCached1 cntCached838 cntCached839 cntCached840 cntCached841 cntCached842
private def cntCached844 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached46 cntCached302
private def cntCached845 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached46 cntCached65 cntCached124
private def cntCached846 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached208 cntCached591 cntCached155
private def cntCached847 : T6 := .leaf 154
private def cntCached848 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached389 cntCached130 cntCached847
private def cntCached849 : T6 := .leaf 182
private def cntCached850 : T6 := .node cntCached0 cntCached324 cntCached235 cntCached447 cntCached847 cntCached849
private def cntCached851 : T6 := .node cntCached1 cntCached844 cntCached845 cntCached846 cntCached848 cntCached850
private def cntCached852 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached46 cntCached302 cntCached292
private def cntCached853 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached331 cntCached124 cntCached120
private def cntCached854 : T6 := .node cntCached0 cntCached89 cntCached331 cntCached235 cntCached155 cntCached317
private def cntCached855 : T6 := .leaf 210
private def cntCached856 : T6 := .node cntCached0 cntCached115 cntCached293 cntCached134 cntCached849 cntCached855
private def cntCached857 : T6 := .node cntCached1 cntCached852 cntCached853 cntCached854 cntCached850 cntCached856
private def cntCached858 : T6 := .node cntCached2 cntCached406 cntCached837 cntCached843 cntCached851 cntCached857
private def cntCached859 : T6 := .node cntCached0 cntCached0 cntCached30 cntCached43 cntCached57 cntCached70
private def cntCached860 : T6 := .node cntCached0 cntCached13 cntCached38 cntCached283 cntCached381 cntCached105
private def cntCached861 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached510 cntCached105 cntCached389
private def cntCached862 : T6 := .node cntCached1 cntCached54 cntCached403 cntCached859 cntCached860 cntCached861
private def cntCached863 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached194 cntCached65 cntCached304
private def cntCached864 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached251 cntCached446 cntCached298
private def cntCached865 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached408 cntCached298 cntCached170
private def cntCached866 : T6 := .node cntCached1 cntCached810 cntCached834 cntCached863 cntCached864 cntCached865
private def cntCached867 : T6 := .node cntCached0 cntCached30 cntCached32 cntCached53 cntCached283 cntCached510
private def cntCached868 : T6 := .node cntCached0 cntCached16 cntCached21 cntCached194 cntCached65 cntCached304
private def cntCached869 : T6 := .node cntCached0 cntCached224 cntCached44 cntCached70 cntCached463 cntCached416
private def cntCached870 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached446 cntCached700 cntCached337
private def cntCached871 : T6 := .node cntCached0 cntCached62 cntCached79 cntCached342 cntCached337 cntCached552
private def cntCached872 : T6 := .node cntCached1 cntCached867 cntCached868 cntCached869 cntCached870 cntCached871
private def cntCached873 : T6 := .node cntCached0 cntCached21 cntCached40 cntCached99 cntCached381 cntCached105
private def cntCached874 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached115 cntCached463 cntCached307
private def cntCached875 : T6 := .node cntCached0 cntCached198 cntCached381 cntCached463 cntCached778 cntCached171
private def cntCached876 : T6 := .leaf 183
private def cntCached877 : T6 := .node cntCached0 cntCached510 cntCached561 cntCached700 cntCached876 cntCached689
private def cntCached878 : T6 := .leaf 247
private def cntCached879 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached337 cntCached689 cntCached878
private def cntCached880 : T6 := .node cntCached1 cntCached873 cntCached874 cntCached875 cntCached877 cntCached879
private def cntCached881 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached110 cntCached105 cntCached389
private def cntCached882 : T6 := .leaf 144
private def cntCached883 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached290 cntCached307 cntCached882
private def cntCached884 : T6 := .leaf 196
private def cntCached885 : T6 := .node cntCached0 cntCached284 cntCached79 cntCached416 cntCached171 cntCached884
private def cntCached886 : T6 := .leaf 143
private def cntCached887 : T6 := .leaf 279
private def cntCached888 : T6 := .node cntCached0 cntCached408 cntCached886 cntCached552 cntCached878 cntCached887
private def cntCached889 : T6 := .node cntCached1 cntCached881 cntCached883 cntCached885 cntCached879 cntCached888
private def cntCached890 : T6 := .node cntCached2 cntCached862 cntCached866 cntCached872 cntCached880 cntCached889
private def cntCached891 : T6 := .node cntCached0 cntCached13 cntCached43 cntCached57 cntCached65 cntCached670
private def cntCached892 : T6 := .node cntCached0 cntCached34 cntCached46 cntCached381 cntCached124 cntCached479
private def cntCached893 : T6 := .node cntCached0 cntCached92 cntCached302 cntCached105 cntCached479 cntCached155
private def cntCached894 : T6 := .node cntCached1 cntCached56 cntCached439 cntCached891 cntCached892 cntCached893
private def cntCached895 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached283 cntCached292 cntCached304
private def cntCached896 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached251 cntCached446 cntCached298
private def cntCached897 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached306 cntCached569 cntCached570
private def cntCached898 : T6 := .node cntCached0 cntCached302 cntCached304 cntCached416 cntCached570 cntCached572
private def cntCached899 : T6 := .node cntCached1 cntCached811 cntCached895 cntCached896 cntCached897 cntCached898
private def cntCached900 : T6 := .node cntCached0 cntCached21 cntCached92 cntCached99 cntCached381 cntCached105
private def cntCached901 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached251 cntCached446 cntCached298
private def cntCached902 : T6 := .leaf 167
private def cntCached903 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached267 cntCached392 cntCached902
private def cntCached904 : T6 := .node cntCached0 cntCached70 cntCached463 cntCached564 cntCached173 cntCached491
private def cntCached905 : T6 := .leaf 168
private def cntCached906 : T6 := .leaf 249
private def cntCached907 : T6 := .node cntCached0 cntCached345 cntCached307 cntCached905 cntCached491 cntCached906
private def cntCached908 : T6 := .node cntCached1 cntCached900 cntCached901 cntCached903 cntCached904 cntCached907
private def cntCached909 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached115 cntCached124 cntCached479
private def cntCached910 : T6 := .leaf 130
private def cntCached911 : T6 := .leaf 158
private def cntCached912 : T6 := .node cntCached0 cntCached281 cntCached72 cntCached267 cntCached910 cntCached911
private def cntCached913 : T6 := .leaf 184
private def cntCached914 : T6 := .node cntCached0 cntCached510 cntCached463 cntCached392 cntCached913 cntCached433
private def cntCached915 : T6 := .leaf 129
private def cntCached916 : T6 := .leaf 237
private def cntCached917 : T6 := .leaf 270
private def cntCached918 : T6 := .node cntCached0 cntCached670 cntCached915 cntCached173 cntCached916 cntCached917
private def cntCached919 : T6 := .leaf 157
private def cntCached920 : T6 := .leaf 303
private def cntCached921 : T6 := .node cntCached0 cntCached463 cntCached919 cntCached491 cntCached917 cntCached920
private def cntCached922 : T6 := .node cntCached1 cntCached909 cntCached912 cntCached914 cntCached918 cntCached921
private def cntCached923 : T6 := .node cntCached0 cntCached55 cntCached70 cntCached396 cntCached479 cntCached155
private def cntCached924 : T6 := .leaf 186
private def cntCached925 : T6 := .node cntCached0 cntCached284 cntCached408 cntCached244 cntCached911 cntCached924
private def cntCached926 : T6 := .leaf 248
private def cntCached927 : T6 := .node cntCached0 cntCached440 cntCached307 cntCached902 cntCached433 cntCached926
private def cntCached928 : T6 := .leaf 336
private def cntCached929 : T6 := .node cntCached0 cntCached260 cntCached173 cntCached906 cntCached920 cntCached928
private def cntCached930 : T6 := .node cntCached1 cntCached923 cntCached925 cntCached927 cntCached921 cntCached929
private def cntCached931 : T6 := .node cntCached2 cntCached894 cntCached899 cntCached908 cntCached922 cntCached930
private def cntCached932 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached70 cntCached670 cntCached561
private def cntCached933 : T6 := .node cntCached0 cntCached60 cntCached292 cntCached389 cntCached155 cntCached424
private def cntCached934 : T6 := .node cntCached1 cntCached58 cntCached478 cntCached932 cntCached893 cntCached933
private def cntCached935 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached304 cntCached146
private def cntCached936 : T6 := .node cntCached0 cntCached60 cntCached208 cntCached408 cntCached298 cntCached170
private def cntCached937 : T6 := .node cntCached0 cntCached292 cntCached146 cntCached418 cntCached572 cntCached689
private def cntCached938 : T6 := .node cntCached1 cntCached812 cntCached935 cntCached936 cntCached898 cntCached937
private def cntCached939 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached110 cntCached105 cntCached389
private def cntCached940 : T6 := .node cntCached0 cntCached46 cntCached65 cntCached408 cntCached298 cntCached170
private def cntCached941 : T6 := .leaf 198
private def cntCached942 : T6 := .node cntCached0 cntCached62 cntCached304 cntCached148 cntCached902 cntCached941
private def cntCached943 : T6 := .leaf 281
private def cntCached944 : T6 := .node cntCached0 cntCached265 cntCached882 cntCached634 cntCached906 cntCached943
private def cntCached945 : T6 := .node cntCached1 cntCached939 cntCached940 cntCached942 cntCached907 cntCached944
private def cntCached946 : T6 := .node cntCached0 cntCached57 cntCached511 cntCached463 cntCached155 cntCached424
private def cntCached947 : T6 := .leaf 214
private def cntCached948 : T6 := .node cntCached0 cntCached102 cntCached410 cntCached687 cntCached924 cntCached947
private def cntCached949 : T6 := .leaf 280
private def cntCached950 : T6 := .node cntCached0 cntCached408 cntCached882 cntCached941 cntCached926 cntCached949
private def cntCached951 : T6 := .leaf 213
private def cntCached952 : T6 := .leaf 369
private def cntCached953 : T6 := .node cntCached0 cntCached130 cntCached951 cntCached943 cntCached928 cntCached952
private def cntCached954 : T6 := .node cntCached1 cntCached946 cntCached948 cntCached950 cntCached929 cntCached953
private def cntCached955 : T6 := .node cntCached2 cntCached934 cntCached938 cntCached945 cntCached930 cntCached954
private def cntCached956 : T6 := .node cntCached3 cntCached832 cntCached858 cntCached890 cntCached931 cntCached955
private def cntCached957 : T6 := .node cntCached0 cntCached0 cntCached6 cntCached8 cntCached13 cntCached85
private def cntCached958 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached32 cntCached43 cntCached89
private def cntCached959 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached87 cntCached94 cntCached62
private def cntCached960 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached70 cntCached112
private def cntCached961 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached438 cntCached112 cntCached79
private def cntCached962 : T6 := .node cntCached1 cntCached957 cntCached958 cntCached959 cntCached960 cntCached961
private def cntCached963 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached43 cntCached198 cntCached96
private def cntCached964 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached94 cntCached110 cntCached340
private def cntCached965 : T6 := .node cntCached0 cntCached23 cntCached94 cntCached331 cntCached242 cntCached267
private def cntCached966 : T6 := .node cntCached0 cntCached220 cntCached62 cntCached326 cntCached267 cntCached127
private def cntCached967 : T6 := .node cntCached1 cntCached820 cntCached963 cntCached964 cntCached965 cntCached966
private def cntCached968 : T6 := .node cntCached0 cntCached11 cntCached18 cntCached224 cntCached40 cntCached46
private def cntCached969 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached198 cntCached284 cntCached72
private def cntCached970 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached70 cntCached670 cntCached463
private def cntCached971 : T6 := .node cntCached0 cntCached220 cntCached438 cntCached396 cntCached535 cntCached307
private def cntCached972 : T6 := .node cntCached0 cntCached281 cntCached296 cntCached446 cntCached307 cntCached392
private def cntCached973 : T6 := .node cntCached1 cntCached968 cntCached969 cntCached970 cntCached971 cntCached972
private def cntCached974 : T6 := .node cntCached0 cntCached16 cntCached38 cntCached40 cntCached46 cntCached139
private def cntCached975 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached96 cntCached72 cntCached229
private def cntCached976 : T6 := .node cntCached0 cntCached40 cntCached284 cntCached345 cntCached463 cntCached260
private def cntCached977 : T6 := .leaf 155
private def cntCached978 : T6 := .node cntCached0 cntCached69 cntCached124 cntCached335 cntCached392 cntCached977
private def cntCached979 : T6 := .node cntCached1 cntCached974 cntCached975 cntCached976 cntCached972 cntCached978
private def cntCached980 : T6 := .node cntCached2 cntCached64 cntCached962 cntCached967 cntCached973 cntCached979
private def cntCached981 : T6 := .node cntCached0 cntCached202 cntCached53 cntCached283 cntCached110 cntCached440
private def cntCached982 : T6 := .node cntCached0 cntCached224 cntCached60 cntCached100 cntCached440 cntCached304
private def cntCached983 : T6 := .node cntCached1 cntCached39 cntCached248 cntCached746 cntCached981 cntCached982
private def cntCached984 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached202 cntCached38 cntCached55
private def cntCached985 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached43 cntCached283 cntCached331
private def cntCached986 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached94 cntCached251 cntCached79
private def cntCached987 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached102 cntCached389 cntCached390
private def cntCached988 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached290 cntCached390 cntCached392
private def cntCached989 : T6 := .node cntCached1 cntCached984 cntCached985 cntCached986 cntCached987 cntCached988
private def cntCached990 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached43 cntCached198 cntCached96
private def cntCached991 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached46 cntCached65 cntCached124
private def cntCached992 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached381 cntCached389 cntCached447
private def cntCached993 : T6 := .leaf 127
private def cntCached994 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached561 cntCached993 cntCached977
private def cntCached995 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached268 cntCached977 cntCached876
private def cntCached996 : T6 := .node cntCached1 cntCached990 cntCached991 cntCached992 cntCached994 cntCached995
private def cntCached997 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached281 cntCached100 cntCached257
private def cntCached998 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached115 cntCached258 cntCached335
private def cntCached999 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached389 cntCached130 cntCached847
private def cntCached1000 : T6 := .leaf 169
private def cntCached1001 : T6 := .node cntCached0 cntCached62 cntCached591 cntCached993 cntCached1000 cntCached941
private def cntCached1002 : T6 := .leaf 111
private def cntCached1003 : T6 := .leaf 227
private def cntCached1004 : T6 := .node cntCached0 cntCached141 cntCached1002 cntCached977 cntCached941 cntCached1003
private def cntCached1005 : T6 := .node cntCached1 cntCached997 cntCached998 cntCached999 cntCached1001 cntCached1004
private def cntCached1006 : T6 := .node cntCached0 cntCached38 cntCached281 cntCached284 cntCached257 cntCached332
private def cntCached1007 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached235 cntCached335 cntCached156
private def cntCached1008 : T6 := .node cntCached0 cntCached96 cntCached79 cntCached447 cntCached847 cntCached849
private def cntCached1009 : T6 := .leaf 256
private def cntCached1010 : T6 := .node cntCached0 cntCached253 cntCached700 cntCached876 cntCached1003 cntCached1009
private def cntCached1011 : T6 := .node cntCached1 cntCached1006 cntCached1007 cntCached1008 cntCached1004 cntCached1010
private def cntCached1012 : T6 := .node cntCached2 cntCached983 cntCached989 cntCached996 cntCached1005 cntCached1011
private def cntCached1013 : T6 := .node cntCached0 cntCached34 cntCached198 cntCached208 cntCached332 cntCached143
private def cntCached1014 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached75 cntCached143 cntCached562
private def cntCached1015 : T6 := .node cntCached1 cntCached56 cntCached404 cntCached860 cntCached1013 cntCached1014
private def cntCached1016 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached281 cntCached284
private def cntCached1017 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached281 cntCached115 cntCached235
private def cntCached1018 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached65 cntCached561 cntCached268
private def cntCached1019 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached446 cntCached915 cntCached919
private def cntCached1020 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached298 cntCached919 cntCached173
private def cntCached1021 : T6 := .node cntCached1 cntCached1016 cntCached1017 cntCached1018 cntCached1019 cntCached1020
private def cntCached1022 : T6 := .node cntCached0 cntCached21 cntCached92 cntCached57 cntCached208 cntCached75
private def cntCached1023 : T6 := .node cntCached0 cntCached53 cntCached94 cntCached65 cntCached561 cntCached268
private def cntCached1024 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached463 cntCached778 cntCached171
private def cntCached1025 : T6 := .node cntCached0 cntCached70 cntCached561 cntCached700 cntCached876 cntCached689
private def cntCached1026 : T6 := .node cntCached0 cntCached345 cntCached268 cntCached337 cntCached689 cntCached878
private def cntCached1027 : T6 := .node cntCached1 cntCached1022 cntCached1023 cntCached1024 cntCached1025 cntCached1026
private def cntCached1028 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached65 cntCached332 cntCached143
private def cntCached1029 : T6 := .leaf 156
private def cntCached1030 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached463 cntCached309 cntCached1029
private def cntCached1031 : T6 := .node cntCached0 cntCached510 cntCached561 cntCached778 cntCached849 cntCached947
private def cntCached1032 : T6 := .leaf 268
private def cntCached1033 : T6 := .node cntCached0 cntCached670 cntCached309 cntCached876 cntCached782 cntCached1032
private def cntCached1034 : T6 := .leaf 301
private def cntCached1035 : T6 := .node cntCached0 cntCached463 cntCached1029 cntCached689 cntCached1032 cntCached1034
private def cntCached1036 : T6 := .node cntCached1 cntCached1028 cntCached1030 cntCached1031 cntCached1033 cntCached1035
private def cntCached1037 : T6 := .node cntCached0 cntCached55 cntCached70 cntCached670 cntCached143 cntCached562
private def cntCached1038 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached307 cntCached1029 cntCached913
private def cntCached1039 : T6 := .leaf 246
private def cntCached1040 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached171 cntCached947 cntCached1039
private def cntCached1041 : T6 := .leaf 334
private def cntCached1042 : T6 := .node cntCached0 cntCached260 cntCached913 cntCached878 cntCached1034 cntCached1041
private def cntCached1043 : T6 := .node cntCached1 cntCached1037 cntCached1038 cntCached1040 cntCached1035 cntCached1042
private def cntCached1044 : T6 := .node cntCached2 cntCached1015 cntCached1021 cntCached1027 cntCached1036 cntCached1043
private def cntCached1045 : T6 := .node cntCached0 cntCached40 cntCached100 cntCached332 cntCached146 cntCached774
private def cntCached1046 : T6 := .node cntCached0 cntCached46 cntCached257 cntCached143 cntCached774 cntCached134
private def cntCached1047 : T6 := .node cntCached1 cntCached61 cntCached441 cntCached892 cntCached1045 cntCached1046
private def cntCached1048 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached283 cntCached510 cntCached511
private def cntCached1049 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached292 cntCached591 cntCached1002
private def cntCached1050 : T6 := .node cntCached0 cntCached198 cntCached251 cntCached446 cntCached915 cntCached919
private def cntCached1051 : T6 := .leaf 173
private def cntCached1052 : T6 := .leaf 202
private def cntCached1053 : T6 := .node cntCached0 cntCached100 cntCached389 cntCached569 cntCached1051 cntCached1052
private def cntCached1054 : T6 := .leaf 231
private def cntCached1055 : T6 := .node cntCached0 cntCached257 cntCached390 cntCached570 cntCached1052 cntCached1054
private def cntCached1056 : T6 := .node cntCached1 cntCached1048 cntCached1049 cntCached1050 cntCached1053 cntCached1055
private def cntCached1057 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached65 cntCached332 cntCached143
private def cntCached1058 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached446 cntCached915 cntCached919
private def cntCached1059 : T6 := .node cntCached0 cntCached70 cntCached463 cntCached392 cntCached913 cntCached433
private def cntCached1060 : T6 := .node cntCached0 cntCached396 cntCached915 cntCached173 cntCached916 cntCached917
private def cntCached1061 : T6 := .node cntCached0 cntCached446 cntCached919 cntCached491 cntCached917 cntCached920
private def cntCached1062 : T6 := .node cntCached1 cntCached1057 cntCached1058 cntCached1059 cntCached1060 cntCached1061
private def cntCached1063 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached235 cntCached146 cntCached774
private def cntCached1064 : T6 := .leaf 201
private def cntCached1065 : T6 := .node cntCached0 cntCached438 cntCached463 cntCached910 cntCached546 cntCached1064
private def cntCached1066 : T6 := .leaf 236
private def cntCached1067 : T6 := .leaf 269
private def cntCached1068 : T6 := .node cntCached0 cntCached670 cntCached915 cntCached913 cntCached1066 cntCached1067
private def cntCached1069 : T6 := .leaf 327
private def cntCached1070 : T6 := .node cntCached0 cntCached535 cntCached546 cntCached916 cntCached803 cntCached1069
private def cntCached1071 : T6 := .leaf 361
private def cntCached1072 : T6 := .node cntCached0 cntCached307 cntCached1064 cntCached917 cntCached1069 cntCached1071
private def cntCached1073 : T6 := .node cntCached1 cntCached1063 cntCached1065 cntCached1068 cntCached1070 cntCached1072
private def cntCached1074 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached549 cntCached774 cntCached134
private def cntCached1075 : T6 := .leaf 230
private def cntCached1076 : T6 := .node cntCached0 cntCached296 cntCached155 cntCached911 cntCached1064 cntCached1075
private def cntCached1077 : T6 := .leaf 302
private def cntCached1078 : T6 := .node cntCached0 cntCached463 cntCached919 cntCached433 cntCached1067 cntCached1077
private def cntCached1079 : T6 := .leaf 395
private def cntCached1080 : T6 := .node cntCached0 cntCached392 cntCached1075 cntCached920 cntCached1071 cntCached1079
private def cntCached1081 : T6 := .node cntCached1 cntCached1074 cntCached1076 cntCached1078 cntCached1072 cntCached1080
private def cntCached1082 : T6 := .node cntCached2 cntCached1047 cntCached1056 cntCached1062 cntCached1073 cntCached1081
private def cntCached1083 : T6 := .node cntCached0 cntCached139 cntCached332 cntCached562 cntCached134 cntCached455
private def cntCached1084 : T6 := .node cntCached1 cntCached63 cntCached442 cntCached893 cntCached1046 cntCached1083
private def cntCached1085 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached100 cntCached511 cntCached235
private def cntCached1086 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached304 cntCached1002 cntCached700
private def cntCached1087 : T6 := .node cntCached0 cntCached96 cntCached79 cntCached298 cntCached919 cntCached173
private def cntCached1088 : T6 := .leaf 260
private def cntCached1089 : T6 := .node cntCached0 cntCached332 cntCached392 cntCached572 cntCached1054 cntCached1088
private def cntCached1090 : T6 := .node cntCached1 cntCached1085 cntCached1086 cntCached1087 cntCached1055 cntCached1089
private def cntCached1091 : T6 := .node cntCached0 cntCached55 cntCached510 cntCached670 cntCached143 cntCached562
private def cntCached1092 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached298 cntCached919 cntCached173
private def cntCached1093 : T6 := .node cntCached0 cntCached345 cntCached307 cntCached902 cntCached433 cntCached926
private def cntCached1094 : T6 := .node cntCached0 cntCached335 cntCached173 cntCached906 cntCached920 cntCached928
private def cntCached1095 : T6 := .node cntCached1 cntCached1091 cntCached1092 cntCached1093 cntCached1061 cntCached1094
private def cntCached1096 : T6 := .node cntCached0 cntCached62 cntCached265 cntCached447 cntCached134 cntCached455
private def cntCached1097 : T6 := .leaf 259
private def cntCached1098 : T6 := .node cntCached0 cntCached124 cntCached472 cntCached924 cntCached1075 cntCached1097
private def cntCached1099 : T6 := .leaf 335
private def cntCached1100 : T6 := .node cntCached0 cntCached260 cntCached173 cntCached926 cntCached1077 cntCached1099
private def cntCached1101 : T6 := .leaf 429
private def cntCached1102 : T6 := .node cntCached0 cntCached977 cntCached1097 cntCached928 cntCached1079 cntCached1101
private def cntCached1103 : T6 := .node cntCached1 cntCached1096 cntCached1098 cntCached1100 cntCached1080 cntCached1102
private def cntCached1104 : T6 := .node cntCached2 cntCached1084 cntCached1090 cntCached1095 cntCached1081 cntCached1103
private def cntCached1105 : T6 := .node cntCached3 cntCached980 cntCached1012 cntCached1044 cntCached1082 cntCached1104
private def cntCached1106 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached202 cntCached85 cntCached53
private def cntCached1107 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached89 cntCached215
private def cntCached1108 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached94 cntCached62 cntCached72
private def cntCached1109 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached257 cntCached79 cntCached143
private def cntCached1110 : T6 := .node cntCached1 cntCached1106 cntCached1107 cntCached1108 cntCached961 cntCached1109
private def cntCached1111 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached198 cntCached96 cntCached251
private def cntCached1112 : T6 := .node cntCached0 cntCached23 cntCached281 cntCached438 cntCached340 cntCached258
private def cntCached1113 : T6 := .node cntCached0 cntCached46 cntCached72 cntCached117 cntCached127 cntCached309
private def cntCached1114 : T6 := .node cntCached1 cntCached826 cntCached1111 cntCached1112 cntCached966 cntCached1113
private def cntCached1115 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached198 cntCached139 cntCached438
private def cntCached1116 : T6 := .node cntCached0 cntCached87 cntCached69 cntCached251 cntCached229 cntCached463
private def cntCached1117 : T6 := .node cntCached0 cntCached198 cntCached102 cntCached265 cntCached260 cntCached130
private def cntCached1118 : T6 := .node cntCached0 cntCached510 cntCached306 cntCached993 cntCached977 cntCached578
private def cntCached1119 : T6 := .node cntCached1 cntCached1115 cntCached1116 cntCached1117 cntCached978 cntCached1118
private def cntCached1120 : T6 := .node cntCached2 cntCached67 cntCached1110 cntCached1114 cntCached979 cntCached1119
private def cntCached1121 : T6 := .node cntCached0 cntCached87 cntCached139 cntCached141 cntCached304 cntCached479
private def cntCached1122 : T6 := .node cntCached1 cntCached41 cntCached249 cntCached747 cntCached982 cntCached1121
private def cntCached1123 : T6 := .node cntCached0 cntCached30 cntCached21 cntCached53 cntCached55 cntCached49
private def cntCached1124 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached57 cntCached331 cntCached105
private def cntCached1125 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached79 cntCached593
private def cntCached1126 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached432 cntCached392 cntCached399
private def cntCached1127 : T6 := .node cntCached1 cntCached1123 cntCached1124 cntCached1125 cntCached988 cntCached1126
private def cntCached1128 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached198 cntCached96 cntCached251
private def cntCached1129 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached331 cntCached124 cntCached120
private def cntCached1130 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached79 cntCached447 cntCached134
private def cntCached1131 : T6 := .leaf 211
private def cntCached1132 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached886 cntCached876 cntCached1131
private def cntCached1133 : T6 := .node cntCached1 cntCached1128 cntCached1129 cntCached1130 cntCached995 cntCached1132
private def cntCached1134 : T6 := .node cntCached0 cntCached40 cntCached324 cntCached102 cntCached332 cntCached267
private def cntCached1135 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached293 cntCached156 cntCached919
private def cntCached1136 : T6 := .node cntCached0 cntCached251 cntCached593 cntCached134 cntCached849 cntCached855
private def cntCached1137 : T6 := .leaf 285
private def cntCached1138 : T6 := .node cntCached0 cntCached446 cntCached570 cntCached1131 cntCached1009 cntCached1137
private def cntCached1139 : T6 := .node cntCached1 cntCached1134 cntCached1135 cntCached1136 cntCached1010 cntCached1138
private def cntCached1140 : T6 := .node cntCached2 cntCached1122 cntCached1127 cntCached1133 cntCached1011 cntCached1139
private def cntCached1141 : T6 := .node cntCached0 cntCached60 cntCached251 cntCached591 cntCached562 cntCached569
private def cntCached1142 : T6 := .node cntCached1 cntCached58 cntCached405 cntCached861 cntCached1014 cntCached1141
private def cntCached1143 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached281 cntCached284 cntCached102
private def cntCached1144 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached208 cntCached235 cntCached293
private def cntCached1145 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached304 cntCached268 cntCached886
private def cntCached1146 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached170 cntCached173 cntCached951
private def cntCached1147 : T6 := .node cntCached1 cntCached1143 cntCached1144 cntCached1145 cntCached1020 cntCached1146
private def cntCached1148 : T6 := .node cntCached0 cntCached53 cntCached283 cntCached70 cntCached75 cntCached591
private def cntCached1149 : T6 := .node cntCached0 cntCached46 cntCached381 cntCached304 cntCached268 cntCached886
private def cntCached1150 : T6 := .node cntCached0 cntCached62 cntCached79 cntCached416 cntCached171 cntCached884
private def cntCached1151 : T6 := .node cntCached0 cntCached265 cntCached886 cntCached552 cntCached878 cntCached887
private def cntCached1152 : T6 := .node cntCached1 cntCached1148 cntCached1149 cntCached1150 cntCached1026 cntCached1151
private def cntCached1153 : T6 := .node cntCached0 cntCached57 cntCached511 cntCached561 cntCached562 cntCached569
private def cntCached1154 : T6 := .leaf 212
private def cntCached1155 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached882 cntCached913 cntCached1154
private def cntCached1156 : T6 := .leaf 278
private def cntCached1157 : T6 := .node cntCached0 cntCached408 cntCached886 cntCached884 cntCached1039 cntCached1156
private def cntCached1158 : T6 := .leaf 367
private def cntCached1159 : T6 := .node cntCached0 cntCached130 cntCached1154 cntCached887 cntCached1041 cntCached1158
private def cntCached1160 : T6 := .node cntCached1 cntCached1153 cntCached1155 cntCached1157 cntCached1042 cntCached1159
private def cntCached1161 : T6 := .node cntCached2 cntCached1142 cntCached1147 cntCached1152 cntCached1043 cntCached1160
private def cntCached1162 : T6 := .leaf 180
private def cntCached1163 : T6 := .node cntCached0 cntCached438 cntCached267 cntCached569 cntCached455 cntCached1162
private def cntCached1164 : T6 := .node cntCached1 cntCached66 cntCached480 cntCached933 cntCached1083 cntCached1163
private def cntCached1165 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached141 cntCached235 cntCached125
private def cntCached1166 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached146 cntCached700 cntCached570
private def cntCached1167 : T6 := .node cntCached0 cntCached251 cntCached593 cntCached170 cntCached173 cntCached951
private def cntCached1168 : T6 := .leaf 289
private def cntCached1169 : T6 := .node cntCached0 cntCached267 cntCached399 cntCached689 cntCached1088 cntCached1168
private def cntCached1170 : T6 := .node cntCached1 cntCached1165 cntCached1166 cntCached1167 cntCached1089 cntCached1169
private def cntCached1171 : T6 := .node cntCached0 cntCached57 cntCached296 cntCached561 cntCached562 cntCached569
private def cntCached1172 : T6 := .node cntCached0 cntCached102 cntCached432 cntCached170 cntCached173 cntCached951
private def cntCached1173 : T6 := .node cntCached0 cntCached265 cntCached882 cntCached941 cntCached926 cntCached949
private def cntCached1174 : T6 := .node cntCached0 cntCached993 cntCached951 cntCached943 cntCached928 cntCached952
private def cntCached1175 : T6 := .node cntCached1 cntCached1171 cntCached1172 cntCached1173 cntCached1094 cntCached1174
private def cntCached1176 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached156 cntCached455 cntCached1162
private def cntCached1177 : T6 := .leaf 288
private def cntCached1178 : T6 := .node cntCached0 cntCached306 cntCached497 cntCached947 cntCached1097 cntCached1177
private def cntCached1179 : T6 := .leaf 368
private def cntCached1180 : T6 := .node cntCached0 cntCached130 cntCached951 cntCached949 cntCached1099 cntCached1179
private def cntCached1181 : T6 := .leaf 463
private def cntCached1182 : T6 := .node cntCached0 cntCached578 cntCached1177 cntCached952 cntCached1101 cntCached1181
private def cntCached1183 : T6 := .node cntCached1 cntCached1176 cntCached1178 cntCached1180 cntCached1102 cntCached1182
private def cntCached1184 : T6 := .node cntCached2 cntCached1164 cntCached1170 cntCached1175 cntCached1103 cntCached1183
private def cntCached1185 : T6 := .node cntCached3 cntCached1120 cntCached1140 cntCached1161 cntCached1104 cntCached1184
private def cntCached1186 : T6 := .node cntCached4 cntCached169 cntCached807 cntCached956 cntCached1105 cntCached1185
private def cntCached1187 : T6 := .node cntCached0 cntCached0 cntCached11 cntCached202 cntCached43 cntCached89
private def cntCached1188 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached53 cntCached281 cntCached284
private def cntCached1189 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached281 cntCached438 cntCached296
private def cntCached1190 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached284 cntCached296 cntCached124
private def cntCached1191 : T6 := .node cntCached1 cntCached363 cntCached1187 cntCached1188 cntCached1189 cntCached1190
private def cntCached1192 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached38 cntCached89 cntCached139
private def cntCached1193 : T6 := .node cntCached0 cntCached13 cntCached43 cntCached198 cntCached62 cntCached141
private def cntCached1194 : T6 := .node cntCached0 cntCached85 cntCached60 cntCached62 cntCached440 cntCached290
private def cntCached1195 : T6 := .node cntCached0 cntCached26 cntCached69 cntCached141 cntCached290 cntCached535
private def cntCached1196 : T6 := .node cntCached1 cntCached515 cntCached1192 cntCached1193 cntCached1194 cntCached1195
private def cntCached1197 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached55 cntCached139 cntCached110
private def cntCached1198 : T6 := .node cntCached0 cntCached85 cntCached89 cntCached96 cntCached141 cntCached253
private def cntCached1199 : T6 := .node cntCached0 cntCached194 cntCached331 cntCached253 cntCached535 cntCached155
private def cntCached1200 : T6 := .node cntCached1 cntCached522 cntCached1197 cntCached1198 cntCached1195 cntCached1199
private def cntCached1201 : T6 := .node cntCached2 cntCached48 cntCached508 cntCached1191 cntCached1196 cntCached1200
private def cntCached1202 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached87 cntCached94 cntCached302
private def cntCached1203 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached46 cntCached302 cntCached115
private def cntCached1204 : T6 := .node cntCached1 cntCached33 cntCached193 cntCached248 cntCached1202 cntCached1203
private def cntCached1205 : T6 := .node cntCached0 cntCached6 cntCached11 cntCached32 cntCached87 cntCached57
private def cntCached1206 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached26 cntCached222 cntCached65
private def cntCached1207 : T6 := .node cntCached0 cntCached85 cntCached220 cntCached215 cntCached72 cntCached79
private def cntCached1208 : T6 := .node cntCached0 cntCached87 cntCached49 cntCached251 cntCached79 cntCached519
private def cntCached1209 : T6 := .node cntCached1 cntCached531 cntCached1205 cntCached1206 cntCached1207 cntCached1208
private def cntCached1210 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached102 cntCached561 cntCached562
private def cntCached1211 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached290 cntCached562 cntCached564
private def cntCached1212 : T6 := .node cntCached1 cntCached364 cntCached538 cntCached539 cntCached1210 cntCached1211
private def cntCached1213 : T6 := .node cntCached0 cntCached32 cntCached92 cntCached57 cntCached115 cntCached253
private def cntCached1214 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached251 cntCached591 cntCached1002
private def cntCached1215 : T6 := .node cntCached1 cntCached516 cntCached1213 cntCached1214 cntCached545 cntCached547
private def cntCached1216 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached208 cntCached253 cntCached479
private def cntCached1217 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached79 cntCached1002 cntCached700
private def cntCached1218 : T6 := .node cntCached1 cntCached523 cntCached1216 cntCached1217 cntCached547 cntCached553
private def cntCached1219 : T6 := .node cntCached2 cntCached1204 cntCached1209 cntCached1212 cntCached1215 cntCached1218
private def cntCached1220 : T6 := .node cntCached0 cntCached32 cntCached26 cntCached57 cntCached331 cntCached345
private def cntCached1221 : T6 := .node cntCached0 cntCached23 cntCached198 cntCached438 cntCached345 cntCached290
private def cntCached1222 : T6 := .node cntCached1 cntCached39 cntCached248 cntCached746 cntCached1220 cntCached1221
private def cntCached1223 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached57 cntCached72 cntCached408
private def cntCached1224 : T6 := .node cntCached0 cntCached92 cntCached215 cntCached257 cntCached267 cntCached268
private def cntCached1225 : T6 := .node cntCached0 cntCached281 cntCached251 cntCached258 cntCached268 cntCached151
private def cntCached1226 : T6 := .node cntCached1 cntCached559 cntCached1206 cntCached1223 cntCached1224 cntCached1225
private def cntCached1227 : T6 := .node cntCached0 cntCached18 cntCached26 cntCached283 cntCached102 cntCached290
private def cntCached1228 : T6 := .node cntCached0 cntCached26 cntCached283 cntCached292 cntCached306 cntCached416
private def cntCached1229 : T6 := .node cntCached0 cntCached283 cntCached72 cntCached125 cntCached156 cntCached455
private def cntCached1230 : T6 := .node cntCached0 cntCached100 cntCached408 cntCached342 cntCached455 cntCached457
private def cntCached1231 : T6 := .node cntCached1 cntCached567 cntCached1227 cntCached1228 cntCached1229 cntCached1230
private def cntCached1232 : T6 := .node cntCached0 cntCached510 cntCached463 cntCached424 cntCached606 cntCached607
private def cntCached1233 : T6 := .node cntCached0 cntCached511 cntCached155 cntCached399 cntCached607 cntCached609
private def cntCached1234 : T6 := .node cntCached1 cntCached575 cntCached576 cntCached577 cntCached1232 cntCached1233
private def cntCached1235 : T6 := .node cntCached0 cntCached235 cntCached472 cntCached426 cntCached609 cntCached639
private def cntCached1236 : T6 := .node cntCached1 cntCached583 cntCached584 cntCached585 cntCached1233 cntCached1235
private def cntCached1237 : T6 := .node cntCached2 cntCached1222 cntCached1226 cntCached1231 cntCached1234 cntCached1236
private def cntCached1238 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached208 cntCached242 cntCached463
private def cntCached1239 : T6 := .node cntCached0 cntCached220 cntCached302 cntCached340 cntCached463 cntCached410
private def cntCached1240 : T6 := .node cntCached1 cntCached45 cntCached285 cntCached763 cntCached1238 cntCached1239
private def cntCached1241 : T6 := .node cntCached0 cntCached21 cntCached220 cntCached215 cntCached72 cntCached79
private def cntCached1242 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached257 cntCached267 cntCached268
private def cntCached1243 : T6 := .node cntCached0 cntCached283 cntCached257 cntCached125 cntCached309 cntCached310
private def cntCached1244 : T6 := .node cntCached0 cntCached284 cntCached290 cntCached298 cntCached310 cntCached312
private def cntCached1245 : T6 := .node cntCached1 cntCached596 cntCached1241 cntCached1242 cntCached1243 cntCached1244
private def cntCached1246 : T6 := .node cntCached0 cntCached87 cntCached215 cntCached141 cntCached446 cntCached447
private def cntCached1247 : T6 := .node cntCached0 cntCached283 cntCached141 cntCached143 cntCached778 cntCached497
private def cntCached1248 : T6 := .leaf 207
private def cntCached1249 : T6 := .node cntCached0 cntCached110 cntCached267 cntCached700 cntCached312 cntCached1248
private def cntCached1250 : T6 := .node cntCached0 cntCached440 cntCached268 cntCached484 cntCached1248 cntCached1066
private def cntCached1251 : T6 := .node cntCached1 cntCached604 cntCached1246 cntCached1247 cntCached1249 cntCached1250
private def cntCached1252 : T6 := .node cntCached0 cntCached281 cntCached141 cntCached446 cntCached829 cntCached798
private def cntCached1253 : T6 := .node cntCached0 cntCached510 cntCached446 cntCached156 cntCached464 cntCached176
private def cntCached1254 : T6 := .leaf 254
private def cntCached1255 : T6 := .node cntCached0 cntCached75 cntCached130 cntCached779 cntCached706 cntCached1254
private def cntCached1256 : T6 := .leaf 151
private def cntCached1257 : T6 := .leaf 284
private def cntCached1258 : T6 := .node cntCached0 cntCached117 cntCached1256 cntCached780 cntCached1254 cntCached1257
private def cntCached1259 : T6 := .node cntCached1 cntCached612 cntCached1252 cntCached1253 cntCached1255 cntCached1258
private def cntCached1260 : T6 := .node cntCached0 cntCached96 cntCached304 cntCached447 cntCached798 cntCached606
private def cntCached1261 : T6 := .node cntCached0 cntCached511 cntCached447 cntCached455 cntCached176 cntCached466
private def cntCached1262 : T6 := .leaf 314
private def cntCached1263 : T6 := .node cntCached0 cntCached293 cntCached464 cntCached782 cntCached1257 cntCached1262
private def cntCached1264 : T6 := .node cntCached1 cntCached621 cntCached1260 cntCached1261 cntCached1258 cntCached1263
private def cntCached1265 : T6 := .node cntCached2 cntCached1240 cntCached1245 cntCached1251 cntCached1259 cntCached1264
private def cntCached1266 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached408 cntCached410 cntCached148
private def cntCached1267 : T6 := .node cntCached1 cntCached47 cntCached286 cntCached764 cntCached1239 cntCached1266
private def cntCached1268 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached251 cntCached79 cntCached519
private def cntCached1269 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached258 cntCached268 cntCached151
private def cntCached1270 : T6 := .node cntCached0 cntCached251 cntCached293 cntCached134 cntCached312 cntCached319
private def cntCached1271 : T6 := .node cntCached1 cntCached631 cntCached1268 cntCached1269 cntCached1244 cntCached1270
private def cntCached1272 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached265 cntCached447 cntCached449
private def cntCached1273 : T6 := .node cntCached0 cntCached100 cntCached265 cntCached148 cntCached497 cntCached165
private def cntCached1274 : T6 := .leaf 265
private def cntCached1275 : T6 := .node cntCached0 cntCached304 cntCached151 cntCached775 cntCached1066 cntCached1274
private def cntCached1276 : T6 := .node cntCached1 cntCached637 cntCached1272 cntCached1273 cntCached1250 cntCached1275
private def cntCached1277 : T6 := .leaf 200
private def cntCached1278 : T6 := .node cntCached0 cntCached65 cntCached120 cntCached449 cntCached606 cntCached1277
private def cntCached1279 : T6 := .node cntCached0 cntCached235 cntCached449 cntCached457 cntCached466 cntCached473
private def cntCached1280 : T6 := .leaf 344
private def cntCached1281 : T6 := .node cntCached0 cntCached298 cntCached1064 cntCached785 cntCached1262 cntCached1280
private def cntCached1282 : T6 := .node cntCached1 cntCached642 cntCached1278 cntCached1279 cntCached1263 cntCached1281
private def cntCached1283 : T6 := .node cntCached2 cntCached1267 cntCached1271 cntCached1276 cntCached1264 cntCached1282
private def cntCached1284 : T6 := .node cntCached3 cntCached1201 cntCached1219 cntCached1237 cntCached1265 cntCached1283
private def cntCached1285 : T6 := .node cntCached0 cntCached8 cntCached32 cntCached38 cntCached60 cntCached324
private def cntCached1286 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached281 cntCached70 cntCached345
private def cntCached1287 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached110 cntCached396 cntCached446
private def cntCached1288 : T6 := .node cntCached0 cntCached40 cntCached284 cntCached340 cntCached446 cntCached335
private def cntCached1289 : T6 := .node cntCached1 cntCached820 cntCached1285 cntCached1286 cntCached1287 cntCached1288
private def cntCached1290 : T6 := .node cntCached0 cntCached16 cntCached53 cntCached60 cntCached302 cntCached102
private def cntCached1291 : T6 := .node cntCached0 cntCached34 cntCached46 cntCached510 cntCached105 cntCached561
private def cntCached1292 : T6 := .node cntCached0 cntCached40 cntCached100 cntCached670 cntCached549 cntCached268
private def cntCached1293 : T6 := .node cntCached0 cntCached46 cntCached257 cntCached463 cntCached268 cntCached700
private def cntCached1294 : T6 := .node cntCached1 cntCached968 cntCached1290 cntCached1291 cntCached1292 cntCached1293
private def cntCached1295 : T6 := .node cntCached0 cntCached34 cntCached60 cntCached324 cntCached102 cntCached242
private def cntCached1296 : T6 := .node cntCached0 cntCached92 cntCached302 cntCached440 cntCached561 cntCached274
private def cntCached1297 : T6 := .node cntCached0 cntCached139 cntCached332 cntCached260 cntCached700 cntCached847
private def cntCached1298 : T6 := .node cntCached1 cntCached974 cntCached1295 cntCached1296 cntCached1293 cntCached1297
private def cntCached1299 : T6 := .node cntCached2 cntCached64 cntCached962 cntCached1289 cntCached1294 cntCached1298
private def cntCached1300 : T6 := .node cntCached0 cntCached202 cntCached43 cntCached198 cntCached381 cntCached332
private def cntCached1301 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached208 cntCached591 cntCached155
private def cntCached1302 : T6 := .node cntCached0 cntCached198 cntCached115 cntCached389 cntCached130 cntCached847
private def cntCached1303 : T6 := .node cntCached0 cntCached96 cntCached235 cntCached447 cntCached847 cntCached849
private def cntCached1304 : T6 := .node cntCached1 cntCached990 cntCached1300 cntCached1301 cntCached1302 cntCached1303
private def cntCached1305 : T6 := .node cntCached0 cntCached43 cntCached99 cntCached65 cntCached265 cntCached260
private def cntCached1306 : T6 := .node cntCached0 cntCached60 cntCached115 cntCached591 cntCached829 cntCached310
private def cntCached1307 : T6 := .node cntCached0 cntCached284 cntCached117 cntCached130 cntCached905 cntCached552
private def cntCached1308 : T6 := .leaf 226
private def cntCached1309 : T6 := .node cntCached0 cntCached72 cntCached127 cntCached847 cntCached552 cntCached1308
private def cntCached1310 : T6 := .node cntCached1 cntCached997 cntCached1305 cntCached1306 cntCached1307 cntCached1309
private def cntCached1311 : T6 := .node cntCached0 cntCached89 cntCached381 cntCached124 cntCached260 cntCached424
private def cntCached1312 : T6 := .leaf 181
private def cntCached1313 : T6 := .node cntCached0 cntCached324 cntCached235 cntCached155 cntCached310 cntCached1312
private def cntCached1314 : T6 := .leaf 255
private def cntCached1315 : T6 := .node cntCached0 cntCached229 cntCached778 cntCached849 cntCached1308 cntCached1314
private def cntCached1316 : T6 := .node cntCached1 cntCached1006 cntCached1311 cntCached1313 cntCached1309 cntCached1315
private def cntCached1317 : T6 := .node cntCached2 cntCached558 cntCached989 cntCached1304 cntCached1310 cntCached1316
private def cntCached1318 : T6 := .node cntCached0 cntCached43 cntCached281 cntCached115 cntCached463 cntCached307
private def cntCached1319 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached267 cntCached910 cntCached911
private def cntCached1320 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached244 cntCached911 cntCached924
private def cntCached1321 : T6 := .node cntCached1 cntCached1016 cntCached986 cntCached1318 cntCached1319 cntCached1320
private def cntCached1322 : T6 := .node cntCached2 cntCached1015 cntCached1321 cntCached1027 cntCached1036 cntCached1043
private def cntCached1323 : T6 := .node cntCached0 cntCached53 cntCached222 cntCached102 cntCached389 cntCached390
private def cntCached1324 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached267 cntCached910 cntCached911
private def cntCached1325 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached424 cntCached578 cntCached319
private def cntCached1326 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached399 cntCached319 cntCached580
private def cntCached1327 : T6 := .node cntCached1 cntCached1048 cntCached1323 cntCached1324 cntCached1325 cntCached1326
private def cntCached1328 : T6 := .node cntCached2 cntCached1047 cntCached1327 cntCached1062 cntCached1073 cntCached1081
private def cntCached1329 : T6 := .node cntCached0 cntCached60 cntCached65 cntCached290 cntCached390 cntCached392
private def cntCached1330 : T6 := .node cntCached0 cntCached302 cntCached304 cntCached244 cntCached911 cntCached924
private def cntCached1331 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached426 cntCached580 cntCached586
private def cntCached1332 : T6 := .node cntCached1 cntCached1085 cntCached1329 cntCached1330 cntCached1326 cntCached1331
private def cntCached1333 : T6 := .node cntCached2 cntCached1084 cntCached1332 cntCached1095 cntCached1081 cntCached1103
private def cntCached1334 : T6 := .node cntCached3 cntCached1299 cntCached1317 cntCached1322 cntCached1328 cntCached1333
private def cntCached1335 : T6 := .node cntCached0 cntCached6 cntCached30 cntCached16 cntCached85 cntCached26
private def cntCached1336 : T6 := .node cntCached0 cntCached30 cntCached85 cntCached26 cntCached198 cntCached206
private def cntCached1337 : T6 := .node cntCached0 cntCached18 cntCached40 cntCached57 cntCached70 cntCached112
private def cntCached1338 : T6 := .node cntCached0 cntCached43 cntCached57 cntCached331 cntCached105 cntCached591
private def cntCached1339 : T6 := .node cntCached0 cntCached44 cntCached62 cntCached345 cntCached591 cntCached593
private def cntCached1340 : T6 := .node cntCached1 cntCached1335 cntCached1336 cntCached1337 cntCached1338 cntCached1339
private def cntCached1341 : T6 := .node cntCached0 cntCached202 cntCached87 cntCached46 cntCached62 cntCached141
private def cntCached1342 : T6 := .node cntCached0 cntCached23 cntCached283 cntCached331 cntCached242 cntCached267
private def cntCached1343 : T6 := .node cntCached0 cntCached44 cntCached70 cntCached229 cntCached519 cntCached244
private def cntCached1344 : T6 := .node cntCached0 cntCached94 cntCached112 cntCached306 cntCached244 cntCached472
private def cntCached1345 : T6 := .node cntCached1 cntCached968 cntCached1341 cntCached1342 cntCached1343 cntCached1344
private def cntCached1346 : T6 := .node cntCached0 cntCached16 cntCached43 cntCached220 cntCached94 cntCached324
private def cntCached1347 : T6 := .node cntCached0 cntCached224 cntCached281 cntCached62 cntCached112 cntCached304
private def cntCached1348 : T6 := .node cntCached0 cntCached220 cntCached510 cntCached396 cntCached535 cntCached307
private def cntCached1349 : T6 := .node cntCached0 cntCached283 cntCached326 cntCached237 cntCached993 cntCached418
private def cntCached1350 : T6 := .node cntCached0 cntCached96 cntCached258 cntCached298 cntCached418 cntCached902
private def cntCached1351 : T6 := .node cntCached1 cntCached1346 cntCached1347 cntCached1348 cntCached1349 cntCached1350
private def cntCached1352 : T6 := .node cntCached0 cntCached21 cntCached44 cntCached281 cntCached324 cntCached331
private def cntCached1353 : T6 := .node cntCached0 cntCached92 cntCached96 cntCached141 cntCached304 cntCached549
private def cntCached1354 : T6 := .node cntCached0 cntCached281 cntCached511 cntCached446 cntCached307 cntCached392
private def cntCached1355 : T6 := .node cntCached0 cntCached208 cntCached120 cntCached564 cntCached902 cntCached572
private def cntCached1356 : T6 := .node cntCached1 cntCached1352 cntCached1353 cntCached1354 cntCached1350 cntCached1355
private def cntCached1357 : T6 := .node cntCached2 cntCached74 cntCached1340 cntCached1345 cntCached1351 cntCached1356
private def cntCached1358 : T6 := .node cntCached0 cntCached224 cntCached198 cntCached70 cntCached105 cntCached591
private def cntCached1359 : T6 := .node cntCached0 cntCached92 cntCached206 cntCached112 cntCached591 cntCached593
private def cntCached1360 : T6 := .node cntCached1 cntCached45 cntCached528 cntCached981 cntCached1358 cntCached1359
private def cntCached1361 : T6 := .node cntCached0 cntCached30 cntCached18 cntCached43 cntCached89 cntCached139
private def cntCached1362 : T6 := .node cntCached0 cntCached18 cntCached92 cntCached57 cntCached65 cntCached229
private def cntCached1363 : T6 := .node cntCached0 cntCached26 cntCached222 cntCached292 cntCached591 cntCached1002
private def cntCached1364 : T6 := .node cntCached0 cntCached281 cntCached102 cntCached561 cntCached148 cntCached418
private def cntCached1365 : T6 := .node cntCached0 cntCached96 cntCached235 cntCached562 cntCached418 cntCached546
private def cntCached1366 : T6 := .node cntCached1 cntCached1361 cntCached1362 cntCached1363 cntCached1364 cntCached1365
private def cntCached1367 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached46 cntCached62 cntCached141
private def cntCached1368 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached65 cntCached265 cntCached260
private def cntCached1369 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached389 cntCached130 cntCached847
private def cntCached1370 : T6 := .node cntCached0 cntCached100 cntCached591 cntCached993 cntCached1000 cntCached941
private def cntCached1371 : T6 := .node cntCached0 cntCached257 cntCached1002 cntCached977 cntCached941 cntCached1003
private def cntCached1372 : T6 := .node cntCached1 cntCached1367 cntCached1368 cntCached1369 cntCached1370 cntCached1371
private def cntCached1373 : T6 := .node cntCached0 cntCached43 cntCached283 cntCached438 cntCached345 cntCached408
private def cntCached1374 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached258 cntCached298 cntCached886
private def cntCached1375 : T6 := .node cntCached0 cntCached62 cntCached591 cntCached130 cntCached905 cntCached552
private def cntCached1376 : T6 := .node cntCached0 cntCached440 cntCached342 cntCached1000 cntCached689 cntCached185
private def cntCached1377 : T6 := .leaf 275
private def cntCached1378 : T6 := .node cntCached0 cntCached290 cntCached687 cntCached941 cntCached185 cntCached1377
private def cntCached1379 : T6 := .node cntCached1 cntCached1373 cntCached1374 cntCached1375 cntCached1376 cntCached1378
private def cntCached1380 : T6 := .node cntCached0 cntCached44 cntCached284 cntCached296 cntCached408 cntCached237
private def cntCached1381 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached335 cntCached886 cntCached905
private def cntCached1382 : T6 := .node cntCached0 cntCached141 cntCached1002 cntCached847 cntCached552 cntCached1308
private def cntCached1383 : T6 := .leaf 305
private def cntCached1384 : T6 := .node cntCached0 cntCached535 cntCached161 cntCached1003 cntCached1377 cntCached1383
private def cntCached1385 : T6 := .node cntCached1 cntCached1380 cntCached1381 cntCached1382 cntCached1378 cntCached1384
private def cntCached1386 : T6 := .node cntCached2 cntCached1360 cntCached1366 cntCached1372 cntCached1379 cntCached1385
private def cntCached1387 : T6 := .node cntCached0 cntCached40 cntCached62 cntCached253 cntCached593 cntCached148
private def cntCached1388 : T6 := .node cntCached0 cntCached46 cntCached141 cntCached125 cntCached148 cntCached317
private def cntCached1389 : T6 := .node cntCached1 cntCached61 cntCached556 cntCached1013 cntCached1387 cntCached1388
private def cntCached1390 : T6 := .node cntCached0 cntCached18 cntCached87 cntCached94 cntCached438 cntCached296
private def cntCached1391 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached251 cntCached117 cntCached127
private def cntCached1392 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached463 cntCached309 cntCached1029
private def cntCached1393 : T6 := .node cntCached0 cntCached438 cntCached389 cntCached910 cntCached546 cntCached1064
private def cntCached1394 : T6 := .node cntCached0 cntCached296 cntCached390 cntCached911 cntCached1064 cntCached1075
private def cntCached1395 : T6 := .node cntCached1 cntCached1390 cntCached1391 cntCached1392 cntCached1393 cntCached1394
private def cntCached1396 : T6 := .node cntCached0 cntCached26 cntCached99 cntCached381 cntCached253 cntCached125
private def cntCached1397 : T6 := .node cntCached0 cntCached281 cntCached292 cntCached561 cntCached993 cntCached977
private def cntCached1398 : T6 := .node cntCached0 cntCached70 cntCached561 cntCached778 cntCached849 cntCached947
private def cntCached1399 : T6 := .node cntCached0 cntCached396 cntCached309 cntCached876 cntCached782 cntCached1032
private def cntCached1400 : T6 := .node cntCached0 cntCached446 cntCached1029 cntCached689 cntCached1032 cntCached1034
private def cntCached1401 : T6 := .node cntCached1 cntCached1396 cntCached1397 cntCached1398 cntCached1399 cntCached1400
private def cntCached1402 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached124 cntCached593 cntCached148
private def cntCached1403 : T6 := .leaf 170
private def cntCached1404 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached309 cntCached1403 cntCached634
private def cntCached1405 : T6 := .leaf 267
private def cntCached1406 : T6 := .node cntCached0 cntCached670 cntCached309 cntCached849 cntCached466 cntCached1405
private def cntCached1407 : T6 := .leaf 325
private def cntCached1408 : T6 := .node cntCached0 cntCached535 cntCached161 cntCached782 cntCached711 cntCached1407
private def cntCached1409 : T6 := .leaf 359
private def cntCached1410 : T6 := .node cntCached0 cntCached307 cntCached1277 cntCached1032 cntCached1407 cntCached1409
private def cntCached1411 : T6 := .node cntCached1 cntCached1402 cntCached1404 cntCached1406 cntCached1408 cntCached1410
private def cntCached1412 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached479 cntCached148 cntCached317
private def cntCached1413 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached1029 cntCached634 cntCached346
private def cntCached1414 : T6 := .leaf 300
private def cntCached1415 : T6 := .node cntCached0 cntCached463 cntCached1029 cntCached947 cntCached1405 cntCached1414
private def cntCached1416 : T6 := .leaf 229
private def cntCached1417 : T6 := .leaf 393
private def cntCached1418 : T6 := .node cntCached0 cntCached392 cntCached1416 cntCached1034 cntCached1409 cntCached1417
private def cntCached1419 : T6 := .node cntCached1 cntCached1412 cntCached1413 cntCached1415 cntCached1410 cntCached1418
private def cntCached1420 : T6 := .node cntCached2 cntCached1389 cntCached1395 cntCached1401 cntCached1411 cntCached1419
private def cntCached1421 : T6 := .node cntCached0 cntCached94 cntCached345 cntCached593 cntCached156 cntCached310
private def cntCached1422 : T6 := .node cntCached0 cntCached324 cntCached408 cntCached148 cntCached310 cntCached1051
private def cntCached1423 : T6 := .node cntCached1 cntCached71 cntCached592 cntCached1045 cntCached1421 cntCached1422
private def cntCached1424 : T6 := .node cntCached0 cntCached43 cntCached94 cntCached70 cntCached326 cntCached258
private def cntCached1425 : T6 := .node cntCached0 cntCached198 cntCached292 cntCached389 cntCached342 cntCached687
private def cntCached1426 : T6 := .node cntCached0 cntCached100 cntCached389 cntCached910 cntCached546 cntCached1064
private def cntCached1427 : T6 := .leaf 220
private def cntCached1428 : T6 := .leaf 250
private def cntCached1429 : T6 := .node cntCached0 cntCached340 cntCached774 cntCached578 cntCached1427 cntCached1428
private def cntCached1430 : T6 := .node cntCached0 cntCached265 cntCached489 cntCached319 cntCached1428 cntCached949
private def cntCached1431 : T6 := .node cntCached1 cntCached1424 cntCached1425 cntCached1426 cntCached1429 cntCached1430
private def cntCached1432 : T6 := .node cntCached0 cntCached60 cntCached208 cntCached124 cntCached593 cntCached148
private def cntCached1433 : T6 := .node cntCached0 cntCached438 cntCached561 cntCached915 cntCached161 cntCached1277
private def cntCached1434 : T6 := .node cntCached0 cntCached396 cntCached915 cntCached913 cntCached1066 cntCached1067
private def cntCached1435 : T6 := .node cntCached0 cntCached237 cntCached546 cntCached916 cntCached803 cntCached1069
private def cntCached1436 : T6 := .node cntCached0 cntCached298 cntCached1064 cntCached917 cntCached1069 cntCached1071
private def cntCached1437 : T6 := .node cntCached1 cntCached1432 cntCached1433 cntCached1434 cntCached1435 cntCached1436
private def cntCached1438 : T6 := .node cntCached0 cntCached69 cntCached229 cntCached432 cntCached156 cntCached310
private def cntCached1439 : T6 := .node cntCached0 cntCached340 cntCached599 cntCached546 cntCached802 cntCached926
private def cntCached1440 : T6 := .leaf 326
private def cntCached1441 : T6 := .node cntCached0 cntCached535 cntCached546 cntCached1066 cntCached498 cntCached1440
private def cntCached1442 : T6 := .leaf 353
private def cntCached1443 : T6 := .leaf 388
private def cntCached1444 : T6 := .node cntCached0 cntCached993 cntCached799 cntCached803 cntCached1442 cntCached1443
private def cntCached1445 : T6 := .leaf 423
private def cntCached1446 : T6 := .node cntCached0 cntCached418 cntCached906 cntCached1069 cntCached1443 cntCached1445
private def cntCached1447 : T6 := .node cntCached1 cntCached1438 cntCached1439 cntCached1441 cntCached1444 cntCached1446
private def cntCached1448 : T6 := .node cntCached0 cntCached70 cntCached446 cntCached599 cntCached310 cntCached1051
private def cntCached1449 : T6 := .node cntCached0 cntCached265 cntCached600 cntCached1064 cntCached926 cntCached1156
private def cntCached1450 : T6 := .leaf 360
private def cntCached1451 : T6 := .node cntCached0 cntCached307 cntCached1064 cntCached1067 cntCached1440 cntCached1450
private def cntCached1452 : T6 := .leaf 458
private def cntCached1453 : T6 := .node cntCached0 cntCached902 cntCached887 cntCached1071 cntCached1445 cntCached1452
private def cntCached1454 : T6 := .node cntCached1 cntCached1448 cntCached1449 cntCached1451 cntCached1446 cntCached1453
private def cntCached1455 : T6 := .node cntCached2 cntCached1423 cntCached1431 cntCached1437 cntCached1447 cntCached1454
private def cntCached1456 : T6 := .leaf 193
private def cntCached1457 : T6 := .node cntCached0 cntCached331 cntCached237 cntCached317 cntCached1051 cntCached1456
private def cntCached1458 : T6 := .node cntCached1 cntCached73 cntCached594 cntCached1046 cntCached1422 cntCached1457
private def cntCached1459 : T6 := .node cntCached0 cntCached44 cntCached302 cntCached112 cntCached258 cntCached120
private def cntCached1460 : T6 := .node cntCached0 cntCached206 cntCached124 cntCached390 cntCached687 cntCached161
private def cntCached1461 : T6 := .node cntCached0 cntCached257 cntCached390 cntCached911 cntCached1064 cntCached1075
private def cntCached1462 : T6 := .leaf 310
private def cntCached1463 : T6 := .node cntCached0 cntCached519 cntCached1051 cntCached580 cntCached949 cntCached1462
private def cntCached1464 : T6 := .node cntCached1 cntCached1459 cntCached1460 cntCached1461 cntCached1430 cntCached1463
private def cntCached1465 : T6 := .node cntCached0 cntCached49 cntCached340 cntCached479 cntCached148 cntCached317
private def cntCached1466 : T6 := .node cntCached0 cntCached296 cntCached562 cntCached919 cntCached1277 cntCached1416
private def cntCached1467 : T6 := .node cntCached0 cntCached446 cntCached919 cntCached433 cntCached1067 cntCached1077
private def cntCached1468 : T6 := .node cntCached0 cntCached564 cntCached1075 cntCached920 cntCached1071 cntCached1079
private def cntCached1469 : T6 := .node cntCached1 cntCached1465 cntCached1466 cntCached1467 cntCached1436 cntCached1468
private def cntCached1470 : T6 := .node cntCached0 cntCached72 cntCached274 cntCached886 cntCached1051 cntCached1456
private def cntCached1471 : T6 := .leaf 308
private def cntCached1472 : T6 := .node cntCached0 cntCached519 cntCached578 cntCached1075 cntCached1156 cntCached1471
private def cntCached1473 : T6 := .leaf 394
private def cntCached1474 : T6 := .node cntCached0 cntCached392 cntCached1075 cntCached1077 cntCached1450 cntCached1473
private def cntCached1475 : T6 := .leaf 309
private def cntCached1476 : T6 := .leaf 493
private def cntCached1477 : T6 := .node cntCached0 cntCached572 cntCached1475 cntCached1079 cntCached1452 cntCached1476
private def cntCached1478 : T6 := .node cntCached1 cntCached1470 cntCached1472 cntCached1474 cntCached1453 cntCached1477
private def cntCached1479 : T6 := .node cntCached2 cntCached1458 cntCached1464 cntCached1469 cntCached1454 cntCached1478
private def cntCached1480 : T6 := .node cntCached3 cntCached1357 cntCached1386 cntCached1420 cntCached1455 cntCached1479
private def cntCached1481 : T6 := .node cntCached0 cntCached11 cntCached32 cntCached34 cntCached26 cntCached194
private def cntCached1482 : T6 := .node cntCached0 cntCached32 cntCached87 cntCached198 cntCached206 cntCached208
private def cntCached1483 : T6 := .node cntCached0 cntCached38 cntCached94 cntCached438 cntCached112 cntCached79
private def cntCached1484 : T6 := .node cntCached0 cntCached46 cntCached292 cntCached290 cntCached593 cntCached244
private def cntCached1485 : T6 := .node cntCached1 cntCached1481 cntCached1482 cntCached1483 cntCached1339 cntCached1484
private def cntCached1486 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached302 cntCached141 cntCached253
private def cntCached1487 : T6 := .node cntCached0 cntCached220 cntCached100 cntCached326 cntCached267 cntCached127
private def cntCached1488 : T6 := .node cntCached0 cntCached206 cntCached79 cntCached1002 cntCached472 cntCached919
private def cntCached1489 : T6 := .node cntCached1 cntCached974 cntCached1486 cntCached1487 cntCached1344 cntCached1488
private def cntCached1490 : T6 := .node cntCached0 cntCached23 cntCached46 cntCached69 cntCached331 cntCached257
private def cntCached1491 : T6 := .node cntCached0 cntCached89 cntCached65 cntCached253 cntCached549 cntCached562
private def cntCached1492 : T6 := .node cntCached0 cntCached69 cntCached235 cntCached335 cntCached392 cntCached977
private def cntCached1493 : T6 := .node cntCached0 cntCached296 cntCached307 cntCached1029 cntCached572 cntCached1248
private def cntCached1494 : T6 := .node cntCached1 cntCached1490 cntCached1491 cntCached1492 cntCached1355 cntCached1493
private def cntCached1495 : T6 := .node cntCached2 cntCached77 cntCached1485 cntCached1489 cntCached1356 cntCached1494
private def cntCached1496 : T6 := .node cntCached0 cntCached89 cntCached208 cntCached79 cntCached593 cntCached244
private def cntCached1497 : T6 := .node cntCached1 cntCached47 cntCached529 cntCached982 cntCached1359 cntCached1496
private def cntCached1498 : T6 := .node cntCached0 cntCached32 cntCached53 cntCached89 cntCached139 cntCached110
private def cntCached1499 : T6 := .node cntCached0 cntCached53 cntCached99 cntCached208 cntCached229 cntCached143
private def cntCached1500 : T6 := .node cntCached0 cntCached198 cntCached65 cntCached304 cntCached1002 cntCached700
private def cntCached1501 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached564 cntCached546 cntCached552
private def cntCached1502 : T6 := .node cntCached1 cntCached1498 cntCached1499 cntCached1500 cntCached1365 cntCached1501
private def cntCached1503 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached302 cntCached141 cntCached253
private def cntCached1504 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached124 cntCached260 cntCached424
private def cntCached1505 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached447 cntCached847 cntCached849
private def cntCached1506 : T6 := .node cntCached0 cntCached332 cntCached700 cntCached876 cntCached1003 cntCached1009
private def cntCached1507 : T6 := .node cntCached1 cntCached1503 cntCached1504 cntCached1505 cntCached1371 cntCached1506
private def cntCached1508 : T6 := .node cntCached0 cntCached46 cntCached251 cntCached124 cntCached237 cntCached447
private def cntCached1509 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached156 cntCached905 cntCached1456
private def cntCached1510 : T6 := .node cntCached0 cntCached253 cntCached700 cntCached849 cntCached1308 cntCached1314
private def cntCached1511 : T6 := .node cntCached0 cntCached155 cntCached884 cntCached1009 cntCached1383 cntCached1099
private def cntCached1512 : T6 := .node cntCached1 cntCached1508 cntCached1509 cntCached1510 cntCached1384 cntCached1511
private def cntCached1513 : T6 := .node cntCached2 cntCached1497 cntCached1502 cntCached1507 cntCached1385 cntCached1512
private def cntCached1514 : T6 := .node cntCached0 cntCached139 cntCached253 cntCached390 cntCached317 cntCached399
private def cntCached1515 : T6 := .node cntCached1 cntCached63 cntCached557 cntCached1014 cntCached1388 cntCached1514
private def cntCached1516 : T6 := .node cntCached0 cntCached38 cntCached46 cntCached62 cntCached296 cntCached124
private def cntCached1517 : T6 := .node cntCached0 cntCached60 cntCached381 cntCached79 cntCached127 cntCached778
private def cntCached1518 : T6 := .node cntCached0 cntCached302 cntCached79 cntCached307 cntCached1029 cntCached913
private def cntCached1519 : T6 := .node cntCached0 cntCached124 cntCached392 cntCached924 cntCached1075 cntCached1097
private def cntCached1520 : T6 := .node cntCached1 cntCached1516 cntCached1517 cntCached1518 cntCached1394 cntCached1519
private def cntCached1521 : T6 := .node cntCached0 cntCached55 cntCached510 cntCached105 cntCached125 cntCached390
private def cntCached1522 : T6 := .node cntCached0 cntCached284 cntCached304 cntCached268 cntCached977 cntCached876
private def cntCached1523 : T6 := .node cntCached0 cntCached345 cntCached268 cntCached171 cntCached947 cntCached1039
private def cntCached1524 : T6 := .node cntCached0 cntCached335 cntCached913 cntCached878 cntCached1034 cntCached1041
private def cntCached1525 : T6 := .node cntCached1 cntCached1521 cntCached1522 cntCached1523 cntCached1400 cntCached1524
private def cntCached1526 : T6 := .node cntCached0 cntCached62 cntCached265 cntCached155 cntCached317 cntCached399
private def cntCached1527 : T6 := .leaf 257
private def cntCached1528 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached913 cntCached346 cntCached1527
private def cntCached1529 : T6 := .leaf 333
private def cntCached1530 : T6 := .node cntCached0 cntCached260 cntCached913 cntCached1039 cntCached1414 cntCached1529
private def cntCached1531 : T6 := .leaf 258
private def cntCached1532 : T6 := .leaf 427
private def cntCached1533 : T6 := .node cntCached0 cntCached977 cntCached1531 cntCached1041 cntCached1417 cntCached1532
private def cntCached1534 : T6 := .node cntCached1 cntCached1526 cntCached1528 cntCached1530 cntCached1418 cntCached1533
private def cntCached1535 : T6 := .node cntCached2 cntCached1515 cntCached1520 cntCached1525 cntCached1419 cntCached1534
private def cntCached1536 : T6 := .node cntCached0 cntCached257 cntCached447 cntCached399 cntCached1456 cntCached951
private def cntCached1537 : T6 := .node cntCached1 cntCached76 cntCached629 cntCached1083 cntCached1457 cntCached1536
private def cntCached1538 : T6 := .node cntCached0 cntCached46 cntCached115 cntCached79 cntCached120 cntCached307
private def cntCached1539 : T6 := .node cntCached0 cntCached208 cntCached535 cntCached392 cntCached161 cntCached884
private def cntCached1540 : T6 := .node cntCached0 cntCached332 cntCached392 cntCached924 cntCached1075 cntCached1097
private def cntCached1541 : T6 := .leaf 340
private def cntCached1542 : T6 := .node cntCached0 cntCached268 cntCached941 cntCached586 cntCached1462 cntCached1541
private def cntCached1543 : T6 := .node cntCached1 cntCached1538 cntCached1539 cntCached1540 cntCached1463 cntCached1542
private def cntCached1544 : T6 := .node cntCached0 cntCached62 cntCached408 cntCached155 cntCached317 cntCached399
private def cntCached1545 : T6 := .node cntCached0 cntCached124 cntCached564 cntCached173 cntCached1416 cntCached1531
private def cntCached1546 : T6 := .node cntCached0 cntCached335 cntCached173 cntCached926 cntCached1077 cntCached1099
private def cntCached1547 : T6 := .node cntCached0 cntCached1029 cntCached1097 cntCached928 cntCached1079 cntCached1101
private def cntCached1548 : T6 := .node cntCached1 cntCached1544 cntCached1545 cntCached1546 cntCached1468 cntCached1547
private def cntCached1549 : T6 := .node cntCached0 cntCached75 cntCached774 cntCached497 cntCached1456 cntCached951
private def cntCached1550 : T6 := .leaf 338
private def cntCached1551 : T6 := .node cntCached0 cntCached268 cntCached634 cntCached1097 cntCached1471 cntCached1550
private def cntCached1552 : T6 := .leaf 428
private def cntCached1553 : T6 := .node cntCached0 cntCached977 cntCached1097 cntCached1099 cntCached1473 cntCached1552
private def cntCached1554 : T6 := .leaf 339
private def cntCached1555 : T6 := .leaf 528
private def cntCached1556 : T6 := .node cntCached0 cntCached1248 cntCached1554 cntCached1101 cntCached1476 cntCached1555
private def cntCached1557 : T6 := .node cntCached1 cntCached1549 cntCached1551 cntCached1553 cntCached1477 cntCached1556
private def cntCached1558 : T6 := .node cntCached2 cntCached1537 cntCached1543 cntCached1548 cntCached1478 cntCached1557
private def cntCached1559 : T6 := .node cntCached3 cntCached1495 cntCached1513 cntCached1535 cntCached1479 cntCached1558
private def cntCached1560 : T6 := .node cntCached4 cntCached184 cntCached1284 cntCached1334 cntCached1480 cntCached1559
private def cntCached1561 : T6 := .node cntCached0 cntCached11 cntCached21 cntCached53 cntCached89 cntCached215
private def cntCached1562 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached46 cntCached284 cntCached102
private def cntCached1563 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached102 cntCached124 cntCached306
private def cntCached1564 : T6 := .node cntCached1 cntCached369 cntCached1561 cntCached1562 cntCached1190 cntCached1563
private def cntCached1565 : T6 := .node cntCached0 cntCached21 cntCached212 cntCached49 cntCached110 cntCached296
private def cntCached1566 : T6 := .node cntCached0 cntCached53 cntCached215 cntCached251 cntCached253 cntCached446
private def cntCached1567 : T6 := .node cntCached0 cntCached94 cntCached511 cntCached446 cntCached155 cntCached910
private def cntCached1568 : T6 := .node cntCached1 cntCached657 cntCached1565 cntCached1566 cntCached1199 cntCached1567
private def cntCached1569 : T6 := .node cntCached2 cntCached51 cntCached653 cntCached1564 cntCached1200 cntCached1568
private def cntCached1570 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached206 cntCached115 cntCached340
private def cntCached1571 : T6 := .node cntCached1 cntCached35 cntCached195 cntCached249 cntCached1203 cntCached1570
private def cntCached1572 : T6 := .node cntCached0 cntCached13 cntCached224 cntCached220 cntCached57 cntCached510
private def cntCached1573 : T6 := .node cntCached0 cntCached85 cntCached44 cntCached222 cntCached65 cntCached242
private def cntCached1574 : T6 := .node cntCached0 cntCached89 cntCached331 cntCached253 cntCached519 cntCached416
private def cntCached1575 : T6 := .node cntCached1 cntCached665 cntCached1572 cntCached1573 cntCached1208 cntCached1574
private def cntCached1576 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached432 cntCached564 cntCached455
private def cntCached1577 : T6 := .node cntCached1 cntCached370 cntCached671 cntCached672 cntCached1211 cntCached1576
private def cntCached1578 : T6 := .node cntCached0 cntCached212 cntCached70 cntCached670 cntCached479 cntCached268
private def cntCached1579 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached593 cntCached700 cntCached570
private def cntCached1580 : T6 := .node cntCached1 cntCached658 cntCached1578 cntCached1579 cntCached553 cntCached677
private def cntCached1581 : T6 := .node cntCached2 cntCached1571 cntCached1575 cntCached1577 cntCached1218 cntCached1580
private def cntCached1582 : T6 := .node cntCached0 cntCached92 cntCached69 cntCached257 cntCached290 cntCached549
private def cntCached1583 : T6 := .node cntCached1 cntCached41 cntCached249 cntCached747 cntCached1221 cntCached1582
private def cntCached1584 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached115 cntCached408 cntCached410
private def cntCached1585 : T6 := .node cntCached0 cntCached324 cntCached253 cntCached260 cntCached151 cntCached276
private def cntCached1586 : T6 := .node cntCached1 cntCached682 cntCached1573 cntCached1584 cntCached1225 cntCached1585
private def cntCached1587 : T6 := .node cntCached0 cntCached87 cntCached222 cntCached65 cntCached290 cntCached432
private def cntCached1588 : T6 := .node cntCached0 cntCached281 cntCached65 cntCached265 cntCached416 cntCached418
private def cntCached1589 : T6 := .node cntCached0 cntCached141 cntCached410 cntCached489 cntCached457 cntCached491
private def cntCached1590 : T6 := .node cntCached1 cntCached686 cntCached1587 cntCached1588 cntCached1230 cntCached1589
private def cntCached1591 : T6 := .node cntCached0 cntCached125 cntCached497 cntCached433 cntCached639 cntCached711
private def cntCached1592 : T6 := .node cntCached1 cntCached692 cntCached693 cntCached694 cntCached1235 cntCached1591
private def cntCached1593 : T6 := .node cntCached2 cntCached1583 cntCached1586 cntCached1590 cntCached1236 cntCached1592
private def cntCached1594 : T6 := .node cntCached0 cntCached222 cntCached340 cntCached535 cntCached148 cntCached472
private def cntCached1595 : T6 := .node cntCached1 cntCached50 cntCached327 cntCached790 cntCached1266 cntCached1594
private def cntCached1596 : T6 := .node cntCached0 cntCached55 cntCached331 cntCached253 cntCached519 cntCached416
private def cntCached1597 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached260 cntCached151 cntCached276
private def cntCached1598 : T6 := .node cntCached0 cntCached326 cntCached148 cntCached337 cntCached319 cntCached346
private def cntCached1599 : T6 := .node cntCached1 cntCached703 cntCached1596 cntCached1597 cntCached1270 cntCached1598
private def cntCached1600 : T6 := .node cntCached0 cntCached206 cntCached253 cntCached274 cntCached449 cntCached484
private def cntCached1601 : T6 := .node cntCached0 cntCached141 cntCached274 cntCached600 cntCached165 cntCached802
private def cntCached1602 : T6 := .leaf 294
private def cntCached1603 : T6 := .node cntCached0 cntCached479 cntCached276 cntCached799 cntCached1274 cntCached1602
private def cntCached1604 : T6 := .node cntCached1 cntCached709 cntCached1600 cntCached1601 cntCached1275 cntCached1603
private def cntCached1605 : T6 := .node cntCached0 cntCached345 cntCached342 cntCached484 cntCached1277 cntCached180
private def cntCached1606 : T6 := .node cntCached0 cntCached125 cntCached484 cntCached491 cntCached473 cntCached498
private def cntCached1607 : T6 := .leaf 374
private def cntCached1608 : T6 := .node cntCached0 cntCached778 cntCached1308 cntCached803 cntCached1280 cntCached1607
private def cntCached1609 : T6 := .node cntCached1 cntCached714 cntCached1605 cntCached1606 cntCached1281 cntCached1608
private def cntCached1610 : T6 := .node cntCached2 cntCached1595 cntCached1599 cntCached1604 cntCached1282 cntCached1609
private def cntCached1611 : T6 := .node cntCached3 cntCached1569 cntCached1581 cntCached1593 cntCached1283 cntCached1610
private def cntCached1612 : T6 := .node cntCached0 cntCached202 cntCached26 cntCached60 cntCached324 cntCached115
private def cntCached1613 : T6 := .node cntCached0 cntCached224 cntCached46 cntCached100 cntCached345 cntCached265
private def cntCached1614 : T6 := .node cntCached0 cntCached198 cntCached102 cntCached258 cntCached335 cntCached993
private def cntCached1615 : T6 := .node cntCached1 cntCached826 cntCached1612 cntCached1613 cntCached1288 cntCached1614
private def cntCached1616 : T6 := .node cntCached0 cntCached26 cntCached139 cntCached115 cntCached242 cntCached561
private def cntCached1617 : T6 := .node cntCached0 cntCached60 cntCached292 cntCached408 cntCached274 cntCached829
private def cntCached1618 : T6 := .node cntCached0 cntCached438 cntCached267 cntCached130 cntCached847 cntCached1051
private def cntCached1619 : T6 := .node cntCached1 cntCached1115 cntCached1616 cntCached1617 cntCached1297 cntCached1618
private def cntCached1620 : T6 := .node cntCached2 cntCached67 cntCached1110 cntCached1615 cntCached1298 cntCached1619
private def cntCached1621 : T6 := .node cntCached0 cntCached53 cntCached57 cntCached110 cntCached332 cntCached519
private def cntCached1622 : T6 := .node cntCached0 cntCached60 cntCached331 cntCached235 cntCached155 cntCached317
private def cntCached1623 : T6 := .node cntCached0 cntCached251 cntCached293 cntCached134 cntCached849 cntCached855
private def cntCached1624 : T6 := .node cntCached1 cntCached1128 cntCached1621 cntCached1622 cntCached1303 cntCached1623
private def cntCached1625 : T6 := .node cntCached0 cntCached215 cntCached396 cntCached120 cntCached424 cntCached1029
private def cntCached1626 : T6 := .leaf 209
private def cntCached1627 : T6 := .node cntCached0 cntCached115 cntCached293 cntCached317 cntCached1312 cntCached1626
private def cntCached1628 : T6 := .node cntCached0 cntCached463 cntCached911 cntCached855 cntCached1314 cntCached1257
private def cntCached1629 : T6 := .node cntCached1 cntCached1134 cntCached1625 cntCached1627 cntCached1315 cntCached1628
private def cntCached1630 : T6 := .node cntCached2 cntCached681 cntCached1127 cntCached1624 cntCached1316 cntCached1629
private def cntCached1631 : T6 := .node cntCached0 cntCached198 cntCached208 cntCached290 cntCached307 cntCached882
private def cntCached1632 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached687 cntCached924 cntCached947
private def cntCached1633 : T6 := .node cntCached1 cntCached1143 cntCached1125 cntCached1631 cntCached1320 cntCached1632
private def cntCached1634 : T6 := .node cntCached2 cntCached1142 cntCached1633 cntCached1152 cntCached1043 cntCached1160
private def cntCached1635 : T6 := .node cntCached0 cntCached139 cntCached242 cntCached432 cntCached392 cntCached399
private def cntCached1636 : T6 := .node cntCached0 cntCached292 cntCached146 cntCached687 cntCached924 cntCached947
private def cntCached1637 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached433 cntCached586 cntCached695
private def cntCached1638 : T6 := .node cntCached1 cntCached1165 cntCached1635 cntCached1636 cntCached1331 cntCached1637
private def cntCached1639 : T6 := .node cntCached2 cntCached1164 cntCached1638 cntCached1175 cntCached1103 cntCached1183
private def cntCached1640 : T6 := .node cntCached3 cntCached1620 cntCached1630 cntCached1634 cntCached1333 cntCached1639
private def cntCached1641 : T6 := .node cntCached0 cntCached13 cntCached34 cntCached26 cntCached194 cntCached94
private def cntCached1642 : T6 := .node cntCached0 cntCached34 cntCached89 cntCached69 cntCached208 cntCached112
private def cntCached1643 : T6 := .node cntCached0 cntCached40 cntCached96 cntCached257 cntCached79 cntCached143
private def cntCached1644 : T6 := .node cntCached0 cntCached49 cntCached75 cntCached549 cntCached244 cntCached700
private def cntCached1645 : T6 := .node cntCached1 cntCached1641 cntCached1642 cntCached1643 cntCached1484 cntCached1644
private def cntCached1646 : T6 := .node cntCached0 cntCached87 cntCached206 cntCached292 cntCached253 cntCached446
private def cntCached1647 : T6 := .node cntCached0 cntCached46 cntCached141 cntCached117 cntCached127 cntCached309
private def cntCached1648 : T6 := .node cntCached0 cntCached70 cntCached143 cntCached915 cntCached919 cntCached464
private def cntCached1649 : T6 := .node cntCached1 cntCached1115 cntCached1646 cntCached1647 cntCached1488 cntCached1648
private def cntCached1650 : T6 := .node cntCached0 cntCached26 cntCached49 cntCached510 cntCached257 cntCached670
private def cntCached1651 : T6 := .node cntCached0 cntCached57 cntCached345 cntCached446 cntCached562 cntCached915
private def cntCached1652 : T6 := .node cntCached0 cntCached510 cntCached125 cntCached993 cntCached977 cntCached578
private def cntCached1653 : T6 := .node cntCached0 cntCached396 cntCached156 cntCached606 cntCached1248 cntCached1003
private def cntCached1654 : T6 := .node cntCached1 cntCached1650 cntCached1651 cntCached1652 cntCached1493 cntCached1653
private def cntCached1655 : T6 := .node cntCached2 cntCached81 cntCached1645 cntCached1649 cntCached1494 cntCached1654
private def cntCached1656 : T6 := .node cntCached0 cntCached57 cntCached112 cntCached143 cntCached244 cntCached700
private def cntCached1657 : T6 := .node cntCached1 cntCached50 cntCached663 cntCached1121 cntCached1496 cntCached1656
private def cntCached1658 : T6 := .node cntCached0 cntCached34 cntCached194 cntCached215 cntCached110 cntCached296
private def cntCached1659 : T6 := .node cntCached0 cntCached194 cntCached70 cntCached670 cntCached143 cntCached447
private def cntCached1660 : T6 := .node cntCached0 cntCached69 cntCached242 cntCached146 cntCached700 cntCached570
private def cntCached1661 : T6 := .node cntCached0 cntCached345 cntCached244 cntCached455 cntCached552 cntCached615
private def cntCached1662 : T6 := .node cntCached1 cntCached1658 cntCached1659 cntCached1660 cntCached1501 cntCached1661
private def cntCached1663 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached292 cntCached253 cntCached446
private def cntCached1664 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached120 cntCached424 cntCached1029
private def cntCached1665 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached134 cntCached849 cntCached855
private def cntCached1666 : T6 := .node cntCached0 cntCached267 cntCached570 cntCached1131 cntCached1009 cntCached1137
private def cntCached1667 : T6 := .node cntCached1 cntCached1663 cntCached1664 cntCached1665 cntCached1506 cntCached1666
private def cntCached1668 : T6 := .node cntCached0 cntCached49 cntCached326 cntCached306 cntCached447 cntCached569
private def cntCached1669 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached919 cntCached1456 cntCached802
private def cntCached1670 : T6 := .node cntCached0 cntCached446 cntCached570 cntCached855 cntCached1314 cntCached1257
private def cntCached1671 : T6 := .leaf 221
private def cntCached1672 : T6 := .leaf 365
private def cntCached1673 : T6 := .node cntCached0 cntCached910 cntCached1671 cntCached1137 cntCached1099 cntCached1672
private def cntCached1674 : T6 := .node cntCached1 cntCached1668 cntCached1669 cntCached1670 cntCached1511 cntCached1673
private def cntCached1675 : T6 := .node cntCached2 cntCached1657 cntCached1662 cntCached1667 cntCached1512 cntCached1674
private def cntCached1676 : T6 := .leaf 179
private def cntCached1677 : T6 := .node cntCached0 cntCached438 cntCached446 cntCached910 cntCached399 cntCached1676
private def cntCached1678 : T6 := .node cntCached1 cntCached66 cntCached680 cntCached1141 cntCached1514 cntCached1677
private def cntCached1679 : T6 := .node cntCached0 cntCached40 cntCached206 cntCached72 cntCached124 cntCached306
private def cntCached1680 : T6 := .node cntCached0 cntCached139 cntCached396 cntCached593 cntCached778 cntCached911
private def cntCached1681 : T6 := .node cntCached0 cntCached292 cntCached593 cntCached882 cntCached913 cntCached1154
private def cntCached1682 : T6 := .node cntCached0 cntCached306 cntCached399 cntCached947 cntCached1097 cntCached1177
private def cntCached1683 : T6 := .node cntCached1 cntCached1679 cntCached1680 cntCached1681 cntCached1519 cntCached1682
private def cntCached1684 : T6 := .node cntCached0 cntCached57 cntCached296 cntCached389 cntCached390 cntCached910
private def cntCached1685 : T6 := .node cntCached0 cntCached102 cntCached146 cntCached886 cntCached876 cntCached1131
private def cntCached1686 : T6 := .node cntCached0 cntCached265 cntCached886 cntCached884 cntCached1039 cntCached1156
private def cntCached1687 : T6 := .node cntCached0 cntCached993 cntCached1154 cntCached887 cntCached1041 cntCached1158
private def cntCached1688 : T6 := .node cntCached1 cntCached1684 cntCached1685 cntCached1686 cntCached1524 cntCached1687
private def cntCached1689 : T6 := .node cntCached0 cntCached65 cntCached237 cntCached424 cntCached399 cntCached1676
private def cntCached1690 : T6 := .leaf 286
private def cntCached1691 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached1154 cntCached1527 cntCached1690
private def cntCached1692 : T6 := .leaf 366
private def cntCached1693 : T6 := .node cntCached0 cntCached130 cntCached1154 cntCached1156 cntCached1529 cntCached1692
private def cntCached1694 : T6 := .leaf 287
private def cntCached1695 : T6 := .leaf 461
private def cntCached1696 : T6 := .node cntCached0 cntCached578 cntCached1694 cntCached1158 cntCached1532 cntCached1695
private def cntCached1697 : T6 := .node cntCached1 cntCached1689 cntCached1691 cntCached1693 cntCached1533 cntCached1696
private def cntCached1698 : T6 := .node cntCached2 cntCached1678 cntCached1683 cntCached1688 cntCached1534 cntCached1697
private def cntCached1699 : T6 := .node cntCached0 cntCached670 cntCached569 cntCached1676 cntCached951 cntCached609
private def cntCached1700 : T6 := .node cntCached1 cntCached80 cntCached701 cntCached1163 cntCached1536 cntCached1699
private def cntCached1701 : T6 := .node cntCached0 cntCached49 cntCached340 cntCached143 cntCached307 cntCached156
private def cntCached1702 : T6 := .node cntCached0 cntCached112 cntCached298 cntCached399 cntCached884 cntCached1671
private def cntCached1703 : T6 := .node cntCached0 cntCached267 cntCached399 cntCached947 cntCached1097 cntCached1177
private def cntCached1704 : T6 := .leaf 223
private def cntCached1705 : T6 := .leaf 370
private def cntCached1706 : T6 := .node cntCached0 cntCached424 cntCached1704 cntCached695 cntCached1541 cntCached1705
private def cntCached1707 : T6 := .node cntCached1 cntCached1701 cntCached1702 cntCached1703 cntCached1542 cntCached1706
private def cntCached1708 : T6 := .node cntCached0 cntCached65 cntCached535 cntCached424 cntCached399 cntCached1676
private def cntCached1709 : T6 := .node cntCached0 cntCached306 cntCached455 cntCached951 cntCached1531 cntCached1694
private def cntCached1710 : T6 := .node cntCached0 cntCached993 cntCached951 cntCached949 cntCached1099 cntCached1179
private def cntCached1711 : T6 := .node cntCached0 cntCached606 cntCached1177 cntCached952 cntCached1101 cntCached1181
private def cntCached1712 : T6 := .node cntCached1 cntCached1708 cntCached1709 cntCached1710 cntCached1547 cntCached1711
private def cntCached1713 : T6 := .node cntCached0 cntCached79 cntCached449 cntCached1312 cntCached951 cntCached609
private def cntCached1714 : T6 := .node cntCached0 cntCached424 cntCached706 cntCached1177 cntCached1550 cntCached1179
private def cntCached1715 : T6 := .leaf 462
private def cntCached1716 : T6 := .node cntCached0 cntCached578 cntCached1177 cntCached1179 cntCached1552 cntCached1715
private def cntCached1717 : T6 := .leaf 563
private def cntCached1718 : T6 := .node cntCached0 cntCached1003 cntCached952 cntCached1181 cntCached1555 cntCached1717
private def cntCached1719 : T6 := .node cntCached1 cntCached1713 cntCached1714 cntCached1716 cntCached1556 cntCached1718
private def cntCached1720 : T6 := .node cntCached2 cntCached1700 cntCached1707 cntCached1712 cntCached1557 cntCached1719
private def cntCached1721 : T6 := .node cntCached3 cntCached1655 cntCached1675 cntCached1698 cntCached1558 cntCached1720
private def cntCached1722 : T6 := .node cntCached4 cntCached189 cntCached1611 cntCached1640 cntCached1559 cntCached1721
private def cntCached1723 : T6 := .node cntCached5 cntCached190 cntCached722 cntCached1186 cntCached1560 cntCached1722

/-- Boolean structural equality of `T6` trees (evaluated by the kernel only). -/
noncomputable def t6beq (x : T6) : T6 → Bool :=
  T6.rec (motive := fun _ => T6 → Bool)
    (fun a y => T6.casesOn (motive := fun _ => Bool) y (fun b => Nat.beq a b) (fun _ _ _ _ _ _ => false))
    (fun _ _ _ _ _ _ ra rb rc rd re rf y => T6.casesOn (motive := fun _ => Bool) y (fun _ => false)
      (fun a' b' c' d' e' f' => ra a' && (rb b' && (rc c' && (rd d' && (re e' && rf f'))))))
    x

theorem eq_of_t6beq : ∀ (x y : T6), t6beq x y = true → x = y := by
  intro x
  induction x with
  | leaf a =>
    intro y h
    cases y with
    | leaf b => exact congrArg T6.leaf (Nat.eq_of_beq_eq_true h)
    | node => exact absurd h (by simp [t6beq])
  | node a b c d e f iha ihb ihc ihd ihe ihf =>
    intro y h
    cases y with
    | leaf => exact absurd h (by simp [t6beq])
    | node a' b' c' d' e' f' =>
      simp only [t6beq, Bool.and_eq_true] at h
      rw [iha a' h.1, ihb b' h.2.1, ihc c' h.2.2.1, ihd d' h.2.2.2.1, ihe e' h.2.2.2.2.1,
        ihf f' h.2.2.2.2.2]

-- Checked by the kernel only (a `rfl` would first run the elaborator's defeq check).
private theorem cntT_cached_eq : cntT = cntCached1723 := eq_of_t6beq _ _ (by decide +kernel)
private theorem coveragePacked_cached_eq (hb j : Nat) :
    coveragePacked hb j = maxHistT hb cntCached1723
      (dT (mapT (fun z => z ^ j) cntCached1723)) :=
  congrArg (fun c => maxHistT hb c (dT (mapT (fun z => z ^ j) c))) cntT_cached_eq
theorem coverageH1_packed : coveragePacked (2^128) 1 = coverageHPack (2^128) 1 := by
  exact (coveragePacked_cached_eq (2^128) 1).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 1) cntCached1723)) =
      coverageHPack (2^128) 1 by decide +kernel)
theorem coverageH2_packed : coveragePacked (2^128) 2 = coverageHPack (2^128) 2 := by
  exact (coveragePacked_cached_eq (2^128) 2).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 2) cntCached1723)) =
      coverageHPack (2^128) 2 by decide +kernel)
theorem coverageH3_packed : coveragePacked (2^128) 3 = coverageHPack (2^128) 3 := by
  exact (coveragePacked_cached_eq (2^128) 3).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 3) cntCached1723)) =
      coverageHPack (2^128) 3 by decide +kernel)
theorem coverageH4_packed : coveragePacked (2^128) 4 = coverageHPack (2^128) 4 := by
  exact (coveragePacked_cached_eq (2^128) 4).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 4) cntCached1723)) =
      coverageHPack (2^128) 4 by decide +kernel)
theorem coverageH5_packed : coveragePacked (2^128) 5 = coverageHPack (2^128) 5 := by
  exact (coveragePacked_cached_eq (2^128) 5).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 5) cntCached1723)) =
      coverageHPack (2^128) 5 by decide +kernel)
theorem coverageH6_packed : coveragePacked (2^128) 6 = coverageHPack (2^128) 6 := by
  exact (coveragePacked_cached_eq (2^128) 6).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 6) cntCached1723)) =
      coverageHPack (2^128) 6 by decide +kernel)
theorem coverageH7_packed : coveragePacked (2^128) 7 = coverageHPack (2^128) 7 := by
  exact (coveragePacked_cached_eq (2^128) 7).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 7) cntCached1723)) =
      coverageHPack (2^128) 7 by decide +kernel)
theorem coverageH8_packed : coveragePacked (2^128) 8 = coverageHPack (2^128) 8 := by
  exact (coveragePacked_cached_eq (2^128) 8).trans
    (show maxHistT (2^128) cntCached1723 (dT (mapT (fun z => z ^ 8) cntCached1723)) =
      coverageHPack (2^128) 8 by decide +kernel)
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (fact)
def winsorBinCheck : Bool :=
  (List.range 4096).all (fun c =>
    c * 50 ^ coverageBin c ≤ 51 ^ coverageBin c &&
      (c ≤ 1 || 51 ^ (coverageBin c - 1) < c * 50 ^ (coverageBin c - 1)))
def winsorMassCheck (r : Nat) : Bool :=
  coverageRetainedFastPack 1 r ≤ xNum r && xNum r < 2^512
def winsorRowDots (r : Nat) : Nat × Nat :=
  if r ≤ 20 then
    let v := winsorPackedSums winsorMGFPayData winsorResidualPayData (coverageProductLinear r)
    let missed := xNum r ^ 9 - v.1
    (v.2.1 + 3000 * winsorScale * missed, v.2.2 + winsorScale * missed)
  else (3000 * winsorScale * xNum r ^ 9, winsorScale * xNum r ^ 9)
def winsorRowBounds (r : Nat) : Nat × Nat :=
  let dots := winsorRowDots r
  let num := 1353 * 2^24 * 13533529 * LN^r
  let den := 100000000 * LD^r * fact r * Q^(9*r)
  (winsorCeil (num * dots.1) den, winsorCeil (num * dots.2) den)
def winsorTailBound : Nat := winsorCeil (winsorScale * A * LN^81) (LD^81 * fact 81)
def winsorBounds : Nat × Nat :=
  (List.range 81).foldr (fun r p =>
    let b := winsorRowBounds r
    (b.1 + p.1, b.2 + p.2)) (3000*winsorTailBound,winsorTailBound)
def winsorCheck : Bool := winsorBounds.1 ≤ 8*winsorScale && 5000*winsorBounds.2 ≤ winsorScale
end ClaudeWCT.Numerics.N600

namespace ClaudeWCT.Numerics.N600
theorem coverageH_packed (j : ℕ) (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    coveragePacked (2^128) j = coverageHPack (2^128) j := by
  interval_cases j
  · exact coverageH1_packed
  · exact coverageH2_packed
  · exact coverageH3_packed
  · exact coverageH4_packed
  · exact coverageH5_packed
  · exact coverageH6_packed
  · exact coverageH7_packed
  · exact coverageH8_packed
end ClaudeWCT.Numerics.N600
end
-- ==== merged from ClaudeWCT_Numerics_N600PriceChecksMoment ====
section

end
