import SigGolfCandidate.T3.Nonbinary.Codec
import SigGolfCandidate.T3.Gate6.ChildCounting

namespace SigGolfResearch.NonbinaryTop.Counting
open scoped BigOperators
open Codec Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false
def tripleSum5 (d : Triple5) : Nat := ∑ i,(d i).val
def tripleSum4 (d : Triple4) : Nat := ∑ i,(d i).val
def tripleSum8 (d : Triple8) : Nat := ∑ i,(d i).val
def weight (w : Word) : Nat := (∑ i,tripleSum5 (w.1 i))+tripleSum8 w.2
theorem weighted_tuples {α : Type} [Fintype α] (f : α → Nat) (y n : Nat) :
    (∑ d : Fin n → α,y^(∑ i,f (d i)))=(∑ a : α,y^f a)^n := by
  classical
  simpa only [Fintype.piFinset_univ,Finset.prod_pow_eq_pow_sum] using
    (Finset.sum_pow' (Finset.univ : Finset α) (fun a => y^f a) n).symm
def q4 (y : Nat) : Nat := 1+y+y^2+y^3
def q5 (y : Nat) : Nat := 1+y+y^2+y^3+y^4
def q8 (y : Nat) : Nat := 1+y+y^2+y^3+y^4+y^5+y^6+y^7
theorem weighted5 (y : Nat) : (∑ d : Triple5,y^tripleSum5 d)=q5 y^3 := by
  simp only [tripleSum5]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q5]
theorem weighted4 (y : Nat) : (∑ d : Triple4,y^tripleSum4 d)=q4 y^3 := by
  simp only [tripleSum4]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q4]
theorem weighted8 (y : Nat) : (∑ d : Triple8,y^tripleSum8 d)=q8 y^3 := by
  simp only [tripleSum8]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q8]
theorem weighted_words (y : Nat) : (∑ w : Word,y^weight w)=q5 y^51*q8 y^3 := by
  rw [Fintype.sum_prod_type]
  simp only [weight,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted5,weighted8,←pow_mul]
def radix : Nat := 2^136
def packed : Nat := q5 radix^51*q8 radix^3
theorem word_card_small : Fintype.card Word<radix-1 := by
  norm_num [Word,Triple8,Triple5,Fintype.card_prod,Fintype.card_fun,radix]
theorem truncated_card (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun w : Word => weight w<cut).card=
      (packed%radix^cut)%(radix-1) := by
  classical
  unfold packed
  rw [←weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ weight
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]
/-- Accepted top words at target 146 (no credit floor; configuration (1)+(2)). -/
def count : Nat := 68265759603931770586437474120287175
theorem exact_packed_count :
    (packed%radix^147)%(radix-1)-(packed%radix^146)%(radix-1)=count := by decide +kernel
theorem accepted_card : (Finset.univ.filter fun w : Word => weight w=146).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w=146)=
      (Finset.univ.filter fun w : Word => weight w<147)\
        (Finset.univ.filter fun w : Word => weight w<146) := by
    ext w; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]; omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 147 (by decide),truncated_card 146 (by decide),exact_packed_count]
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega
def digest (w : Word) : Fin (2^128) :=
  ⟨encode w,encode_bound w⟩
theorem digest_injective : Function.Injective digest := by
  intro a b h
  apply encode_injective
  change (digest a).val=(digest b).val
  exact congrArg (fun x : Fin (2^128) => x.val) h
noncomputable def acceptedDigests : Finset (Fin (2^128)) := by
  classical
  exact (Finset.univ.filter fun w : Word => weight w=146).image digest
theorem accepted_digest_card : acceptedDigests.card=count := by
  classical
  unfold acceptedDigests
  rw [Finset.card_image_of_injective _ digest_injective,accepted_card]
theorem probability_fraction : (count : ℚ)/2^128=
    68265759603931770586437474120287175/340282366920938463463374607431768211456 := by
  norm_num [count]
end SigGolfResearch.NonbinaryTop.Counting
#print axioms SigGolfResearch.NonbinaryTop.Counting.weighted_words
#print axioms SigGolfResearch.NonbinaryTop.Counting.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.Counting.accepted_card
#print axioms SigGolfResearch.NonbinaryTop.Counting.accepted_digest_card
#print axioms SigGolfResearch.NonbinaryTop.Counting.probability_fraction

/-! ### Campaign R6: the top word and its exact checksum-window count -/
namespace SigGolfResearch.NonbinaryTop.R6
open scoped BigOperators
open Codec Finset Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false
/-- The R6 top word: 8 radix-6 triples (chains 0..23) and 9 radix-5 triples (chains 24..50); the radix-8 checksum
chain 51 is derived (`153 - weight`). -/
abbrev Word := (Fin 8 → Triple6) × (Fin 9 → Triple5)
def tripleSum6 (d : Triple6) : Nat := ∑ i,(d i).val
def weight (w : Word) : Nat := (∑ g,tripleSum6 (w.1 g))+∑ q,tripleSum5 (w.2 q)
def q6 (y : Nat) : Nat := 1+y+y^2+y^3+y^4+y^5
theorem weighted6 (y : Nat) : (∑ d : Triple6,y^tripleSum6 d)=q6 y^3 := by
  simp only [tripleSum6]
  rw [weighted_tuples]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ,q6]
theorem weighted_words (y : Nat) : (∑ w : Word,y^weight w)=q6 y^24*q5 y^27 := by
  rw [Fintype.sum_prod_type]
  simp only [weight,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted_tuples,weighted6,weighted5,←pow_mul,←pow_mul]
def packed : Nat := q6 radix^24*q5 radix^27
theorem word_card_small : Fintype.card Word<radix-1 := by
  norm_num [Word,Triple6,Triple5,Fintype.card_prod,Fintype.card_fun,radix]
theorem truncated_card (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun w : Word => weight w<cut).card=
      (packed%radix^cut)%(radix-1) := by
  classical
  unfold packed
  rw [←weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ weight
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]
/-- R6 words whose checksum digit `153 - weight` lies in `[0, 7]` (data sums 146..153). -/
def count : Nat := 72344464170684509555509354797011162
theorem exact_packed_count :
    (packed%radix^154)%(radix-1)-(packed%radix^146)%(radix-1)=count := by decide +kernel
/-- The broad R6 top decoder accepts exactly `count` words (`0.426 · 2^127 / 1001`). -/
theorem window_card :
    (Finset.univ.filter fun w : Word => weight w≤153 ∧ 153-weight w<8).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w≤153 ∧ 153-weight w<8)=
      (Finset.univ.filter fun w : Word => weight w<154)\
        (Finset.univ.filter fun w : Word => weight w<146) := by
    ext w; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]; omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 154 (by decide),truncated_card 146 (by decide),exact_packed_count]
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega
end SigGolfResearch.NonbinaryTop.R6
#print axioms SigGolfResearch.NonbinaryTop.R6.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.R6.window_card
