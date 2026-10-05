import SigGolfCandidate.T3.Nonbinary.Counting
import SigGolfCandidate.T3.Nonbinary.SourceEncoding

/-! Credit filter: exact count of the top words a credit-filtering producer may select.
The credit of a word is the number of digits equal to the last-but-one value of their chain (3 at the radix-five
positions, 2 at the radix-four positions): the packed-header verifier spends one cycle less on exactly those chains.
`credited_card`: the weight-126 words with at least `creditFloor` credited digits number `count`. Same
packed-polynomial argument as `Counting.accepted_card`, with the statistic `credit + 64 * weight` (credit `≤ 54 < 64`),
so the set is one difference of two truncations. -/
namespace SigGolfResearch.NonbinaryTop.CreditCounting
open scoped BigOperators
open Codec Finset Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false

/-- The producer's credit threshold at the top layer. -/
def creditFloor : Nat := 9

def credit5 (d : Triple5) : Nat := ∑ i,if (d i).val=3 then 1 else 0
def credit4 (d : Triple4) : Nat := ∑ i,if (d i).val=2 then 1 else 0
/-- Number of digits equal to 3 (radix five) or 2 (radix four). -/
def credit (w : Word) : Nat := (∑ i,credit5 (w.1 i))+credit4 w.2
def g5 (n : Nat) : Nat := (if n=3 then 1 else 0)+64*n
def g4 (n : Nat) : Nat := (if n=2 then 1 else 0)+64*n
def s5 (d : Triple5) : Nat := ∑ i,g5 (d i).val
def s4 (d : Triple4) : Nat := ∑ i,g4 (d i).val
def stat (w : Word) : Nat := (∑ i,s5 (w.1 i))+s4 w.2

theorem s5_eq (d : Triple5) : s5 d=credit5 d+64*tripleSum5 d := by
  simp only [s5,g5,credit5,tripleSum5,Finset.sum_add_distrib,←Finset.mul_sum]

theorem s4_eq (d : Triple4) : s4 d=credit4 d+64*tripleSum4 d := by
  simp only [s4,g4,credit4,tripleSum4,Finset.sum_add_distrib,←Finset.mul_sum]

theorem stat_eq (w : Word) : stat w=credit w+64*weight w := by
  simp only [stat,s5_eq,s4_eq,credit,weight,Finset.sum_add_distrib,←Finset.mul_sum]
  ring

theorem credit5_le (d : Triple5) : credit5 d≤3 := by
  unfold credit5
  calc (∑ i : Fin 3,if (d i).val=3 then 1 else 0)≤∑ _i : Fin 3,1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = 3 := by simp

theorem credit4_le (d : Triple4) : credit4 d≤3 := by
  unfold credit4
  calc (∑ i : Fin 3,if (d i).val=2 then 1 else 0)≤∑ _i : Fin 3,1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = 3 := by simp

theorem credit_le (w : Word) : credit w≤54 := by
  have h1 : (∑ i,credit5 (w.1 i))≤∑ _i : Fin 17,3 := Finset.sum_le_sum fun i _ => credit5_le _
  have h2 := credit4_le w.2
  have h3 : (∑ _i : Fin 17,3)=51 := by simp
  unfold credit
  omega

def r5 (y : Nat) : Nat := 1+y^64+y^128+y^193+y^256
def r4 (y : Nat) : Nat := 1+y^64+y^129+y^192

theorem weighted5 (y : Nat) : (∑ d : Triple5,y^s5 d)=r5 y^3 := by
  calc (∑ d : Triple5,y^s5 d)=(∑ a : Fin 5,y^g5 a.val)^3 :=
        weighted_tuples (fun a : Fin 5 => g5 a.val) y 3
    _ = r5 y^3 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => y^g5 n) 5]
        norm_num [Finset.sum_range_succ,g5,r5]

theorem weighted4 (y : Nat) : (∑ d : Triple4,y^s4 d)=r4 y^3 := by
  calc (∑ d : Triple4,y^s4 d)=(∑ a : Fin 4,y^g4 a.val)^3 :=
        weighted_tuples (fun a : Fin 4 => g4 a.val) y 3
    _ = r4 y^3 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => y^g4 n) 4]
        norm_num [Finset.sum_range_succ,g4,r4]

theorem weighted_words (y : Nat) : (∑ w : Word,y^stat w)=r5 y^51*r4 y^3 := by
  rw [Fintype.sum_prod_type]
  simp only [stat,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted5,weighted4,←pow_mul]

def packed : Nat := r5 radix^51*r4 radix^3

theorem truncated_card (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun w : Word => stat w<cut).card=
      (packed%radix^cut)%(radix-1) := by
  classical
  unfold packed
  rw [←weighted_words radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ stat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le word_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_small))]

/-- Weight-126 words with credit at least `creditFloor = 9`. -/
def count : Nat := 169880087395417918897451495310468748

theorem exact_packed_count :
    (packed%radix^8128)%(radix-1)-(packed%radix^(8064+creditFloor))%(radix-1)=count := by decide +kernel

theorem credited_card :
    (Finset.univ.filter fun w : Word => weight w=126 ∧ creditFloor≤credit w).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w=126 ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => stat w<8128)\
        (Finset.univ.filter fun w : Word => stat w<8064+creditFloor) := by
    ext w
    have hc := credit_le w
    have he := stat_eq w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 8128 (by decide),truncated_card (8064+creditFloor) (by decide),exact_packed_count]
  · intro w hw
    have hf : creditFloor≤64 := by decide
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega

theorem credited_digest_card :
    ((Finset.univ.filter fun w : Word => weight w=126 ∧ creditFloor≤credit w).image digest).card=count := by
  classical
  rw [Finset.card_image_of_injective _ digest_injective,credited_card]

/-- Digests whose word a credit-filtering producer accepts. -/
theorem credited_decoder_count :
    Fintype.card {d : Fin (2^128) // ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w}=count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => weight w=126 ∧ creditFloor≤credit w).image digest := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨w,hw,hc⟩
      obtain ⟨hd,hweight⟩ := (Decoder.decode_some_iff d w).mp hw
      exact ⟨w,⟨hweight,hc⟩,hd⟩
    · rintro ⟨w,⟨hweight,hc⟩,hd⟩
      exact ⟨w,(Decoder.decode_some_iff d w).mpr ⟨hd,hweight⟩,hc⟩
  rw [he,credited_digest_card]

theorem probability_fraction : (count : ℚ)/2^128=
    169880087395417918897451495310468748/2^128 := by
  simp only [count,Nat.cast_ofNat]

end SigGolfResearch.NonbinaryTop.CreditCounting
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_card
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_decoder_count
