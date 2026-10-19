import SigGolfCandidate.T3.Nonbinary.SourceEncoding

section


namespace SigGolfResearch.NonbinaryTop.CreditCounting
open scoped BigOperators
open Codec Finset Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false
def creditFloor : Nat := 7
def credit5 (d : Triple5) : Nat := ∑ i,if (d i).val=3 then 1 else 0
def credit8 (d : Triple8) : Nat := ∑ i,if (d i).val=6 then 1 else 0
def credit (w : Word) : Nat := (∑ i,credit5 (w.1 i))+credit8 w.2
def g5 (n : Nat) : Nat := (if n=3 then 1 else 0)+64*n
def g8 (n : Nat) : Nat := (if n=6 then 1 else 0)+64*n
def s5 (d : Triple5) : Nat := ∑ i,g5 (d i).val
def s8 (d : Triple8) : Nat := ∑ i,g8 (d i).val
def stat (w : Word) : Nat := (∑ i,s5 (w.1 i))+s8 w.2
theorem s5_eq (d : Triple5) : s5 d=credit5 d+64*tripleSum5 d := by
  simp only [s5,g5,credit5,tripleSum5,Finset.sum_add_distrib,←Finset.mul_sum]
theorem s8_eq (d : Triple8) : s8 d=credit8 d+64*tripleSum8 d := by
  simp only [s8,g8,credit8,tripleSum8,Finset.sum_add_distrib,←Finset.mul_sum]
theorem stat_eq (w : Word) : stat w=credit w+64*weight w := by
  simp only [stat,s5_eq,s8_eq,credit,weight,Finset.sum_add_distrib,←Finset.mul_sum]
  ring
theorem credit5_le (d : Triple5) : credit5 d≤3 := by
  unfold credit5
  calc (∑ i : Fin 3,if (d i).val=3 then 1 else 0)≤∑ _i : Fin 3,1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = 3 := by simp
theorem credit8_le (d : Triple8) : credit8 d≤3 := by
  unfold credit8
  calc (∑ i : Fin 3,if (d i).val=6 then 1 else 0)≤∑ _i : Fin 3,1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = 3 := by simp
theorem credit_le (w : Word) : credit w≤54 := by
  have h1 : (∑ i,credit5 (w.1 i))≤∑ _i : Fin 17,3 := Finset.sum_le_sum fun i _ => credit5_le _
  have h2 := credit8_le w.2
  have h3 : (∑ _i : Fin 17,3)=51 := by simp
  unfold credit
  omega
def r5 (y : Nat) : Nat := 1+y^64+y^128+y^193+y^256
def r8 (y : Nat) : Nat := 1+y^64+y^128+y^192+y^256+y^320+y^385+y^448
theorem weighted5 (y : Nat) : (∑ d : Triple5,y^s5 d)=r5 y^3 := by
  calc (∑ d : Triple5,y^s5 d)=(∑ a : Fin 5,y^g5 a.val)^3 :=
        weighted_tuples (fun a : Fin 5 => g5 a.val) y 3
    _ = r5 y^3 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => y^g5 n) 5]
        norm_num [Finset.sum_range_succ,g5,r5]
theorem weighted8 (y : Nat) : (∑ d : Triple8,y^s8 d)=r8 y^3 := by
  calc (∑ d : Triple8,y^s8 d)=(∑ a : Fin 8,y^g8 a.val)^3 :=
        weighted_tuples (fun a : Fin 8 => g8 a.val) y 3
    _ = r8 y^3 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => y^g8 n) 8]
        norm_num [Finset.sum_range_succ,g8,r8]
theorem weighted_words (y : Nat) : (∑ w : Word,y^stat w)=r5 y^51*r8 y^3 := by
  rw [Fintype.sum_prod_type]
  simp only [stat,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted5,weighted8,←pow_mul]
def packed : Nat := r5 radix^51*r8 radix^3
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
/-- Accepted top words at target 146 with the legacy T3 credit floor7. The W9 producer
uses a separate effective-credit count. -/
def count : Nat := 67567856205106535693258756678239530
theorem exact_packed_count :
    (packed%radix^9408)%(radix-1)-(packed%radix^(9344+creditFloor))%(radix-1)=count := by decide +kernel
theorem credited_card :
    (Finset.univ.filter fun w : Word => weight w=146 ∧ creditFloor≤credit w).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w=146 ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => stat w<9408)\
        (Finset.univ.filter fun w : Word => stat w<9344+creditFloor) := by
    ext w
    have hc := credit_le w
    have he := stat_eq w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 9408 (by decide),truncated_card (9344+creditFloor) (by decide),exact_packed_count]
  · intro w hw
    have hf : creditFloor≤64 := by decide
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega
theorem credited_digest_card :
    ((Finset.univ.filter fun w : Word => weight w=146 ∧ creditFloor≤credit w).image digest).card=count := by
  classical
  rw [Finset.card_image_of_injective _ digest_injective,credited_card]
theorem credited_decoder_count :
    Fintype.card {d : Fin (2^128) // ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w}=count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => weight w=146 ∧ creditFloor≤credit w).image digest := by
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
    67567856205106535693258756678239530/2^128 := by
  simp only [count,Nat.cast_ofNat]
end SigGolfResearch.NonbinaryTop.CreditCounting
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_card
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_decoder_count
/-! ### Campaign R6: the legacy T3 credited top count (`searchDecode 0`: broad R6 decoder and credit floor 7)
The legacy credit counts the digits one below their maximum: radix-6 digit 4, radix-5 digit 3 and the checksum digit 6.
An R6 word in the checksum window is counted together with its checksum digit `153 - weight` (`XWord`), so the credited
words are one interval of the statistic `credit + 64 * weight` (as `CreditCounting.credited_card` for NF17). -/
namespace SigGolfResearch.NonbinaryTop.R6Credit
open scoped BigOperators
open Codec Finset Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option linter.constructorNameAsVariable false
def credit6 (d : Triple6) : Nat := ∑ i,if (d i).val=4 then 1 else 0
def g6 (n : Nat) : Nat := (if n=4 then 1 else 0)+64*n
def s6 (d : Triple6) : Nat := ∑ i,g6 (d i).val
theorem s6_eq (d : Triple6) : s6 d=credit6 d+64*R6.tripleSum6 d := by
  simp only [s6,g6,credit6,R6.tripleSum6,Finset.sum_add_distrib,←Finset.mul_sum]
theorem credit6_le (d : Triple6) : credit6 d≤3 := by
  unfold credit6
  calc (∑ i : Fin 3,if (d i).val=4 then 1 else 0)≤∑ _i : Fin 3,1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = 3 := by simp
/-- Data credit of an R6 word (chains 0..50). -/
def credit (w : R6.Word) : Nat := (∑ g,credit6 (w.1 g))+∑ q,CreditCounting.credit5 (w.2 q)
/-- Legacy T3 credit of the decoded top digits of an R6 word: data credit and checksum credit (`153 - weight = 6`). -/
def fullCredit (w : R6.Word) : Nat := credit w+(if 153-R6.weight w=6 then 1 else 0)
def wstat (w : R6.Word) : Nat := (∑ g,s6 (w.1 g))+∑ q,CreditCounting.s5 (w.2 q)
/-- An R6 word with an explicit checksum digit. -/
abbrev XWord := R6.Word × Fin 8
def xweight (x : XWord) : Nat := R6.weight x.1+x.2.val
def xcredit (x : XWord) : Nat := credit x.1+(if x.2.val=6 then 1 else 0)
def xstat (x : XWord) : Nat := wstat x.1+CreditCounting.g8 x.2.val
theorem xstat_eq (x : XWord) : xstat x=xcredit x+64*xweight x := by
  simp only [xstat,wstat,s6_eq,CreditCounting.s5_eq,xcredit,credit,xweight,R6.weight,CreditCounting.g8,
    Finset.sum_add_distrib,←Finset.mul_sum]
  ring
theorem xcredit_le (x : XWord) : xcredit x≤52 := by
  have h1 : (∑ g,credit6 (x.1.1 g))≤∑ _g : Fin 8,3 := Finset.sum_le_sum fun g _ => credit6_le _
  have h2 : (∑ q,CreditCounting.credit5 (x.1.2 q))≤∑ _q : Fin 9,3 :=
    Finset.sum_le_sum fun q _ => CreditCounting.credit5_le _
  have h3 : (∑ _g : Fin 8,3)=24 := by simp
  have h4 : (∑ _q : Fin 9,3)=27 := by simp
  unfold xcredit credit
  split_ifs <;> omega
def r6 (y : Nat) : Nat := 1+y^64+y^128+y^192+y^257+y^320
theorem weighted6 (y : Nat) : (∑ d : Triple6,y^s6 d)=r6 y^3 := by
  calc (∑ d : Triple6,y^s6 d)=(∑ a : Fin 6,y^g6 a.val)^3 :=
        weighted_tuples (fun a : Fin 6 => g6 a.val) y 3
    _ = r6 y^3 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => y^g6 n) 6]
        norm_num [Finset.sum_range_succ,g6,r6]
theorem weighted_g8 (y : Nat) : (∑ c : Fin 8,y^CreditCounting.g8 c.val)=CreditCounting.r8 y := by
  rw [Fin.sum_univ_eq_sum_range (fun n => y^CreditCounting.g8 n) 8]
  norm_num [Finset.sum_range_succ,CreditCounting.g8,CreditCounting.r8]
theorem weighted_words (y : Nat) : (∑ w : R6.Word,y^wstat w)=r6 y^24*CreditCounting.r5 y^27 := by
  rw [Fintype.sum_prod_type]
  simp only [wstat,pow_add]
  rw [←Finset.sum_mul_sum,weighted_tuples,weighted_tuples,weighted6,CreditCounting.weighted5,←pow_mul,←pow_mul]
theorem weighted_xwords (y : Nat) :
    (∑ x : XWord,y^xstat x)=r6 y^24*CreditCounting.r5 y^27*CreditCounting.r8 y := by
  rw [Fintype.sum_prod_type]
  simp only [xstat,pow_add]
  rw [←Finset.sum_mul_sum,weighted_words,weighted_g8]
def packed : Nat := r6 radix^24*CreditCounting.r5 radix^27*CreditCounting.r8 radix
theorem xword_card_small : Fintype.card XWord<radix-1 := by
  norm_num [XWord,R6.Word,Triple6,Triple5,Fintype.card_prod,Fintype.card_fun,radix]
theorem truncated_card (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun x : XWord => xstat x<cut).card=(packed%radix^cut)%(radix-1) := by
  classical
  unfold packed
  rw [←weighted_xwords radix]
  symm
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hc _ xstat
      (by simpa only [Finset.card_univ] using Nat.lt_of_lt_of_le xword_card_small (Nat.sub_le _ _)),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic (by norm_num [radix]),
    Nat.mod_eq_of_lt ((Finset.card_filter_le _ _).trans_lt (by simpa using xword_card_small))]
/-- R6 top words accepted by the legacy T3 search decoder (checksum window and credit at least 7). -/
def count : Nat := 70924784661680998479659805406180633
theorem exact_packed_count :
    (packed%radix^9856)%(radix-1)-(packed%radix^9799)%(radix-1)=count := by decide +kernel
theorem xcredited_card :
    (Finset.univ.filter fun x : XWord => xweight x=153 ∧ 7≤xcredit x).card=count := by
  classical
  have hs : (Finset.univ.filter fun x : XWord => xweight x=153 ∧ 7≤xcredit x)=
      (Finset.univ.filter fun x : XWord => xstat x<9856)\(Finset.univ.filter fun x : XWord => xstat x<9799) := by
    ext x
    have hc := xcredit_le x
    have he := xstat_eq x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 9856 (by decide),truncated_card 9799 (by decide),exact_packed_count]
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    omega
/-- An R6 word with its checksum digit `153 - weight` (mod 8; exact in the checksum window). -/
def toX (w : R6.Word) : XWord := (w,⟨(153-R6.weight w)%8,Nat.mod_lt _ (by decide)⟩)
/-- The legacy credited R6 count: checksum window and full credit (checksum included) at least 7. -/
theorem credited_card :
    (Finset.univ.filter fun w : R6.Word => R6.weight w≤153 ∧ 153-R6.weight w<8 ∧ 7≤fullCredit w).card=count := by
  rw [←xcredited_card]
  refine Finset.card_bij' (fun w _ => toX w) (fun x _ => x.1) (fun w hw => ?_) (fun x hx => ?_) (fun w _ => rfl)
    (fun x hx => ?_)
  · rw [Finset.mem_filter] at hw
    rw [Finset.mem_filter, and_iff_right (by simp only [Finset.mem_univ])]
    obtain ⟨-,h1,h2,h3⟩ := hw
    have hm : (153-R6.weight w)%8=153-R6.weight w := Nat.mod_eq_of_lt h2
    refine ⟨?_,?_⟩
    · show R6.weight w+(153-R6.weight w)%8=153
      omega
    · show 7≤credit w+(if (153-R6.weight w)%8=6 then 1 else 0)
      rw [hm]; exact h3
  · rw [Finset.mem_filter] at hx
    rw [Finset.mem_filter, and_iff_right (by simp only [Finset.mem_univ])]
    obtain ⟨-,h1,h2⟩ := hx
    have h8 := x.2.isLt
    have h1' : R6.weight x.1+x.2.val=153 := h1
    have he : 153-R6.weight x.1=x.2.val := by omega
    refine ⟨by omega,by omega,?_⟩
    show 7≤credit x.1+(if 153-R6.weight x.1=6 then 1 else 0)
    rw [he]; exact h2
  · rw [Finset.mem_filter] at hx
    have h1' : R6.weight x.1+x.2.val=153 := hx.2.1
    have h8 := x.2.isLt
    refine Prod.ext rfl (Fin.ext ?_)
    show (153-R6.weight x.1)%8=x.2.val
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
end SigGolfResearch.NonbinaryTop.R6Credit
#print axioms SigGolfResearch.NonbinaryTop.R6Credit.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.R6Credit.credited_card
end

section

namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
theorem creditFloor_top : creditFloor 0=CreditCounting.creditFloor := rfl
theorem searchDecode_eq_none_or (lay : Layer) (value : Digest) :
    searchDecode lay value=none ∨ searchDecode lay value=decode lay value := by
  unfold searchDecode
  by_cases hc : encCredit lay value<creditFloor lay
  · left; rw [if_pos hc]
  · right; rw [if_neg hc]
theorem creditFloor_lower {lay : Layer} (hl : lay≠0) : creditFloor lay=0 := by
  fin_cases lay
  · exact absurd rfl hl
  all_goals rfl
theorem searchDecode_lower {lay : Layer} (hl : lay≠0) (value : Digest) :
    searchDecode lay value=decode lay value := by
  unfold searchDecode
  rw [creditFloor_lower hl,if_neg (Nat.not_lt_zero _)]
theorem searchDecode_credit {lay : Layer} {value : Digest} {digits : List Nat}
    (h : searchDecode lay value=some digits) : creditFloor lay≤encCredit lay value := by
  unfold searchDecode at h
  by_contra hc
  rw [if_pos (Nat.lt_of_not_le hc)] at h
  cases h
theorem encCredit_top (value : Digest) : encCredit 0 value=topCredit value := by
  unfold encCredit
  rw [if_pos rfl]
theorem searchDecode_top_credit {value : Digest} {digits : List Nat}
    (h : searchDecode 0 value=some digits) : creditFloor 0≤topCredit value := by
  rw [←encCredit_top]
  exact searchDecode_credit h
theorem searchDecode_of {lay : Layer} {value : Digest} {digits : List Nat}
    (hd : decode lay value=some digits) (hc : creditFloor lay≤encCredit lay value) :
    searchDecode lay value=some digits := by
  unfold searchDecode
  rw [if_neg (Nat.not_lt.mpr hc)]
  exact hd
theorem searchDecode_top_of {value : Digest} {digits : List Nat}
    (hd : decode 0 value=some digits) (hc : creditFloor 0≤topCredit value) :
    searchDecode 0 value=some digits :=
  searchDecode_of hd (by rw [encCredit_top]; exact hc)
/-- Campaign R6: the legacy T3 top credit of a valid top word, read from its R6 word (52 digits, checksum included). -/
theorem topCredit_r6 {v : Digest} (h : topRanksValid v = true) :
    topCredit v = ((List.range 52).map fun i =>
      if (r6Full (r6Word v)).getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum := by
  unfold topCredit r6Full
  rw [dataDigits_r6 h, r6Digits_sum]
theorem credit_term_r6 (w : R6.Word) (g : Fin 8) (k : Nat) (hk : k < 3) :
    (if (r6Full w).getD (3 * g.val + k) 0 + 1 = maxDigit 0 (3 * g.val + k) then 1 else 0) =
      (if (w.1 g ⟨k, hk⟩).val = 4 then 1 else 0) := by
  have h : 3 * g.val + k < 24 := by omega
  have hd : r6Digit w (3 * g.val + k) = (w.1 g ⟨k, hk⟩).val := r6Digit_r6 w g ⟨k, hk⟩
  have hm : maxDigit 0 (3 * g.val + k) = 5 := by simp [maxDigit, h]
  rw [r6Full_getD, if_pos (show 3 * g.val + k < 51 by omega), hd, hm]
  split_ifs <;> omega
theorem credit_term_r5 (w : R6.Word) (q : Fin 9) (k : Nat) (hk : k < 3) :
    (if (r6Full w).getD (24 + (3 * q.val + k)) 0 + 1 = maxDigit 0 (24 + (3 * q.val + k)) then 1 else 0) =
      (if (w.2 q ⟨k, hk⟩).val = 3 then 1 else 0) := by
  have h : ¬ (24 + (3 * q.val + k) < 24) := by omega
  have h' : 24 + (3 * q.val + k) < 51 := by omega
  have hd : r6Digit w (24 + (3 * q.val + k)) = (w.2 q ⟨k, hk⟩).val := by
    rw [← Nat.add_assoc]; exact r6Digit_r5 w q ⟨k, hk⟩
  have hm : maxDigit 0 (24 + (3 * q.val + k)) = 4 := by simp [maxDigit, h, h']
  rw [r6Full_getD, if_pos h', hd, hm]
  split_ifs <;> omega
/-- The legacy top credit of the decoded digits of an R6 word (`r6Full`) in closed form. -/
theorem credit_r6Full (w : R6.Word) :
    ((List.range 52).map fun i => if (r6Full w).getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum =
      R6Credit.fullCredit w := by
  rw [list_sum_range_map, Finset.sum_range_succ, show Finset.range 51 = Finset.range (24 + 27) from rfl,
    Finset.sum_range_add]
  have hA : ∑ i ∈ Finset.range 24, (if (r6Full w).getD i 0 + 1 = maxDigit 0 i then 1 else 0) =
      ∑ g, R6Credit.credit6 (w.1 g) := by
    rw [show Finset.range 24 = Finset.range (3 * 8) from rfl, sum_range_triples, Finset.sum_range]
    refine Finset.sum_congr rfl fun g _ => ?_
    have t0 : (if (r6Full w).getD (3 * g.val) 0 + 1 = maxDigit 0 (3 * g.val) then 1 else 0) = _ :=
      credit_term_r6 w g 0 (by decide)
    have t1 := credit_term_r6 w g 1 (by decide)
    have t2 := credit_term_r6 w g 2 (by decide)
    rw [t0, t1, t2, R6Credit.credit6, Fin.sum_univ_three]
    rfl
  have hB : ∑ x ∈ Finset.range 27, (if (r6Full w).getD (24 + x) 0 + 1 = maxDigit 0 (24 + x) then 1 else 0) =
      ∑ q, CreditCounting.credit5 (w.2 q) := by
    rw [show Finset.range 27 = Finset.range (3 * 9) from rfl, sum_range_triples, Finset.sum_range]
    refine Finset.sum_congr rfl fun q _ => ?_
    have t0 : (if (r6Full w).getD (24 + 3 * q.val) 0 + 1 = maxDigit 0 (24 + 3 * q.val) then 1 else 0) = _ :=
      credit_term_r5 w q 0 (by decide)
    have t1 := credit_term_r5 w q 1 (by decide)
    have t2 := credit_term_r5 w q 2 (by decide)
    rw [t0, t1, t2, CreditCounting.credit5, Fin.sum_univ_three]
    rfl
  have hC : (if (r6Full w).getD 51 0 + 1 = maxDigit 0 51 then 1 else 0) =
      if 153 - R6.weight w = 6 then 1 else 0 := by
    rw [r6Full_getD, if_neg (show ¬ (51 < 51) by decide), if_pos rfl, show target 0 = 153 from rfl,
      show maxDigit 0 51 = 7 from rfl]
    split_ifs <;> omega
  rw [hA, hB, hC]
  rfl
/-- The legacy top credit of a valid top word in closed form: data credit of its R6 word and the checksum credit. -/
theorem topCredit_full {v : Digest} (h : topRanksValid v = true) :
    topCredit v = R6Credit.fullCredit (r6Word v) := by
  rw [topCredit_r6 h, credit_r6Full]
theorem searchDecode_top_isSome (v : Digest) :
    (searchDecode 0 v).isSome=true ↔
      topRanksValid v=true ∧ (R6.weight (r6Word v)≤153 ∧ 153-R6.weight (r6Word v)<8 ∧
        7≤R6Credit.fullCredit (r6Word v)) := by
  unfold searchDecode
  rw [encCredit_top, creditFloor_top]
  by_cases hv : topRanksValid v=true
  · rw [topCredit_full hv]
    have hw := decode_top_isSome_r6 v
    unfold r6Window at hw
    rw [show target 0 = 153 from rfl] at hw
    by_cases hc : R6Credit.fullCredit (r6Word v)<CreditCounting.creditFloor
    · rw [if_pos hc]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and, not_le]
      intro _ _ _
      exact hc
    · rw [if_neg hc, hw]
      simp only [CreditCounting.creditFloor] at hc ⊢
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, by omega⟩
      · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
  · have hn : (decode 0 v).isSome = false := by
      cases hd : (decode 0 v).isSome
      · rfl
      · exact absurd ((decode_top_isSome_r6 v).mp hd).1 hv
    split_ifs <;> simp_all
/-- Campaign R6: the legacy T3 search decoder accepts exactly `R6Credit.count` top words. -/
theorem searchDecode_top_count :
    Fintype.card {v : Digest // (searchDecode 0 v).isSome=true}=R6Credit.count := by
  classical
  rw [Fintype.card_subtype]
  simp_rw [searchDecode_top_isSome]
  rw [card_valid_transport (fun w => R6.weight w≤153 ∧ 153-R6.weight w<8 ∧ 7≤R6Credit.fullCredit w)]
  exact R6Credit.credited_card
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.topCredit_full
#print axioms SigGolfCandidate.T3.Nonbinary.searchDecode_top_count
end
