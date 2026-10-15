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
/-- Campaign T8D (NF17): accepted top words at target 144 with at least `creditFloor` = 7 credits (T3's legacy
`creditFloor 0`; the W9 producer floor 8 is counted in `Numerics.TopCreditCount`). -/
def count : Nat := 119055472510971231422674926968209380
theorem exact_packed_count :
    (packed%radix^9280)%(radix-1)-(packed%radix^(9216+creditFloor))%(radix-1)=count := by decide +kernel
theorem credited_card :
    (Finset.univ.filter fun w : Word => weight w=144 ∧ creditFloor≤credit w).card=count := by
  classical
  have hs : (Finset.univ.filter fun w : Word => weight w=144 ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => stat w<9280)\
        (Finset.univ.filter fun w : Word => stat w<9216+creditFloor) := by
    ext w
    have hc := credit_le w
    have he := stat_eq w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [hs,Finset.card_sdiff_of_subset]
  · rw [truncated_card 9280 (by decide),truncated_card (9216+creditFloor) (by decide),exact_packed_count]
  · intro w hw
    have hf : creditFloor≤64 := by decide
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    omega
theorem credited_digest_card :
    ((Finset.univ.filter fun w : Word => weight w=144 ∧ creditFloor≤credit w).image digest).card=count := by
  classical
  rw [Finset.card_image_of_injective _ digest_injective,credited_card]
theorem credited_decoder_count :
    Fintype.card {d : Fin (2^128) // ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w}=count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => ∃ w,Decoder.decode d=some w ∧ creditFloor≤credit w)=
      (Finset.univ.filter fun w : Word => weight w=144 ∧ creditFloor≤credit w).image digest := by
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
    119055472510971231422674926968209380/2^128 := by
  simp only [count,Nat.cast_ofNat]
end SigGolfResearch.NonbinaryTop.CreditCounting
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.exact_packed_count
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_card
#print axioms SigGolfResearch.NonbinaryTop.CreditCounting.credited_decoder_count
end

section

namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
theorem creditFloor_top : creditFloor 0=CreditCounting.creditFloor := rfl
theorem searchDecode_some {lay : Layer} {value : Digest} {digits : List Nat}
    (h : searchDecode lay value=some digits) : decode lay value=some digits := by
  unfold searchDecode at h
  by_cases hc : encCredit lay value<creditFloor lay
  · rw [if_pos hc] at h; cases h
  · rwa [if_neg hc] at h
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
theorem range54_map_ofFn (f : Nat → Nat) :
    (List.range 54).map f=List.ofFn (fun i : Fin 54 => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
theorem topCredit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 (topFlip v).toNat=some w) : topCredit v=CreditCounting.credit w := by
  unfold topCredit
  rw [range54_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => if coreDigit 0 v i.val=(if i.val<51 then 3 else 6) then 1 else 0).sum+
      (List.ofFn fun k : Fin 3 =>
        if coreDigit 0 v (51+k.val)=(if 51+k.val<51 then 3 else 6) then 1 else 0).sum=CreditCounting.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold CreditCounting.credit CreditCounting.credit5 CreditCounting.credit8
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := coreDigit_parse5 hp j k
    rw [Nat.mul_comm 3 j.val] at he
    have hlt : j.val*3+k.val<51 := by have := j.isLt;have := k.isLt;omega
    show (if coreDigit 0 v (j.val*3+k.val)=(if j.val*3+k.val<51 then 3 else 6) then 1 else 0)=
      if (w.1 j k).val=3 then 1 else 0
    rw [if_pos hlt,he]
  · apply Finset.sum_congr rfl
    intro k hk
    have he := coreDigit_parse8 hp k
    show (if coreDigit 0 v (51+k.val)=(if 51+k.val<51 then 3 else 6) then 1 else 0)=
      if (w.2 k).val=6 then 1 else 0
    have hn : ¬(51+k.val<51) := by omega
    rw [if_neg hn,he]
theorem decodeBV_parse {v : Digest} {w : Codec.Word} (hw : Decoder.decodeBV v=some w) :
    Decoder.parse 17 v.toNat=some w := by
  change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=144))=some w at hw
  exact (Option.filter_eq_some_iff.mp hw).1
theorem searchDecode_top_isSome (v : Digest) :
    (searchDecode 0 v).isSome=true ↔
      ∃ w,Decoder.decodeBV (topFlip v)=some w ∧ creditFloor 0≤CreditCounting.credit w := by
  constructor
  · intro h
    obtain ⟨ds,hds⟩ := Option.isSome_iff_exists.mp h
    have hm := searchDecode_some hds
    rw [decode_top_eq_map] at hm
    cases hw : Decoder.decodeBV (topFlip v) with
    | none => simp [hw] at hm
    | some w =>
    refine ⟨w,rfl,?_⟩
    rw [←topCredit_parse (decodeBV_parse hw)]
    exact searchDecode_top_credit hds
  · rintro ⟨w,hw,hc⟩
    have hd : decode 0 v=some (wordDigits w) := by rw [decode_top_eq_map,hw]; rfl
    rw [searchDecode_top_of hd (by rw [topCredit_parse (decodeBV_parse hw)]; exact hc)]
    rfl
theorem searchDecode_top_count :
    Fintype.card {v : Digest // (searchDecode 0 v).isSome=true}=CreditCounting.count := by
  classical
  let e : Digest ≃ Fin (2^128) := ⟨fun v => (topFlip v).toFin,fun d => topFlip (BitVec.ofFin d),
    fun v => by simp [topFlip_topFlip],fun d => by simp [topFlip_topFlip]⟩
  rw [Fintype.card_congr (e.subtypeEquiv (p := fun v => (searchDecode 0 v).isSome=true)
    (q := fun d => ∃ w,Decoder.decode d=some w ∧ CreditCounting.creditFloor≤CreditCounting.credit w)
    (fun v => searchDecode_top_isSome v))]
  convert CreditCounting.credited_decoder_count
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.topCredit_parse
#print axioms SigGolfCandidate.T3.Nonbinary.searchDecode_top_count
end
