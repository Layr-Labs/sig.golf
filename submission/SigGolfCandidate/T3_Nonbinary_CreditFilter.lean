import SigGolfCandidate.T3_Nonbinary_SourceEncoding

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
theorem decodeBV_parse {v : Digest} {w : Codec.Word} (hw : Decoder.decodeBV v=some w) :
    Decoder.parse 17 v.toNat=some w := by
  change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=146))=some w at hw
  exact (Option.filter_eq_some_iff.mp hw).1
end SigGolfCandidate.T3.Nonbinary
end

/-! ### Campaign T51: the legacy search decoder (`topCredit ≥ 7`) through the T51 model word -/
section
namespace SigGolfResearch.T51Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

theorem ind_le (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split_ifs <;> omega
theorem ind_cases (p : Prop) [Decidable p] : (p ∧ ind p = 1) ∨ (¬p ∧ ind p = 0) := by
  by_cases h : p
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩
theorem ind_pos {p : Prop} [Decidable p] (h : p) : ind p = 1 := if_pos h
theorem ind_neg {p : Prop} [Decidable p] (h : ¬p) : ind p = 0 := if_neg h
theorem ind_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : ind p = ind q := by
  unfold ind; by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

theorem fiber_card {ι M : Type} [DecidableEq M] (f : ι → M) (s : Finset ι) (t : Finset M)
    (H : ∀ a ∈ s, f a ∈ t) : s.card = ∑ b ∈ t, (s.filter fun a => f a = b).card :=
  Finset.card_eq_sum_card_fiberwise fun a ha => H a ha

theorem fiber_card_filter {ι M : Type} [Fintype ι] [DecidableEq M] (Q : ι → Prop) [DecidablePred Q]
    (f : ι → M) (t : Finset M) (H : ∀ a, Q a → f a ∈ t) :
    (univ.filter Q).card = ∑ b ∈ t, ((univ.filter Q).filter fun a => f a = b).card :=
  fiber_card f _ t (fun a ha => H a (Finset.mem_filter.mp ha).2)

/-! ### Legacy credit count (the legacy T3 `searchDecode`: `topCredit ≥ 7`) -/
def tcreditAll (w : Word) : Nat :=
  (∑ g : Fin 9, tcredit 6 (w.1 g).val) + (∑ j : Fin 7, tcredit 5 (w.2.1 j).val) + pcredit w.2.2.val
def legacyS : GStat := ⟨fun _ r => 64 * tsum 6 r + tcredit 6 r, fun _ r => 64 * tsum 5 r + tcredit 5 r,
  fun r => 64 * psum r + pcredit r⟩
theorem legacyS_eval (w : Word) : legacyS.eval w = 64 * weight w + tcreditAll w := by
  simp only [GStat.eval, legacyS, weight, tcreditAll, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem tcredit6_le (r : Fin 216) : tcredit 6 r.val ≤ 3 := by revert r; decide +kernel
theorem tcredit5_le (r : Fin 125) : tcredit 5 r.val ≤ 3 := by revert r; decide +kernel
theorem pcredit_le (r : Fin 49) : pcredit r.val ≤ 2 := by revert r; decide +kernel
theorem tcreditAll_le (w : Word) : tcreditAll w ≤ 50 := by
  have h6 : (∑ g : Fin 9, tcredit 6 (w.1 g).val) ≤ ∑ _g : Fin 9, 3 :=
    Finset.sum_le_sum fun g _ => tcredit6_le (w.1 g)
  have h5 : (∑ j : Fin 7, tcredit 5 (w.2.1 j).val) ≤ ∑ _j : Fin 7, 3 :=
    Finset.sum_le_sum fun j _ => tcredit5_le (w.2.1 j)
  have hp := pcredit_le w.2.2
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h6 h5
  unfold tcreditAll; omega

def lcut : Nat := 64 * 153
def packedL : Nat := packedG lcut legacyS false
attribute [irreducible] packedL

/-- The legacy accepted words: decodable (`147 ≤ weight ≤ 152`) with at least 7 credited chains, the checksum chain
included (credited iff its digit `152 - weight` is 4). -/
def legacyOk (w : Word) : Prop := 147 ≤ weight w ∧ weight w ≤ 152 ∧ 7 ≤ tcreditAll w + ind (weight w = 148)
instance : DecidablePred legacyOk := fun w => by unfold legacyOk; infer_instance

/-- The admissible `(weight, credits)` keys of a legacy-accepted word. -/
def legacyKeys : List (Nat × Nat) :=
  ((List.range 6).flatMap fun i => (List.range 51).map fun c => (147 + i, c)).filter
    fun pr => decide (7 ≤ pr.2 + ind (pr.1 = 148))
def legacyCountP (p : Nat) : Nat := (legacyKeys.map fun pr => p / B ^ (64 * pr.1 + pr.2) % B).sum

theorem legacyKeys_nodup : legacyKeys.Nodup := by decide
theorem mem_legacyKeys (s c : Nat) : (s, c) ∈ legacyKeys ↔ 147 ≤ s ∧ s ≤ 152 ∧ c ≤ 50 ∧ 7 ≤ c + ind (s = 148) := by
  simp only [legacyKeys, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl, rfl⟩, h⟩; exact ⟨by omega, by omega, by omega, h⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨s - 147, by omega, c, by omega, by omega, rfl⟩, h4⟩
attribute [irreducible] legacyKeys

theorem legacy_card : (univ.filter legacyOk).card = legacyCountP packedL := by
  classical
  unfold legacyCountP
  rw [← List.sum_toFinset _ legacyKeys_nodup,
    fiber_card_filter legacyOk (fun w => (weight w, tcreditAll w)) legacyKeys.toFinset (fun w hw => by
      obtain ⟨h1, h2, h3⟩ := hw
      exact List.mem_toFinset.mpr ((mem_legacyKeys _ _).mpr ⟨h1, h2, tcreditAll_le w, h3⟩))]
  apply Finset.sum_congr rfl
  intro pr hpr
  obtain ⟨s, c⟩ := pr
  obtain ⟨h1, h2, h3, h4⟩ := (mem_legacyKeys s c).mp (List.mem_toFinset.mp hpr)
  rw [packedL, packedG_digit _ _ _ _ (by unfold lcut; omega), Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [legacyS_eval]
  have hc := tcreditAll_le w
  unfold legacyOk
  simp only [Prod.mk.injEq, Bool.false_eq_true, false_implies, true_and]
  constructor
  · rintro ⟨-, rfl, rfl⟩; rfl
  · intro h
    have e1 : weight w = s := by omega
    have e2 : tcreditAll w = c := by omega
    subst e1 e2
    exact ⟨⟨h1, h2, h4⟩, rfl, rfl⟩

/-- The legacy T3 search-decoder count (credit floor 7 on the 51 chains). -/
def legacyCount : Nat := 58354217001057952582130682281963303
theorem legacyCount_digits : legacyCountP packedL = legacyCount := by decide +kernel

theorem getD_digits (v : Digest) (chk i : Nat) :
    (dataDigits 0 v ++ [chk]).getD i 0 = if i < 50 then coreDigit 0 v i else if i = 50 then chk else 0 := by
  have hl : (dataDigits 0 v).length = 50 := by simp [dataDigits, dataCount]
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

theorem sum_51 (f : Nat → Nat) :
    ∑ i ∈ range 51, f i = (∑ g : Fin 9, (f (3 * g.val) + f (3 * g.val + 1) + f (3 * g.val + 2))) +
      (∑ j : Fin 7, (f (3 * (9 + j.val)) + f (3 * (9 + j.val) + 1) + f (3 * (9 + j.val) + 2))) +
        (f 48 + f 49) + f 50 := by
  rw [Finset.sum_range_succ, sum_50]

theorem getD6 (w : Word) (chk : Nat) (g : Fin 9) (k : Nat) (hk : k < 3) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + k) 0 = dg 6 (w.1 g).val k := by
  rw [getD_digits, if_pos (by omega), core_encode6 w g k hk]
theorem getD5 (w : Word) (chk : Nat) (j : Fin 7) (k : Nat) (hk : k < 3) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + j.val) + k) 0 = dg 5 (w.2.1 j).val k := by
  rw [getD_digits, if_pos (by omega), core_encode5 w j k hk]
theorem getD48 (w : Word) (chk : Nat) : (dataDigits 0 (encode w) ++ [chk]).getD 48 0 = dg 7 w.2.2.val 0 := by
  rw [getD_digits, if_pos (by omega)]; exact core_encode7 w 0 (by decide)
theorem getD49 (w : Word) (chk : Nat) : (dataDigits 0 (encode w) ++ [chk]).getD 49 0 = dg 7 w.2.2.val 1 := by
  rw [getD_digits, if_pos (by omega)]; exact core_encode7 w 1 (by decide)
theorem getD50 (w : Word) (chk : Nat) : (dataDigits 0 (encode w) ++ [chk]).getD 50 0 = chk := by
  rw [getD_digits, if_neg (by omega), if_pos rfl]
theorem max6 (g : Fin 9) (k : Nat) (hk : k < 3) : maxDigit 0 (3 * g.val + k) = 5 := by
  have := g.isLt; unfold maxDigit; simp only [if_true]; rw [if_pos (by omega)]
theorem max5 (j : Fin 7) (k : Nat) (hk : k < 3) : maxDigit 0 (3 * (9 + j.val) + k) = 4 := by
  have := j.isLt; unfold maxDigit; simp only [if_true]; rw [if_neg (by omega), if_pos (by omega)]

theorem blk6 (w : Word) (chk : Nat) (g : Fin 9) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val) 0 = dg 6 (w.1 g).val 0 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 1) 0 = dg 6 (w.1 g).val 1 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 2) 0 = dg 6 (w.1 g).val 2 ∧
    maxDigit 0 (3 * g.val) = 5 ∧ maxDigit 0 (3 * g.val + 1) = 5 ∧ maxDigit 0 (3 * g.val + 2) = 5 :=
  ⟨by simpa using getD6 w chk g 0 (by decide), getD6 w chk g 1 (by decide), getD6 w chk g 2 (by decide),
    by simpa using max6 g 0 (by decide), max6 g 1 (by decide), max6 g 2 (by decide)⟩
theorem blk5 (w : Word) (chk : Nat) (j : Fin 7) :
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + j.val)) 0 = dg 5 (w.2.1 j).val 0 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + j.val) + 1) 0 = dg 5 (w.2.1 j).val 1 ∧
    (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + j.val) + 2) 0 = dg 5 (w.2.1 j).val 2 ∧
    maxDigit 0 (3 * (9 + j.val)) = 4 ∧ maxDigit 0 (3 * (9 + j.val) + 1) = 4 ∧ maxDigit 0 (3 * (9 + j.val) + 2) = 4 :=
  ⟨by simpa using getD5 w chk j 0 (by decide), getD5 w chk j 1 (by decide), getD5 w chk j 2 (by decide),
    by simpa using max5 j 0 (by decide), max5 j 1 (by decide), max5 j 2 (by decide)⟩

def credits (w : Word) : Nat :=
  (∑ g : Fin 9, tcredit 6 (w.1 g).val) + (∑ j : Fin 7, tcredit 5 (w.2.1 j).val) + pcredit w.2.2.val
def copies (w : Word) : Nat :=
  (∑ g : Fin 9, tcopies 6 (decide (g.val = 0)) (w.1 g).val) + (∑ j : Fin 7, tcopies 5 false (w.2.1 j).val) +
    pcopies w.2.2.val
def penalty (w : Word) : Nat := ∑ j : Fin 7, ind (pen j = true ∧ tsum 5 (w.2.1 j).val < 3)


theorem topCredit_encode (w : Word) :
    topCredit (encode w) = tcreditAll w + ind (152 - weight w + 1 = 5) := by
  unfold topCredit
  rw [sum_encode, show target 0 = 152 from rfl, list_sum_range_map]
  change (∑ i ∈ range 51, ind ((dataDigits 0 (encode w) ++ [152 - weight w]).getD i 0 + 1 = maxDigit 0 i)) = _
  rw [sum_51, getD48, getD49, getD50, show maxDigit 0 48 = 6 from rfl, show maxDigit 0 49 = 6 from rfl,
    show maxDigit 0 50 = 5 from rfl]
  unfold tcreditAll pcredit
  congr 2
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w (152 - weight w) g
    rw [a0, a1, a2, m0, m1, m2]; rfl
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w (152 - weight w) j
    rw [a0, a1, a2, m0, m1, m2]; rfl

theorem searchDecode_top_encode (w : Word) :
    (searchDecode 0 (encode w)).isSome = true ↔ legacyOk w := by
  unfold searchDecode encCredit
  rw [if_pos rfl, topCredit_encode, decode_top_encode, show creditFloor 0 = 7 from rfl]
  unfold legacyOk
  have e : ind (152 - weight w + 1 = 5) = ind (weight w = 148) := by
    unfold ind; by_cases h : weight w = 148
    · rw [if_pos (by omega), if_pos h]
    · by_cases h' : weight w ≤ 152
      · rw [if_neg (by omega), if_neg h]
      · rw [if_neg (by omega), if_neg h]
  rw [e]
  by_cases h1 : tcreditAll w + ind (weight w = 148) < 7
  · rw [if_pos h1]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega
  · rw [if_neg h1]
    split_ifs with h2 <;> simp <;> omega

end SigGolfResearch.T51Top
end

section
namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
/-- Campaign T51: the exact legacy search-decoder count (`topCredit ≥ 7`, the checksum chain included). -/
theorem searchDecode_top_count :
    Fintype.card {v : Digest // (searchDecode 0 v).isSome=true}=SigGolfResearch.T51Top.legacyCount := by
  classical
  rw [Fintype.card_subtype, SigGolfResearch.T51Top.card_encode _ (fun v h =>
      SigGolfResearch.T51Top.decode_top_valid (by
        obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp h
        rw [searchDecode_some hds]; rfl)),
    ← SigGolfResearch.T51Top.legacyCount_digits, ← SigGolfResearch.T51Top.legacy_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  exact SigGolfResearch.T51Top.searchDecode_top_encode w
end SigGolfCandidate.T3.Nonbinary
end
