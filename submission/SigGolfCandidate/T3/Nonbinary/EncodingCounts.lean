import SigGolfCandidate.T3.Gate6.DigestCounting

noncomputable section
namespace SigGolfCandidate.T3.EncodingCounting
open scoped BigOperators
open Polynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option backward.isDefEq.respectTransparency false
def fields (lay : Layer) : List Nat :=
  if lay=0 then List.replicate 49 2 ++ List.replicate 9 3 else List.replicate 42 3
def usedBits (widths : List Nat) : Nat := widths.sum
def decodeFields : List Nat → Nat → List Nat
  | [], _ => []
  | w::ws, n => n%2^w :: decodeFields ws (n/2^w)
theorem decodeFields_append (as bs : List Nat) (n : Nat) :
    decodeFields (as++bs) n = decodeFields as n ++ decodeFields bs (n/2^as.sum) := by
  induction as generalizing n with
  | nil => simp [decodeFields]
  | cons w ws ih =>
    simp only [List.cons_append,decodeFields,ih,List.sum_cons,Nat.pow_add,Nat.div_div_eq_div_mul]
theorem decodeFields_replicate (k w n : Nat) :
    decodeFields (List.replicate k w) n = (List.range k).map (fun i => n/2^(w*i)%2^w) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,decodeFields,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro i _
      simp [Nat.div_div_eq_div_mul,Nat.mul_succ,Nat.pow_add,Nat.mul_comm]
theorem decodeFields_fields (lay : Layer) (value : Digest) (hl : lay≠0) :
    decodeFields (fields lay) (lowerWord value) = dataDigits lay value := by
  simp only [fields,hl,ite_false,decodeFields_replicate,dataDigits_lowerWord hl]
  rfl
def wordSum (widths : List Nat) (n : Nat) : Nat := (decodeFields widths n).sum
def wordPoly (widths : List Nat) : Polynomial Nat :=
  ∑ n : Fin (2^usedBits widths), X^(wordSum widths n.val)
def fieldPoly (w : Nat) : Polynomial Nat := ∑ n : Fin (2^w), X^n.val
theorem wordPoly_cons (w : Nat) (ws : List Nat) :
    wordPoly (w::ws) = fieldPoly w * wordPoly ws := by
  classical
  let e : Fin (2^usedBits ws) × Fin (2^w) ≃ Fin (2^usedBits (w::ws)) :=
    finProdFinEquiv.trans (finCongr (by simp [usedBits,pow_add,Nat.mul_comm]))
  have he : ∀ p : Fin (2^usedBits ws) × Fin (2^w),
      (e p).val = p.2.val + 2^w*p.1.val := by intro p; rfl
  rw [wordPoly,← e.sum_comp]
  simp only [Fintype.sum_prod_type,he,wordSum,decodeFields,List.sum_cons]
  have hm (n : Fin (2^w)) (m : Nat) : (n.val+2^w*m)%2^w=n.val := by
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt n.isLt]
  have hd (n : Fin (2^w)) (m : Nat) : (n.val+2^w*m)/2^w=m := by
    rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt n.isLt,Nat.zero_add]
  simp_rw [hm,hd,pow_add]
  simp only [fieldPoly,wordPoly,wordSum,Finset.sum_mul,Finset.mul_sum]
@[simp] theorem wordPoly_nil : wordPoly [] = 1 := by
  norm_num [wordPoly,usedBits,wordSum,decodeFields]
def fieldsPoly : List Nat → Polynomial Nat
  | [] => 1
  | w::ws => fieldPoly w * fieldsPoly ws
theorem wordPoly_eq_fieldsPoly (ws : List Nat) : wordPoly ws=fieldsPoly ws := by
  induction ws with
  | nil => simp [fieldsPoly]
  | cons w ws ih => simp [fieldsPoly,wordPoly_cons,ih]
theorem fieldsPoly_append (a b : List Nat) : fieldsPoly (a++b)=fieldsPoly a*fieldsPoly b := by
  induction a with
  | nil => simp [fieldsPoly]
  | cons w ws ih => simp [fieldsPoly,ih,mul_assoc]
theorem fieldsPoly_replicate (w n : Nat) : fieldsPoly (List.replicate n w)=fieldPoly w^n := by
  induction n with
  | zero => simp [fieldsPoly]
  | succ n ih => simp [List.replicate_succ,fieldsPoly,ih,pow_succ,mul_comm]
attribute [local irreducible] wordPoly fieldPoly fieldsPoly
def rawAcceptedCount (lay : Layer) : Nat :=
  ![114690553285359954664897085539254262,
    115663871454869880991236461657470944,
    115663871454869880991236461657470944,
    115663871454869880991236461657470944] lay
def AcceptSum (lay : Layer) (total : Nat) : Prop :=
  if lay=0 then total=129 else if lay=3 then 191≤total ∧ total<199 else 191≤total ∧ total<199
instance (lay : Layer) (total : Nat) : Decidable (AcceptSum lay total) :=
  inferInstanceAs (Decidable (if lay=0 then total=129 else if lay=3 then 191≤total ∧ total<199 else 191≤total ∧ total<199))
def wordBits (lay : Layer) : Nat := if lay=0 then 125 else 126
theorem usedBits_fields (lay : Layer) : usedBits (fields lay)=wordBits lay := by
  fin_cases lay <;> decide
def packWord (lay : Layer) (n : Fin (2^usedBits (fields lay))) : Digest :=
  lowerPack n.val
theorem word_lt126 (lay : Layer) (hl : lay≠0) (n : Fin (2^usedBits (fields lay))) : n.val<2^126 :=
  calc n.val<2^usedBits (fields lay) := n.isLt
    _ = 2^126 := by rw [usedBits_fields,wordBits,if_neg hl]
@[simp] theorem packWord_word (lay : Layer) (hl : lay≠0) (n : Fin (2^usedBits (fields lay))) :
    lowerWord (packWord lay n)=n.val :=
  lowerWord_lowerPack (word_lt126 lay hl n)
def q4 (y : Nat) : Nat := 1+y+y^2+y^3
def q8 (y : Nat) : Nat := 1+y+y^2+y^3+y^4+y^5+y^6+y^7
def radix : Nat := 2^136
def topPacked : Nat := q4 radix^49*q8 radix^9
def lowerPacked : Nat := q8 radix^42
theorem eval_wordPoly (ws : List Nat) (y : Nat) :
    (wordPoly ws).eval y = ∑ n : Fin (2^usedBits ws), y^wordSum ws n.val := by
  simp [wordPoly,eval_finsetSum]
theorem eval_field2 (y : Nat) : (fieldPoly 2).eval y=q4 y := by
  unfold fieldPoly
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [q4,Finset.sum_range_succ]
theorem eval_field3 (y : Nat) : (fieldPoly 3).eval y=q8 y := by
  unfold fieldPoly
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [q8,Finset.sum_range_succ]
theorem top_weighted :
    (∑ n : Fin (2^usedBits (fields 0)), radix^wordSum (fields 0) n.val)=topPacked := by
  rw [←eval_wordPoly,wordPoly_eq_fieldsPoly]
  change (fieldsPoly (List.replicate 49 2++List.replicate 9 3)).eval radix=topPacked
  rw [fieldsPoly_append,fieldsPoly_replicate,fieldsPoly_replicate]
  simp only [eval_mul,eval_pow,eval_field2,eval_field3,topPacked]
theorem lower_weighted (lay : Layer) (hl : lay≠0) :
    (∑ n : Fin (2^usedBits (fields lay)), radix^wordSum (fields lay) n.val)=lowerPacked := by
  rw [←eval_wordPoly,wordPoly_eq_fieldsPoly]
  simp only [fields,if_neg hl,fieldsPoly_replicate,eval_pow,eval_field3,lowerPacked]
theorem word_card_small (lay : Layer) :
    Fintype.card (Fin (2^usedBits (fields lay)))<radix-1 := by
  rw [Fintype.card_fin,usedBits_fields]
  fin_cases lay <;> norm_num [wordBits,radix]
theorem interval_card {α : Type} [Fintype α] [DecidableEq α] (f : α → Nat)
    (lo hi : Nat) (h : lo≤hi) :
    (Finset.univ.filter (fun a => lo≤f a ∧ f a<hi)).card =
      (Finset.univ.filter (fun a => f a<hi)).card -
        (Finset.univ.filter (fun a => f a<lo)).card := by
  have he : (Finset.univ.filter (fun a => lo≤f a ∧ f a<hi)) =
      (Finset.univ.filter (fun a => f a<hi)) \ (Finset.univ.filter (fun a => f a<lo)) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [he,Finset.card_sdiff_of_subset]
  intro a ha
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  omega
theorem truncated_count (lay : Layer) (cut : Nat) (hc : 0<cut) :
    (Finset.univ.filter fun n : Fin (2^usedBits (fields lay)) =>
      wordSum (fields lay) n.val<cut).card =
      ((∑ n : Fin (2^usedBits (fields lay)),radix^wordSum (fields lay) n.val)%radix^cut)%(radix-1) := by
  symm
  exact DigestCounting.packed_card (by norm_num [radix]) hc _ _
    (by simpa only [Finset.card_univ] using word_card_small lay)
def intervalCount (packed lo hi : Nat) : Nat :=
  (packed%radix^hi)%(radix-1) - (packed%radix^lo)%(radix-1)
theorem top_exact : intervalCount topPacked 129 130=rawAcceptedCount 0 := by decide +kernel
theorem lower_first_exact : intervalCount lowerPacked 191 199=rawAcceptedCount 1 := by decide +kernel
theorem lower_last_exact : intervalCount lowerPacked 191 199=rawAcceptedCount 3 := by decide +kernel
theorem interval_words_count (lay : Layer) (lo hi : Nat) (hl : 0<lo) (hh : lo≤hi) :
    Fintype.card {n : Fin (2^usedBits (fields lay)) //
      lo≤wordSum (fields lay) n.val ∧ wordSum (fields lay) n.val<hi} =
      intervalCount (∑ n : Fin (2^usedBits (fields lay)),radix^wordSum (fields lay) n.val) lo hi := by
  classical
  rw [Fintype.card_subtype,interval_card _ lo hi hh,
    truncated_count lay hi (lt_of_lt_of_le hl hh),truncated_count lay lo hl]
  rfl
attribute [local irreducible] wordSum fields usedBits
theorem accepted_words_count (lay : Layer) :
    Fintype.card {n : Fin (2^usedBits (fields lay)) //
      AcceptSum lay (wordSum (fields lay) n.val)} = rawAcceptedCount lay := by
  classical
  fin_cases lay
  · have h := interval_words_count 0 129 130 (by decide) (by decide)
    rw [top_weighted,top_exact] at h
    have he (s : Nat) : (129 ≤ s ∧ s < 130) ↔ s = 129 := by omega
    simpa [he,AcceptSum] using h
  · have h := interval_words_count 1 191 199 (by decide) (by decide)
    rw [lower_weighted 1 (by decide),lower_first_exact] at h
    simpa [AcceptSum] using h
  · have h := interval_words_count 2 191 199 (by decide) (by decide)
    rw [lower_weighted 2 (by decide),lower_first_exact] at h
    simpa [AcceptSum,rawAcceptedCount] using h
  · have h := interval_words_count 3 191 199 (by decide) (by decide)
    rw [lower_weighted 3 (by decide),lower_last_exact] at h
    simpa [AcceptSum] using h
theorem decode_isSome_iff (lay : Layer) (value : Digest) (hl : lay≠0) :
    (decode lay value).isSome ↔ lowerSpare value ∧
      AcceptSum lay (wordSum (fields lay) (lowerWord value)) := by
  rw [wordSum,decodeFields_fields lay value hl]
  have hb : ¬ value.toNat ≥ 2^encodedBits lay := by
    simp only [encodedBits,hl,if_false]; have := value.isLt; omega
  have hs : (decode lay value).isSome ↔ lowerSpare value ∧
      (dataDigits lay value).sum ≤ target lay ∧ target lay - (dataDigits lay value).sum < 8 := by
    unfold decode
    rw [if_neg hb]
    simp only [hl,if_false]
    split_ifs with h <;> simp [h]
  rw [hs]
  apply and_congr_right
  intro _
  generalize (dataDigits lay value).sum = t
  fin_cases lay
  · exact absurd rfl hl
  all_goals simp only [AcceptSum,target] <;> constructor <;> intro h <;> simp_all <;> omega
theorem packWord_acceptance (lay : Layer) (n : Fin (2^usedBits (fields lay))) (hl : lay≠0) :
    (decode lay (packWord lay n)).isSome ↔ AcceptSum lay (wordSum (fields lay) n.val) := by
  rw [decode_isSome_iff lay _ hl,packWord_word lay hl]
  simp only [packWord,lowerSpare_lowerPack,true_and]
def acceptedDigestEquiv (lay : Layer) (hl : lay≠0) :
    {value : Digest // (decode lay value).isSome} ≃
      {n : Fin (2^usedBits (fields lay)) // AcceptSum lay (wordSum (fields lay) n.val)} where
  toFun value :=
    ⟨⟨lowerWord value.val,by rw [usedBits_fields,wordBits,if_neg hl];exact lowerWord_lt value.val⟩,
      ((decode_isSome_iff lay value.val hl).mp value.property).2⟩
  invFun n := ⟨packWord lay n.val,(packWord_acceptance lay n.val hl).mpr n.property⟩
  left_inv value := by
    apply Subtype.ext
    exact lowerPack_lowerWord ((decode_isSome_iff lay value.val hl).mp value.property).1
  right_inv n := by
    apply Subtype.ext
    apply Fin.ext
    exact packWord_word lay hl _
def acceptedCount (lay : Layer) : Nat :=
  ![99688341888453976199567696916972594,
    115663871454869880991236461657470944,
    115663871454869880991236461657470944,
    115663871454869880991236461657470944] lay
theorem decoder_acceptance_count (lay : Layer) :
    Fintype.card {value : Digest // (searchDecode lay value).isSome} = acceptedCount lay := by
  classical
  by_cases hl : lay=0
  · subst lay
    simpa [acceptedCount,SigGolfResearch.NonbinaryTop.CreditCounting.count] using
      Nonbinary.searchDecode_top_count
  · simp_rw [Nonbinary.searchDecode_lower hl]
    rw [Fintype.card_congr (acceptedDigestEquiv lay hl),accepted_words_count]
    fin_cases lay <;> simp_all [acceptedCount,rawAcceptedCount]
open OracleComp OracleSpec ENNReal
theorem decoder_uniform_probability (lay : Layer) :
    Pr[fun value => (searchDecode lay value).isSome | ($ᵗ Digest : ProbComp Digest)] =
      (acceptedCount lay : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,← Fintype.card_subtype,decoder_acceptance_count]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
theorem encoding_uniform_probability (lay : Layer) :
    Pr[fun answer => (Sampling.encodingDecode lay answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedCount lay : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample]
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128)
    (by decide) (fun value => (searchDecode lay value).isSome)
  change (Finset.univ.filter fun answer : HashOutput =>
    (searchDecode lay (answer.extractLsb' 0 128)).isSome).card = _ at hc
  rw [show (Finset.univ.filter fun answer : HashOutput =>
      (Sampling.encodingDecode lay answer).isSome).card =
      (Finset.univ.filter fun value : Digest => (searchDecode lay value).isSome).card*2^128 from hc]
  rw [← Fintype.card_subtype,decoder_acceptance_count]
  simp only [Fintype.card_bitVec,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = 2^128*2^128 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
#print axioms decoder_acceptance_count
#print axioms encoding_uniform_probability
end SigGolfCandidate.T3.EncodingCounting
end
