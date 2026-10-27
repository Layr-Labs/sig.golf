import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge023
import SigGolfCandidate.Merge024
import SigGolfCandidate.Merge025

-- ==== merged from T3_Gate6_DigestCounting ====
section

namespace SigGolfCandidate.T3.DigestCounting
open SigGolfResearch.Gate6 OracleComp ENNReal Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def p0 : Rat := SigGolfResearch.Gate6.Budget.p0
theorem packed_card {α : Type} [DecidableEq α] {y n : Nat} (hy : 3≤y) (hn : 0<n)
    (P : Finset α) (g : α → Nat) (hP : P.card<y-1) :
    ((∑ a ∈ P,y^g a)%y^n)%(y-1)=(P.filter (g · < n)).card := by
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hn P g (by omega),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic hy,
    Nat.mod_eq_of_lt ((card_filter_le _ _).trans_lt hP)]
theorem acceptanceProbability_eq_p0 :
    DigestSampling.acceptanceProbability=ENNReal.ofReal (p0 : Real) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold DigestSampling.acceptanceProbability acceptance;finiteness)
    (by finiteness)).mp
  norm_num [DigestSampling.acceptanceProbability,acceptance,p0,
    SigGolfResearch.Gate6.Budget.p0,ENNReal.toReal_div]
theorem digest_probability_eq_p0 :
    Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (p0 : Real) := by
  have he (answer : HashOutput) : (Sampling.digestDecode answer).isSome=digestAdmissible answer := by
    cases ha : digestAdmissible answer <;> simp only [Sampling.digestDecode,ha,
      Bool.false_eq_true,if_false,if_true,Option.isSome_none,Option.isSome_some]
  simp_rw [he]
  rw [SigGolfResearch.Gate6.Source.actual_acceptance_exact]
  exact acceptanceProbability_eq_p0
end SigGolfCandidate.T3.DigestCounting
namespace SigGolfCandidate.T3.Acceptance
open ENNReal DigestSampling
theorem acceptanceProbability_le_one_sixteenth : acceptanceProbability≤(1/16 : ENNReal) := by
  apply (ENNReal.toReal_le_toReal
    (by unfold acceptanceProbability SigGolfResearch.Gate6.acceptance;finiteness)
    (by finiteness)).mp
  norm_num [acceptanceProbability,SigGolfResearch.Gate6.acceptance,ENNReal.toReal_div]
end SigGolfCandidate.T3.Acceptance
end
-- ==== merged from T3_Nonbinary_EncodingCounts ====
section

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
/-- Raw data-word counts. Lower layers (targets 201/202/202): the sums of the 42 data digits in
`[194, 202)` for layer 1 and `[195, 203)` for layers 2 and 3. The top entry is a fixed combinatorial fact about `fields 0`
(the top decoder is counted in `Nonbinary.CreditFilter`). -/
def rawAcceptedCount (lay : Layer) : Nat :=
  ![114690553285359954664897085539254262,
    58782472808233403853217196834292020,
    46428947739236900406585478288441112,
    46428947739236900406585478288441112] lay
def AcceptSum (lay : Layer) (total : Nat) : Prop :=
  if lay=0 then total=129 else target lay - 7 ≤ total ∧ total < target lay + 1
instance (lay : Layer) (total : Nat) : Decidable (AcceptSum lay total) :=
  inferInstanceAs (Decidable (if lay=0 then total=129 else target lay - 7 ≤ total ∧ total < target lay + 1))
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
theorem lower_201_exact : intervalCount lowerPacked 194 202=rawAcceptedCount 1 := by decide +kernel
theorem lower_last_exact : intervalCount lowerPacked 195 203=rawAcceptedCount 3 := by decide +kernel
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
  · have h := interval_words_count 1 194 202 (by decide) (by decide)
    rw [lower_weighted 1 (by decide),lower_201_exact] at h
    simpa [AcceptSum,rawAcceptedCount,target] using h
  · have h := interval_words_count 2 195 203 (by decide) (by decide)
    rw [lower_weighted 2 (by decide),lower_last_exact] at h
    simpa [AcceptSum,rawAcceptedCount,target] using h
  · have h := interval_words_count 3 195 203 (by decide) (by decide)
    rw [lower_weighted 3 (by decide),lower_last_exact] at h
    simpa [AcceptSum,target] using h
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
  ![58354217001057952582130682281963303,
    58782472808233403853217196834292020,
    46428947739236900406585478288441112,
    46428947739236900406585478288441112] lay
theorem decoder_acceptance_count (lay : Layer) :
    Fintype.card {value : Digest // (searchDecode lay value).isSome} = acceptedCount lay := by
  classical
  by_cases hl : lay=0
  · subst lay
    simpa [acceptedCount,SigGolfResearch.T51Top.legacyCount] using
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
end SigGolfCandidate.T3.EncodingCounting
end
end
-- ==== merged from T3_PackedChain ====
section

namespace SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem chainExtra_bound (lay : Layer) (tree leaf : Nat) :
    tree % 2^31 / 2^(32-height lay) +
      (leaf % 4096 / 2^height lay) * 2^(height lay-1) < 2048 := by
  fin_cases lay <;> norm_num [height] <;> omega
theorem chainHeaderLow_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeaderLow lay tree leaf i step).toNat =
      128 + i % 64 + step % 8 * 2^8 +
      (tree % 2^31 * 2^height lay + leaf % 4096) % 2^32 * 2^16 +
      lay.val * 2^48 + 193 * 2^56 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) % 2 * 2^6 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) / 2 % 32 * 2^11 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) / 64 * 2^50 := by
  have hb := chainExtra_bound lay tree leaf
  have hl := lay.isLt
  unfold chainHeaderLow
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega
theorem chainHeaderSpill_bound (tree leaf i step : Nat) :
    chainHeaderSpill tree leaf i step < 2^52 := by
  unfold chainHeaderSpill
  omega
theorem chainHeaderLow_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2^56 ≤ (chainHeaderLow lay tree leaf i step).toNat ∧
      (chainHeaderLow lay tree leaf i step).toNat < 193 * 2^56 + 2^55 := by
  rw [chainHeaderLow_toNat]
  have hb := chainExtra_bound lay tree leaf
  have hl := lay.isLt
  omega
theorem chainHeaderFlaggedLow_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeaderFlaggedLow lay tree leaf i step).toNat =
      (chainHeaderLow lay tree leaf i step).toNat +
        (if chainHeaderSpill tree leaf i step = 0 then 0 else 1) * 2^55 := by
  have hb := chainHeaderLow_band lay tree leaf i step
  unfold chainHeaderFlaggedLow
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  split_ifs <;> omega
private theorem flaggedLow_base_eq (a b : BitVec 64) (f g : Nat)
    (ha : 193 * 2^56 ≤ a.toNat ∧ a.toNat < 193 * 2^56 + 2^55)
    (hb : 193 * 2^56 ≤ b.toNat ∧ b.toNat < 193 * 2^56 + 2^55)
    (hf : f ≤ 1) (hg : g ≤ 1)
    (he : a.toNat + f * 2^55 = b.toNat + g * 2^55) : a = b := by
  apply BitVec.eq_of_toNat_eq
  omega
theorem chainHeaderFlaggedLow_base {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeaderFlaggedLow lay tree leaf i step = chainHeaderFlaggedLow lay' tree' leaf' i' step') :
    chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' := by
  have he := congrArg BitVec.toNat h
  rw [chainHeaderFlaggedLow_toNat, chainHeaderFlaggedLow_toNat] at he
  exact flaggedLow_base_eq _ _ _ _ (chainHeaderLow_band lay tree leaf i step)
    (chainHeaderLow_band lay' tree' leaf' i' step')
    (by split_ifs <;> omega) (by split_ifs <;> omega) he
theorem chainHeader_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).toNat =
      chainHeaderSpill tree leaf i step * 2^64 + (chainHeaderFlaggedLow lay tree leaf i step).toNat := by
  have hb := chainHeaderSpill_bound tree leaf i step
  unfold chainHeader
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (chainHeaderFlaggedLow lay tree leaf i step).isLt,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show chainHeaderSpill tree leaf i step < 2^64 by omega)]
theorem chainHeader_low (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 = chainHeaderFlaggedLow lay tree leaf i step := by
  exact BitVec.extractLsb'_append_eq_right
theorem chainHeaderSpill_zero (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    chainHeaderSpill tree leaf i step = 0 := by
  unfold chainHeaderSpill
  omega
theorem chainHeader_offgraph_bit (lay : Layer) (tree leaf i step : Nat) :
    ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat / 2^55 % 2 =
      if chainHeaderSpill tree leaf i step = 0 then 0 else 1 := by
  rw [chainHeader_low, chainHeaderFlaggedLow_toNat]
  have hb := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega
theorem chainHeader_graph_bit (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat / 2^55 % 2 = 0 := by
  rw [chainHeader_offgraph_bit, chainHeaderSpill_zero tree leaf i step ht hl hi hs, if_pos rfl]
theorem chainHeader_offgraph_low_ne {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hoff : chainHeaderSpill tree leaf i step ≠ 0)
    (ht : tree' < 2^31) (hl : leaf' < 4096) (hi : i' < 64) (hs : step' < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 ≠
      (chainHeader lay' tree' leaf' i' step').extractLsb' 0 64 := by
  intro he
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [he, chainHeader_graph_bit lay' tree' leaf' i' step' ht hl hi hs, if_neg hoff] at hbit
  contradiction
theorem chainHeaderLow_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step') :
    lay = lay' ∧ tree % 2^31 = tree' % 2^31 ∧ leaf % 4096 = leaf' % 4096 ∧
      i % 64 = i' % 64 ∧ step % 8 = step' % 8 := by
  have he := congrArg BitVec.toNat h
  rw [chainHeaderLow_toNat, chainHeaderLow_toNat] at he
  have hl := lay.isLt
  have hl' := lay'.isLt
  have hb := chainExtra_bound lay tree leaf
  have hb' := chainExtra_bound lay' tree' leaf'
  generalize hx : (tree % 2^31 / 2^(32-height lay) +
    (leaf % 4096 / 2^height lay) * 2^(height lay-1)) = extra at he hb
  generalize hx' : (tree' % 2^31 / 2^(32-height lay') +
    (leaf' % 4096 / 2^height lay') * 2^(height lay'-1)) = extra' at he hb'
  have hparts : lay.val = lay'.val ∧ i % 64 = i' % 64 ∧ step % 8 = step' % 8 ∧
      (tree % 2^31 * 2^height lay + leaf % 4096) % 2^32 =
        (tree' % 2^31 * 2^height lay' + leaf' % 4096) % 2^32 ∧ extra = extra' := by omega
  have heq := Fin.ext hparts.1
  subst lay'
  have hmeta := hx.trans (hparts.2.2.2.2.trans hx'.symm)
  have hquot : tree % 2^31 / 2^(32-height lay) = tree' % 2^31 / 2^(32-height lay) ∧
      leaf % 4096 / 2^height lay = leaf' % 4096 / 2^height lay := by
    fin_cases lay <;> norm_num [height] at hmeta ⊢ <;> omega
  have hrem : leaf % 4096 % 2^height lay = leaf' % 4096 % 2^height lay := by
    have hm := congrArg (fun n => n % 2^height lay) hparts.2.2.2.1
    fin_cases lay <;> norm_num [height, Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd] at hm ⊢ <;> omega
  refine ⟨rfl, ?_⟩
  clear he hx hx'
  fin_cases lay <;> norm_num [height] at hparts hquot hrem ⊢ <;> omega
theorem chainHeaderLow_congr {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^31 = tree' % 2^31)
    (hf : leaf % 4096 = leaf' % 4096) (hi : i % 64 = i' % 64)
    (hs : step % 8 = step' % 8) :
    chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' := by
  simp only [chainHeaderLow, hl, ht, hf, hi, hs]
theorem chainHeader_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step') :
    lay = lay' ∧ tree % 2^40 = tree' % 2^40 ∧ leaf % 2^32 = leaf' % 2^32 ∧
      i % 2^24 = i' % 2^24 ∧ step % 256 = step' % 256 := by
  have hlo := congrArg (fun b : BitVec 128 => b.extractLsb' 0 64) h
  simp only [chainHeader_low] at hlo
  obtain ⟨hlay, ht, hf, hi, hs⟩ := chainHeaderLow_fields (chainHeaderFlaggedLow_base hlo)
  have he := congrArg BitVec.toNat h
  rw [chainHeader_toNat, chainHeader_toNat, hlo] at he
  have hh : chainHeaderSpill tree leaf i step = chainHeaderSpill tree' leaf' i' step' := by omega
  unfold chainHeaderSpill at hh
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩
theorem chainHeader_congr {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^40 = tree' % 2^40)
    (hf : leaf % 2^32 = leaf' % 2^32) (hi : i % 2^24 = i' % 2^24)
    (hs : step % 256 = step' % 256) :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' := by
  have hlo : chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' :=
    chainHeaderLow_congr hl (by omega) (by omega) (by omega) (by omega)
  simp only [chainHeader, chainHeaderFlaggedLow, chainHeaderSpill, ht, hf, hi, hs, hlo]
theorem packedRoute_injective {lay : Layer} {tree leaf tree' leaf' : Nat}
    (hl : leaf < 2^height lay) (hl' : leaf' < 2^height lay)
    (h : tree * 2^height lay + leaf = tree' * 2^height lay + leaf') :
    tree = tree' ∧ leaf = leaf' := by
  have he : leaf + 2^height lay * tree = leaf' + 2^height lay * tree' := by
    simpa only [Nat.mul_comm, Nat.add_comm] using h
  obtain ⟨hleaf, htree⟩ := pack_nat_injective hl hl' he
  exact ⟨htree, hleaf⟩
theorem packedRoute_bound {lay : Layer} {tree leaf : Nat}
    (ht : tree < 2^31) (hl : leaf < 2^height lay) :
    tree * 2^height lay + leaf < 2^43 := by
  fin_cases lay <;> norm_num [height] at hl ⊢ <;> omega
theorem chainHeader_low_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8)
    (ht' : tree' < 2^31) (hl' : leaf' < 4096) (hi' : i' < 64) (hs' : step' < 8)
    (h : (chainHeader lay tree leaf i step).extractLsb' 0 64 =
      (chainHeader lay' tree' leaf' i' step').extractLsb' 0 64) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' := by
  simp only [chainHeader_low] at h
  obtain ⟨hlay, htree, hleaf, hindex, hstep⟩ := chainHeaderLow_fields (chainHeaderFlaggedLow_base h)
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩
theorem chainHeader_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (ht : tree < 2^40) (hl : leaf < 2^32) (hi : i < 2^24) (hs : step < 256)
    (ht' : tree' < 2^40) (hl' : leaf' < 2^32) (hi' : i' < 2^24) (hs' : step' < 256)
    (h : chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' := by
  obtain ⟨hlay, htree, hleaf, hindex, hstep⟩ := chainHeader_fields h
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩
theorem chainHeader_marker (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).toNat / 2^56 % 256 = 193 := by
  have hdiv : (chainHeaderLow lay tree leaf i step).toNat / 2^56 = 193 := by
    rw [chainHeaderLow_toNat]
    have := lay.isLt
    have hb := chainExtra_bound lay tree leaf
    generalize (tree % 2^31 / 2^(32-height lay) +
      (leaf % 4096 / 2^height lay) * 2^(height lay-1)) = extra at hb ⊢
    omega
  have hb := chainHeaderLow_band lay tree leaf i step
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat]
  split_ifs <;> omega
theorem header_marker_lt (tag lay tree position index : Nat)
    (ht : tree < 2^31) (hp : position < 2^31) :
    (header tag lay tree position index).toNat / 2^56 % 256 < 128 := by
  have hlow : (header tag lay tree position index).toNat % 2^64 < 2^63 := by
    have htt : tree < 2^32 := by omega
    have hpp : position < 2^32 := by omega
    have hh : tree / 2^32 = 0 := Nat.div_eq_of_lt htt
    let low := 1 + tag % 256 * 2^8 + lay % 256 * 2^16
    have heq : (header tag lay tree position index).toNat =
        if packedNodeTag tag then
          (low + tree * 2^32) + nodeWord tag position index * 2^64
        else (low + position * 2^32) + (tree + index % 2^32 * 2^32) * 2^64 := by
      rw [header_toNat]
      simp only [hh, Nat.zero_mod, Nat.zero_mul, Nat.add_zero,
        Nat.mod_eq_of_lt htt, Nat.mod_eq_of_lt hpp]
      split_ifs <;> dsimp [low] <;> ring
    rw [heq]
    split_ifs <;> rw [Nat.add_mul_mod_self_right]
    all_goals
      apply lt_of_le_of_lt (Nat.mod_le _ _)
      dsimp [low]
      omega
  have he : (header tag lay tree position index).toNat / 2^56 % 256 =
      ((header tag lay tree position index).toNat % 2^64) / 2^56 := by
    rw [show (2 : Nat)^64 = 2^56 * 256 by decide, Nat.mod_mul_right_div_self]
  rw [he]
  omega
theorem chainHeader_ne_header_bounded (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat)
    (ht : roleTree < 2^31) (hp : position < 2^31) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_marker lay tree leaf i step
  have hr := header_marker_lt tag roleLay roleTree position index ht hp
  rw [h] at hc
  omega
theorem chainHeader_firstByte (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (chainHeader lay tree leaf i step).toNat % 256 := by
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat, chainHeaderLow_toNat]
  split_ifs <;> omega
theorem header_firstByte (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat % 256 = 1 := by
  rw [header_toNat]
  split_ifs <;> omega
theorem bytesLE16_first_toNat (h : BitVec 128) :
    ((bytesLE 16 h).getD 0 0).toNat = h.toNat % 256 := by
  change (h.extractLsb' 0 8).toNat = _
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem chainHeader_ne_header (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_firstByte lay tree leaf i step
  rw [h, header_firstByte] at hc
  omega
theorem chainHeader_tweakMarker (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ tweakMarker (chainHeader lay tree leaf i step) := chainHeader_firstByte lay tree leaf i step
theorem chainHeader_ne_digestHeader (lay : Layer) (tree leaf i step : Nat) (counter : BitVec 32) :
    chainHeader lay tree leaf i step ≠ digestHeader counter := by
  intro h
  have hc := chainHeader_tweakMarker lay tree leaf i step
  rw [h, digestHeader_marker] at hc
  omega
theorem chainHeader_ne_leafTweak (lay : Layer) (tree leaf i step : Nat) (lay' : Layer) (tree' leaf' : Nat) :
    chainHeader lay tree leaf i step ≠ leafTweak lay' tree' leaf' := by
  intro h
  have hc := chainHeader_tweakMarker lay tree leaf i step
  rw [h, leafTweak_marker] at hc
  omega
theorem chainHeader_ne_rowTweak (lay : Layer) (tree leaf i step : Nat) (lay' : Layer) (tree' leaf' : Nat) :
    chainHeader lay tree leaf i step ≠ rowTweak lay' tree' leaf' := by
  intro h
  have hc := chainHeader_tweakMarker lay tree leaf i step
  rw [h, rowTweak_marker] at hc
  omega
theorem chainHeader_ne_nodeTweak (lay : Layer) (tree leaf i step : Nat) (tag lay' tree' heap : Nat) :
    chainHeader lay tree leaf i step ≠ nodeTweak tag lay' tree' heap := by
  intro h
  by_cases hf : tag = 3 ∧ 4 ≤ lay' ∧ lay' < 13 ∧ FtsNew heap
  · obtain ⟨rfl, h4, h13, hn⟩ := hf
    have hw := congrArg (fun x : BitVec 128 => (x.extractLsb' 0 64).toNat) h
    simp only [chainHeader_low, chainHeaderFlaggedLow_toNat, nodeTweak_ftsN h4 h13 _ hn, append64_low] at hw
    have hb := chainHeaderLow_band lay tree leaf i step
    have := ftsNodeWordH_lt (lay' - 4) tree' heap
    split_ifs at hw <;> omega
  · by_cases ht : tag = 3 ∧ lay' = 0
    · -- C4 (adapted from b3cc11b): the top label is the low word `topNodeWord heap < 4096`, a chain word is `≥ 193 * 2^56`.
      obtain ⟨rfl, rfl⟩ := ht
      have hw := congrArg (fun x : BitVec 128 => (x.extractLsb' 0 64).toNat) h
      simp only [chainHeader_low, chainHeaderFlaggedLow_toNat, nodeTweak_top, append64_low, topNodeWord_toNat64] at hw
      have hb := chainHeaderLow_band lay tree leaf i step
      have := topNodeWord_lt heap
      split_ifs at hw <;> omega
    · have hc := chainHeader_tweakMarker lay tree leaf i step
      rw [h, nodeTweak_marker, if_neg ht] at hc
      split_ifs at hc <;> first | omega | (exfalso; exact hf ‹_›)
theorem header_marker_lt_nonpacked (tag lay tree position index : Nat)
    (hn : packedNodeTag tag = false) (hp : position < 2^31) :
    (header tag lay tree position index).toNat / 2^56 % 256 < 128 := by
  have hpp : position < 2^32 := by omega
  let low := 1 + tag % 256 * 2^8 + lay % 256 * 2^16 + (tree / 2^32 % 256) * 2^24
  have heq : (header tag lay tree position index).toNat =
      (low + position * 2^32) + (tree % 2^32 + index % 2^32 * 2^32) * 2^64 := by
    rw [header_toNat]
    simp only [hn, Bool.false_eq_true, if_false, Nat.mod_eq_of_lt hpp]
    dsimp [low]
    ring
  have hb : (header tag lay tree position index).toNat % 2^64 < 2^63 := by
    rw [heq, Nat.add_mul_mod_self_right]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    dsimp [low]
    omega
  have he : (header tag lay tree position index).toNat / 2^56 % 256 =
      ((header tag lay tree position index).toNat % 2^64) / 2^56 := by
    rw [show (2 : Nat)^64 = 2^56 * 256 by decide, Nat.mod_mul_right_div_self]
  rw [he]
  omega
theorem chainHeader_ne_nonpacked (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat)
    (hn : packedNodeTag tag = false) (hp : position < 2^31) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_marker lay tree leaf i step
  have hr := header_marker_lt_nonpacked tag roleLay roleTree position index hn hp
  rw [h] at hc
  omega
theorem chainHeader_congr_old {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^40 = tree' % 2^40)
    (hf : leaf % 2^32 = leaf' % 2^32) (hi : i % 2^24 = i' % 2^24)
    (hs : step % 256 = step' % 256) :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' := by
  exact chainHeader_congr hl ht hf hi hs
theorem chainHeader_actual (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2^height lay + leaf < 2^31) (hf : leaf < 2^height lay)
    (hi : i < 64) (hs : step < 8) :
    chainHeader lay tree leaf i step = BitVec.ofNat 128
      (128 + i + step * 2^8 + (tree * 2^height lay + leaf) * 2^16 + lay.val * 2^48 + 193 * 2^56) := by
  apply BitVec.eq_of_toNat_eq
  have hz : chainHeaderSpill tree leaf i step = 0 := by
    unfold chainHeaderSpill
    fin_cases lay <;> norm_num [height] at hr hf ⊢ <;> omega
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat, hz, if_pos rfl,
    chainHeaderLow_toNat, BitVec.toNat_ofNat]
  fin_cases lay <;> norm_num [height] at hr hf ⊢ <;> omega
theorem chainHeader_high_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).toNat / 2^64 = 0 := by
  rw [chainHeader_toNat]
  have hb := (chainHeaderFlaggedLow lay tree leaf i step).isLt
  unfold chainHeaderSpill
  omega
theorem chainInput_padded (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (chainInput lay tree leaf i step value) = chainInput lay tree leaf i step value := by
  simp [pad64, chainInput, bytesLE_length, zero16]
theorem chainInput_header (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    ((chainInput lay tree leaf i step value).drop 16).take 16 =
      bytesLE 16 (chainHeader lay tree leaf i step) := by
  simp [chainInput, zero16, List.append_assoc, bytesLE_length]
theorem chainInput_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {value value' : Digest}
    (h : chainInput lay tree leaf i step value = chainInput lay' tree' leaf' i' step' value') :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' ∧ value = value' := by
  unfold chainInput at h
  obtain ⟨hp, hv⟩ := List.append_inj h (by simp [List.length_append, zero16, bytesLE_length])
  have hh : bytesLE 16 (chainHeader lay tree leaf i step) =
      bytesLE 16 (chainHeader lay' tree' leaf' i' step') := by simpa using hp
  exact ⟨bytesLE_injective hh, bytesLE_injective hv⟩
end SigGolfCandidate.T3
end
-- ==== merged from T3_Gate6_SourceBudget ====
section

namespace SigGolfCandidate.T3.BaseAudit
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def zU : ℚ := 1/(1-6931471808/(10000000000*131072))
def p0 : ℚ := (6963897326262647489342145 / 19807040628566084398385987584)
def b0 : ℚ := (507635451307 / 500000000000)
theorem step_0 : zU*((1-p0)*b0+p0) ≤ b0 := by norm_num [zU,p0,b0]
def p1 : ℚ := (45926795543361359114465905709789119 / 85070591730234615865843651857942052864)
def b1 : ℚ := (1009892452433 / 1000000000000)
theorem step_1 : zU*((1-p1)*b1+p1) ≤ b1 := by norm_num [zU,p1,b1]
def p2 : ℚ := (27179160510794301985010390415765999 / 42535295865117307932921825928971026432)
def b2 : ℚ := (1008345227909 / 1000000000000)
theorem step_2 : zU*((1-p2)*b2+p2) ≤ b2 := by norm_num [zU,p2,b2]
def p3 : ℚ := (27179160510794301985010390415765999 / 42535295865117307932921825928971026432)
def b3 : ℚ := (1008345227909 / 1000000000000)
theorem step_3 : zU*((1-p3)*b3+p3) ≤ b3 := by norm_num [zU,p3,b3]
def p4 : ℚ := (33210373316701753609053794695642145 / 42535295865117307932921825928971026432)
def b4 : ℚ := (503409673483 / 500000000000)
theorem step_4 : zU*((1-p4)*b4+p4) ≤ b4 := by norm_num [zU,p4,b4]
theorem signing_envelope :
    (2 : ℝ)^((121762 : ℝ)/131072) * ((507635451307 / 500000000000) * (1009892452433 / 1000000000000) * (1008345227909 / 1000000000000) * (1008345227909 / 1000000000000) * (503409673483 / 500000000000)) ≤ 2 := by
  have hsplit : (2 : ℝ)^((121762 : ℝ)/131072) = 2/(2 : ℝ)^((9310 : ℝ)/131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (9310/131072) (by norm_num)
  have hn : ((507635451307 / 500000000000) * (1009892452433 / 1000000000000) * (1008345227909 / 1000000000000) * (1008345227909 / 1000000000000) * (503409673483 / 500000000000) : ℝ) ≤
      1+0.6931471803*(9310/131072)+(0.6931471803*(9310/131072))^2/2 := by norm_num
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
theorem source_signing_envelope :
    (2 : ℝ)^((121761 : ℝ)/131072) * ((507635451307 / 500000000000) * (1009892452433 / 1000000000000) * (1008345227909 / 1000000000000) * (1008345227909 / 1000000000000) * (503409673483 / 500000000000)) ≤ 2 := by
  calc
    _ ≤ (2 : ℝ)^((121762 : ℝ)/131072) * ((507635451307 / 500000000000) * (1009892452433 / 1000000000000) * (1008345227909 / 1000000000000) * (1008345227909 / 1000000000000) * (503409673483 / 500000000000)) := by gcongr <;> norm_num
    _ ≤ 2 := signing_envelope
end SigGolfCandidate.T3.BaseAudit
end
-- ==== merged from T3_Gate6_NearCoverage ====
section

section
namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
noncomputable def gatedEventEquiv (event : CoordinateDraw → Prop) :
    {draw : GatedDraw // draw.2=0 ∧ event draw.1} ≃
      {draw : CoordinateDraw // event draw} where
  toFun d := ⟨d.1.1,d.2.2⟩
  invFun d := ⟨(d.1,0),rfl,d.2⟩
  left_inv d := by apply Subtype.ext;exact Prod.ext rfl d.2.1.symm
  right_inv _ := rfl
theorem gated_event_probability (event : CoordinateDraw → Prop) :
    Pr[fun draw : GatedDraw => draw.2=0 ∧ event draw.1 | ($ᵗ GatedDraw : ProbComp GatedDraw)] =
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (gatedEventEquiv event),
    probEvent_uniformSample,←Fintype.card_subtype]
  simp only [GatedDraw,Fintype.card_prod,Padding,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_ofNat]
  rw [div_div]
theorem digest_gated_event_probability (event : CoordinateDraw → Prop) :
    Pr[fun output => (digestRecord output).2.2.1=0 ∧
      event (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8 := by
  rw [digest_event (fun raw => raw.2.2.1=0 ∧ event (rawDraw raw).1)]
  change Pr[fun raw => (rawDraw raw).2=0 ∧ event (rawDraw raw).1 | _]=_
  rw [raw_draw_event (fun draw => draw.2=0 ∧ event draw.1),gated_event_probability]
noncomputable def rawAtEventEquiv (index : Address) (event : GatedDraw → Prop) :
    {raw : RawRecord // raw.1.1=index ∧ event (rawDraw raw)} ≃
      {draw : GatedDraw // event draw} × Unused where
  toFun r := (⟨rawDraw r.1,r.2.2⟩,r.1.2.2.2)
  invFun r := ⟨((index,fun c => (r.1.1.1 c).1),
    (fun c => (r.1.1.1 c).2,(r.1.1.2,r.2))),rfl,r.1.2⟩
  left_inv r := by apply Subtype.ext;exact Prod.ext (Prod.ext r.2.1.symm rfl) rfl
  right_inv _ := rfl
theorem raw_at_draw_event (index : Address) (event : GatedDraw → Prop) :
    Pr[fun raw => raw.1.1=index ∧ event (rawDraw raw) | ($ᵗ RawRecord : ProbComp RawRecord)] =
      (Pr[event | ($ᵗ GatedDraw : ProbComp GatedDraw)])/2^31 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (rawAtEventEquiv index event),
    Fintype.card_prod,rawRecord_card,
    probEvent_uniformSample,←Fintype.card_subtype,gatedDraw_card]
  simp only [Unused,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num
  ring
theorem digest_at_gated_event_probability (index : Address) (event : CoordinateDraw → Prop) :
    Pr[fun output => (digestRecord output).1.1=index ∧
      (digestRecord output).2.2.1=0 ∧ event (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      ((Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8)/2^31 := by
  rw [digest_event (fun raw => raw.1.1=index ∧ raw.2.2.1=0 ∧ event (rawDraw raw).1)]
  change Pr[fun raw => raw.1.1=index ∧ (rawDraw raw).2=0 ∧ event (rawDraw raw).1 | _]=_
  rw [raw_at_draw_event index (fun draw => draw.2=0 ∧ event draw.1),gated_event_probability]
end SigGolfResearch.Gate6
end
section
namespace SigGolfCandidate.T3.BPORS
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def OmitCovered (exposed : Finset (Fin 128)) (omitted : Fin 3)
    (draw : Fin 3 → Fin 128) : Prop := Covered exposed (omitted.removeNth draw)
theorem omitCovered_of_all_but (exposed : Finset (Fin 128)) (omitted : Fin 3)
    (draw : Fin 3 → Fin 128) (hinj : Function.Injective draw)
    (hcovered : ∀ slot, slot ≠ omitted → draw slot ∈ exposed) :
    OmitCovered exposed omitted draw := by
  refine ⟨hinj.comp Fin.succAbove_right_injective, ?_⟩
  intro slot
  exact hcovered (omitted.succAbove slot) (Fin.succAbove_ne omitted slot)
noncomputable def omitCoveredEquiv (exposed : Finset (Fin 128)) (omitted : Fin 3) :
    {draw : Fin 3 → Fin 128 // OmitCovered exposed omitted draw} ≃
      ({draw : Fin 2 → Fin 128 // Covered exposed draw} × Fin 128) where
  toFun draw := (⟨omitted.removeNth draw.1, draw.2⟩, draw.1 omitted)
  invFun draw := ⟨omitted.insertNth draw.2 draw.1.1, by
    simpa only [OmitCovered, Fin.removeNth_insertNth] using draw.1.2⟩
  left_inv draw := by
    apply Subtype.ext
    exact Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  right_inv draw := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      exact Fin.removeNth_insertNth (α := fun _ : Fin 3 => Fin 128) omitted draw.2 draw.1.1
    · dsimp only
      exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => Fin 128) omitted draw.2 draw.1.1
theorem omitCovered_count (exposed : Finset (Fin 128)) (omitted : Fin 3) :
    (Finset.univ.filter fun draw : Fin 3 → Fin 128 => OmitCovered exposed omitted draw).card =
      exposed.card.descFactorial 2 * 128 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (omitCoveredEquiv exposed omitted),
    Fintype.card_prod, Fintype.card_subtype, covered_count, Fintype.card_fin]
noncomputable def bucketOmitCoveredEquiv (exposed : Fin 16 → Finset (Fin 128))
    (omitted : Fin 3) :
    {draw : Fin 16 × (Fin 3 → Fin 128) // OmitCovered (exposed draw.1) omitted draw.2} ≃
      (bucket : Fin 16) × {draw : Fin 3 → Fin 128 // OmitCovered (exposed bucket) omitted draw} where
  toFun draw := ⟨draw.1.1, draw.1.2, draw.2⟩
  invFun draw := ⟨(draw.1, draw.2.1), draw.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem bucket_omitCovered_count (exposed : Fin 16 → Finset (Fin 128)) (omitted : Fin 3) :
    (Finset.univ.filter fun draw : Fin 16 × (Fin 3 → Fin 128) =>
      OmitCovered (exposed draw.1) omitted draw.2).card =
      (∑ bucket, (exposed bucket).card.descFactorial 2) * 128 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (bucketOmitCoveredEquiv exposed omitted),
    Fintype.card_sigma]
  simp only [Fintype.card_subtype, omitCovered_count, Finset.sum_mul]
theorem bucket_omitCovered_probability (exposed : Fin 16 → Finset (Fin 128)) (omitted : Fin 3) :
    Pr[fun draw : Fin 16 × (Fin 3 → Fin 128) => OmitCovered (exposed draw.1) omitted draw.2 |
      ($ᵗ (Fin 16 × (Fin 3 → Fin 128)) : ProbComp _)] =
      (∑ bucket, ((exposed bucket).card.descFactorial 2 : ENNReal)) / (16 * 128^2) := by
  rw [probEvent_uniformSample, bucket_omitCovered_count]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem uniform_forall_probability {α : Type} [Fintype α] [SampleableType α]
    (count : Nat) (event : Fin count → α → Prop) :
    Pr[fun draw : Fin count → α => ∀ coord, event coord (draw coord) |
      ($ᵗ (Fin count → α) : ProbComp _)] =
      ∏ coord, Pr[event coord | ($ᵗ α : ProbComp _)] := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := event)), Fintype.card_pi]
  simp only [probEvent_uniformSample, Fintype.card_subtype, Nat.cast_prod, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
def NearCovered (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) (draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : Prop :=
  ∀ coord, if coord = missing then OmitCovered (exposed coord (draw coord).1) omitted (draw coord).2
    else Covered (exposed coord (draw coord).1) (draw coord).2
theorem nearCovered_of_all_but (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) (draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128)))
    (hinj : ∀ coord, Function.Injective (draw coord).2)
    (hcovered : ∀ coord slot, (coord, slot) ≠ (missing, omitted) →
      (draw coord).2 slot ∈ exposed coord (draw coord).1) :
    NearCovered exposed missing omitted draw := by
  intro coord
  by_cases hcoord : coord = missing
  · rw [if_pos hcoord]
    apply omitCovered_of_all_but _ _ _ (hinj coord)
    intro slot hslot
    exact hcovered coord slot (fun he => hslot (Prod.mk.inj he).2)
  · rw [if_neg hcoord]
    exact ⟨hinj coord, fun slot => hcovered coord slot (fun he => hcoord (Prod.mk.inj he).1)⟩
theorem nearCovered_probability (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[NearCovered exposed missing omitted |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] =
      ∏ coord, if coord = missing then
        (∑ bucket, ((exposed coord bucket).card.descFactorial 2 : ENNReal)) / (16 * 128^2)
      else (∑ bucket, ((exposed coord bucket).card.descFactorial 3 : ENNReal)) / (16 * 128^3) := by
  unfold NearCovered
  rw [uniform_forall_probability 7 (fun coord (draw : Fin 16 × (Fin 3 → Fin 128)) =>
    if coord = missing then OmitCovered (exposed coord draw.1) omitted draw.2
    else Covered (exposed coord draw.1) draw.2)]
  apply Finset.prod_congr rfl
  intro coord _
  by_cases he : coord = missing
  · simp only [he, if_true]
    exact bucket_omitCovered_probability _ omitted
  · simp only [he, if_false]
    exact bucket_covered_probability _
theorem near_denominator_product (missing : Fin 7) :
    (∏ coord : Fin 7, if coord = missing then ((128 : ENNReal)^2)⁻¹
      else ((128 : ENNReal)^3)⁻¹) = ((2 : ENNReal)^140)⁻¹ := by
  have he : (∏ coord : Fin 7, if coord = missing then ((128 : ENNReal)^2)⁻¹
      else ((128 : ENNReal)^3)⁻¹) =
      ((128 : ENNReal)^2)⁻¹ * (((128 : ENNReal)^3)⁻¹)^6 := by
    rw [Finset.prod_ite]
    have hfilter : (Finset.univ.filter fun coord : Fin 7 => coord = missing) = {missing} := by
      ext coord
      simp
    rw [hfilter]
    simp [Finset.prod_const, Finset.filter_ne']
  rw [he]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem div_bucket_leaf_power (value : ENNReal) (power : Nat) :
    value / (16 * (128 : ENNReal)^power) = value / 16 / 128^power := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (16 : ENNReal) ≠ 0))
    (Or.inl (by finiteness : (16 : ENNReal) ≠ ⊤)), mul_assoc]
noncomputable def rawNearWordEnvelope (missing : Fin 7) (word : List History.Buckets) : ENNReal :=
  (∏ c, if c=missing then Numeric.nearCoordinateEnvelope (word.map fun row => row c)
    else coordinateEnvelope (word.map fun row => row c))/2^140
theorem nearCovered_le_rawWordEnvelope
    (word : List History.Buckets) (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (hcard : ∀ coord bucket, (exposed coord bucket).card ≤
      3 * (word.map (fun row => row coord)).count bucket)
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[NearCovered exposed missing omitted |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] ≤
      rawNearWordEnvelope missing word := by
  rw [nearCovered_probability]
  calc
    _ ≤ ∏ coord : Fin 7, if coord = missing then
        Numeric.nearCoordinateEnvelope (word.map (fun row => row coord)) / 128^2
      else coordinateEnvelope (word.map (fun row => row coord)) / 128^3 := by
      apply Finset.prod_le_prod'
      intro coord _
      by_cases he : coord = missing
      · simp only [he, if_true, Numeric.nearCoordinateEnvelope, div_bucket_leaf_power]
        apply ENNReal.div_le_div_right
        apply ENNReal.div_le_div_right
        apply Finset.sum_le_sum
        intro bucket _
        exact_mod_cast Nat.descFactorial_le 2 (hcard missing bucket)
      · simp only [he, if_false, coordinateEnvelope, bucketMass, div_bucket_leaf_power]
        apply ENNReal.div_le_div_right
        apply ENNReal.div_le_div_right
        apply Finset.sum_le_sum
        intro bucket _
        exact_mod_cast Nat.descFactorial_le 3 (hcard coord bucket)
    _ = _ := by
      have hf : (fun coord : Fin 7 => if coord = missing then
          Numeric.nearCoordinateEnvelope (word.map (fun row => row coord)) / 128^2
        else coordinateEnvelope (word.map (fun row => row coord)) / 128^3) =
          (fun coord : Fin 7 =>
            (if coord = missing then Numeric.nearCoordinateEnvelope (word.map (fun row => row coord))
              else coordinateEnvelope (word.map (fun row => row coord))) *
            (if coord = missing then ((128 : ENNReal)^2)⁻¹ else ((128 : ENNReal)^3)⁻¹)) := by
        funext coord
        split_ifs <;> rfl
      rw [hf, Finset.prod_mul_distrib, near_denominator_product]
      rfl
theorem nearCovered_le_wordEnvelope
    (word : List History.Buckets) (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (hcard : ∀ coord bucket, (exposed coord bucket).card ≤
      3*(word.map (fun row => row coord)).count bucket)
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[fun output => (SigGolfResearch.Gate6.digestRecord output).2.2.1=0 ∧
      NearCovered exposed missing omitted
        (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ History.nearWordEnvelope missing word := by
  rw [SigGolfResearch.Gate6.digest_gated_event_probability]
  refine (ENNReal.div_le_div_right (nearCovered_le_rawWordEnvelope word exposed hcard missing omitted) 8).trans_eq ?_
  simp only [rawNearWordEnvelope,History.nearWordEnvelope,div_eq_mul_inv,mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SigGolfCandidate.T3.BPORS
end
end
-- ==== merged from SphincsSecurity_Proof_Event_TruncatedCharge ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
noncomputable def truncatedPotential (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞) (budget count : Nat)
    (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  if count ≤ budget then potential cache + rate * ((budget - count : Nat) : ℝ≥0∞) else 0
theorem expected_truncatedPotential_le {α : Type}
    (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞)
    (hstep : ∀ (query : OracleWorld.Domain) (cache : QueryCache HashSpec), Finite cache →
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
        potential cache + (if query matches .inr _ then rate else 0))
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (budget : Nat) :
    (∑' result, Pr[= result | (simulateQ romImpl (countHashQueries computation)).run cache] *
      truncatedPotential potential rate budget result.1.2 result.2) ≤ potential cache + rate * budget := by
  induction computation using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, truncatedPotential,
        zero_le, if_true, Nat.sub_zero, le_refl]
  | query_bind query next ih =>
      rw [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, tsum_probOutput_map_mul]
      have hmass := romImpl_query_mass query cache
      cases query with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false, zero_add]
          calc
            _ ≤ ∑' result, Pr[= result | (romImpl (.inl sample)).run cache] * (potential result.2 + rate * budget) := by
              apply ENNReal.tsum_le_tsum
              intro result
              by_cases hresult : result ∈ support ((romImpl (.inl sample)).run cache)
              · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult) budget)
              · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
            _ = (∑' result, Pr[= result | (romImpl (.inl sample)).run cache] * potential result.2) + rate * budget := by
              simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
            _ ≤ _ := by
              have h := hstep (.inl sample) cache hfinite
              simp only [Bool.false_eq_true, if_false, add_zero] at h
              exact add_le_add h le_rfl
      | inr input =>
          simp only [if_true]
          cases budget with
          | zero =>
              refine le_trans (le_of_eq ?_) zero_le
              apply ENNReal.tsum_eq_zero.mpr
              intro result
              apply mul_eq_zero_of_right
              apply ENNReal.tsum_eq_zero.mpr
              intro inner
              apply mul_eq_zero_of_right
              simp [truncatedPotential]
          | succ remaining =>
              calc
                _ ≤ ∑' result, Pr[= result | (romImpl (.inr input)).run cache] * (potential result.2 + rate * remaining) := by
                  apply ENNReal.tsum_le_tsum
                  intro result
                  by_cases hresult : result ∈ support ((romImpl (.inr input)).run cache)
                  · apply mul_le_mul' le_rfl
                    refine le_trans (le_of_eq ?_) (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult) remaining)
                    apply tsum_congr
                    intro inner
                    congr 1
                    unfold truncatedPotential
                    by_cases hk : inner.1.2 ≤ remaining
                    · rw [if_pos (by omega), if_pos hk]
                      congr 3
                      omega
                    · rw [if_neg (by omega), if_neg hk]
                  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
                _ = (∑' result, Pr[= result | (romImpl (.inr input)).run cache] * potential result.2) + rate * remaining := by
                  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
                _ ≤ (potential cache + rate) + rate * remaining := add_le_add (by simpa using hstep (.inr input) cache hfinite) le_rfl
                _ = _ := by push_cast; ring
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_DigestLoopRecord ====
section

namespace SphincsSecurity.Concrete
open OracleSpec
abbrev DigestLoopRecord :=
  Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec
def selectedLoopView? (result : DigestLoopRecord) : Option FewTimeView :=
  result.1.map (fun selected => selectedFewTimeView selected.2.1 selected.2.2)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_DigestSelectionIndex ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem uniform_view_index_weight_expectation (weight : Index → ENNReal) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source.1) =
      (∑ index : Index, weight index) / (Fintype.card Index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalSPMF_map_fst_uniformSample_prod (α := Index) (β := IndexGroup → FtsLeaf))
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := weight)]
  simp only [hmarginal, probOutput_uniformSample, tsum_fintype, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
noncomputable def completeSelectedIndex (view : Option FewTimeView) : ProbComp Index :=
  view.elim ($ᵗ Index) (fun selected => pure selected.1)
theorem probEvent_uniform_view_index (index : Index) :
    Pr[fun view : FewTimeView => view.1 = index | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      (Fintype.card Index : ENNReal)⁻¹ := by
  rw [probEvent_eq_tsum_ite]
  have h := uniform_view_index_weight_expectation
    (fun source => if source = index then (1 : ENNReal) else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, one_div] using h
theorem cachedMessageEntryCountWhere_index_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun view => view.1 = index) ≤
      cachedIndexMultiplicity key.parameter cache index := by
  let entries := cachedMessageInputSetWhere cache key.parameter key.root message (fun view => view.1 = index)
  let inputOf : entries → HashInput := fun entry => entry.1.1
  have hinjective : Function.Injective inputOf := by
    rintro ⟨⟨left, leftOutput⟩, hleft⟩ ⟨⟨right, rightOutput⟩, hright⟩ heq
    change left = right at heq
    subst right
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Option.some.inj (hleft.1.1.symm.trans hright.1.1)))
  have hweight (entry : entries) :
      cacheMessageEntryWeight key.parameter (fun _ view => if view.1 = index then 1 else 0)
        cache (inputOf entry) = 1 := by
    rcases entry with ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hindex⟩
    change cache input = some output at hcached
    have hmessage : FtsProbeSimulation.MessageHashInput key.parameter input :=
      ⟨messageDigestPayload key.root message randomness, hinput.symm⟩
    have hvalid := (signAttemptResultOfOutput_ne_none_iff output).mp hadmissible
    simp only [inputOf, cacheMessageEntryWeight, hcached, hmessage, hvalid, and_self,
      if_true, hindex]
  calc
    _ = ∑' _ : entries, (1 : ENNReal) := (ENNReal.tsum_set_one entries).symm
    _ = ∑' entry : entries, cacheMessageEntryWeight key.parameter
        (fun _ view => if view.1 = index then 1 else 0) cache (inputOf entry) :=
      tsum_congr (fun entry => (hweight entry).symm)
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinjective _
private theorem selectedLoopView_partition (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) (result : DigestLoopRecord)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    (if ∃ view, selectedLoopView? result = some view ∧ P view then (1 : ENNReal) else 0) =
      (if FreshSelectedView cache key message P result then 1 else 0) +
        (if PrehitSelectedView cache key message P result then 1 else 0) := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      cases hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView, hc]
      | some output =>
          have hattempt := signDigestLoop_initial_cached_result attempts key message randomness index leaves cache after output hc hr
          have hview : selectedFewTimeView index leaves = hashOutputFewTimeView output :=
            signAttemptResultOfOutput_view output index leaves hattempt
          simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView, hc, hattempt, hview]
theorem probEvent_selectedLoopView_eq_fresh_add_cached (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[fun result => ∃ view, selectedLoopView? result = some view ∧ P view |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      freshDigestSelectionProbability key message cache * Pr[P | signerViewSample] +
        cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  unfold freshDigestSelectionProbability
  rw [← probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message cache cache P
    (onlyRejectedNewMessageEntries_self cache key message),
    ← probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight]
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache)
  · have h := congrArg (fun value =>
      Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] * value)
      (selectedLoopView_partition digestAttemptLimit key message cache P result hr)
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add]
theorem probOutput_completeSelectedLoopIndex (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] =
      (freshDigestSelectionProbability key message cache + digestExhaustionProbability key message cache) *
        (Fintype.card Index : ENNReal)⁻¹ +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun view => view.1 = index) *
        exactDigestReuseWeight key message cache := by
  have h := probEvent_completeOption_eq
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache)
    (fun result => (selectedLoopView? result).map Prod.fst) ($ᵗ Index) (fun selected => selected = index)
  have hcomplete (view : Option FewTimeView) :
      (view.map Prod.fst).elim ($ᵗ Index : ProbComp Index) pure = completeSelectedIndex view := by
    cases view <;> rfl
  have hselected (result : DigestLoopRecord) :
      (∃ selected, (selectedLoopView? result).map Prod.fst = some selected ∧ selected = index) ↔
        ∃ view, selectedLoopView? result = some view ∧ view.1 = index := by
    cases selectedLoopView? result <;> simp
  have hnone (result : DigestLoopRecord) : (selectedLoopView? result).map Prod.fst = none ↔ result.1 = none := by
    cases hresult : result.1 <;> simp [selectedLoopView?, hresult]
  simp only [hcomplete, hselected, hnone] at h
  rw [probEvent_selectedLoopView_eq_fresh_add_cached, probEvent_signerView_index] at h
  simpa only [probEvent_eq_eq_probOutput, probOutput_uniformSample, digestExhaustionProbability,
    add_mul, add_assoc, add_comm, add_left_comm] using h
theorem probOutput_completeSelectedLoopIndex_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] ≤
      (Fintype.card Index : ENNReal)⁻¹ +
        exactDigestReuseWeight key message cache * cachedIndexMultiplicity key.parameter cache index := by
  rw [probOutput_completeSelectedLoopIndex]
  have hmass : freshDigestSelectionProbability key message cache + digestExhaustionProbability key message cache ≤ 1 := by
    calc
      _ ≤ (freshDigestSelectionProbability key message cache +
          cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) *
            exactDigestReuseWeight key message cache) + digestExhaustionProbability key message cache :=
        add_le_add le_self_add le_rfl
      _ = 1 := freshSelection_add_count_exactWeight_add_exhaustion key message cache
  exact add_le_add (mul_le_of_le_one_left' hmass)
    ((mul_le_mul' (cachedMessageEntryCountWhere_index_le key message cache index) le_rfl).trans_eq (mul_comm _ _))
theorem probOutput_completeSelectedLoopIndex_le_proposalRate (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (spent : Nat) (hspent : spent ≤ 2 ^ 127)
    (hcache : QueryCache.enncard cache ≤ spent) (hclean : ¬ MessageDeficitExceptional key cache)
    (hindex : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] ≤ targetProposalIndexRate := by
  apply (probOutput_completeSelectedLoopIndex_le key message cache index).trans
  apply (add_le_add le_rfl (mul_le_mul'
    (exactDigestReuseWeight_le_near_uniform_of_clean_cache key cache spent hspent hcache hclean message) le_rfl)).trans
  simpa only [Nat.add_zero, Nat.cast_zero, zero_mul, add_zero] using
    targetProposalRate_of_cache_bound (cachedIndexMultiplicity key.parameter cache index)
      spent 0 0 0 hspent (Nat.zero_le _) (Nat.zero_le _) (hindex index)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_CachedIndexHashMoments ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem enncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (hfresh : cache input = none) :
    QueryCache.enncard (cache.cacheQuery input output) = QueryCache.enncard cache + 1 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro pair (heq | hold)
    · subst pair
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ cache.toSet := by
    simp only [QueryCache.mem_toSet, hfresh, reduceCtorEq, not_false_eq_true]
  unfold QueryCache.enncard
  rw [hset, Set.encard_insert_of_notMem hnot]
  simp
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
theorem cachedIndexMultiplicity_le_enncard (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤ QueryCache.enncard cache := by
  unfold cachedIndexMultiplicity cacheMessageWeight
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hnone : cache input = none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp only [cacheMessageEntryWeight, hnone])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold cacheMessageEntryWeight
      cases cache input <;> simp only
      · exact zero_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem cachedIndexMultiplicity_ne_top (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) : cachedIndexMultiplicity parameter cache index ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedIndexMultiplicity_le_enncard parameter cache hfinite index)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
noncomputable def cachedIndexExcessScore (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (index : Index) : ℝ :=
  (cachedIndexMultiplicity parameter cache index).toReal - (QueryCache.enncard cache).toReal * cachedIndexRate.toReal
theorem cachedIndexExcessScore_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (input : HashInput) (output : HashOutput)
    (hfresh : cache input = none) (index : Index) :
    cachedIndexExcessScore parameter (cache.cacheQuery input output) index =
      cachedIndexExcessScore parameter cache index +
        (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧
          (hashOutputFewTimeView output).1 = index then 1 else 0) - cachedIndexRate.toReal := by
  have hcount := cachedIndexMultiplicity_ne_top parameter cache hfinite index
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  unfold cachedIndexExcessScore
  rw [cachedIndexMultiplicity_cacheQuery parameter cache input output hfresh,
    enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add hcard (by finiteness), ENNReal.toReal_one]
  split_ifs <;> simp only [add_zero, ENNReal.toReal_add hcount (by finiteness), ENNReal.toReal_one] <;> ring
theorem cachedIndexExcessScore_nonpos_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (index : Index) : cachedIndexExcessScore parameter cache index ≤ 0 := by
  rw [cachedIndexExcessScore, cachedIndexMultiplicity, cacheMessageWeight_of_no_message parameter _ cache hnone,
    ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
def CachedIndexExcessExceptional (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ index, (2 ^ 72 : ℝ) < cachedIndexExcessScore parameter cache index
theorem cachedIndexExcessExceptional_of_bound_failure (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (spent : Nat)
    (hcache : QueryCache.enncard cache ≤ spent) (index : Index)
    (hbad : (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) <
      cachedIndexMultiplicity parameter cache index) : CachedIndexExcessExceptional parameter cache := by
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hreal := (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by finiteness) cachedIndexRate_ne_top, by finiteness⟩)
    (cachedIndexMultiplicity_ne_top parameter cache hfinite index)).mpr hbad
  have hcacheReal := (ENNReal.toReal_le_toReal hcard (by finiteness)).mpr hcache
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by finiteness) cachedIndexRate_ne_top) (by finiteness),
    ENNReal.toReal_mul] at hreal
  norm_num at hreal hcacheReal
  refine ⟨index, ?_⟩
  unfold cachedIndexExcessScore
  have hscaled := mul_le_mul_of_nonneg_right hcacheReal (ENNReal.toReal_nonneg (a := cachedIndexRate))
  norm_num at hscaled ⊢
  linarith
theorem cachedIndex_bound_of_no_excess (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (spent : Nat) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ CachedIndexExcessExceptional parameter cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) := by
  by_contra hbad
  exact hclean (cachedIndexExcessExceptional_of_bound_failure parameter cache hfinite spent hcache index
    (lt_of_not_ge hbad))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
theorem positivePart_shift_even_le (score shift : ℝ) (power : Nat) (heven : Even power) :
    max (score + shift) 0 ^ power ≤ (max score 0 + shift) ^ power := by
  by_cases hnonneg : 0 ≤ score + shift
  · rw [max_eq_left hnonneg]
    exact pow_le_pow_left₀ hnonneg (add_le_add (le_max_left score 0) le_rfl) power
  · rw [max_eq_right (le_of_not_ge hnonneg)]
    by_cases hpower : power = 0
    · simp [hpower]
    · rw [zero_pow hpower]
      exact heven.pow_nonneg _
theorem bernoulliExcess_secondMoment_le (score probability : ℝ)
    (hprob : 0 ≤ probability) (hprob_one : probability ≤ 1) :
    probability * max (score + (1 - probability)) 0 ^ 2 +
        (1 - probability) * max (score + (-probability)) 0 ^ 2 ≤
      max score 0 ^ 2 + probability := by
  let d := max score 0
  have hmiss : 0 ≤ 1 - probability := sub_nonneg.mpr hprob_one
  calc
    _ ≤ probability * (d + (1 - probability)) ^ 2 +
        (1 - probability) * (d + (-probability)) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (1 - probability) 2 (by decide)) hprob)
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (-probability) 2 (by decide)) hmiss)
    _ = d ^ 2 + probability * (1 - probability) := by ring
    _ ≤ _ := by dsimp only [d]; nlinarith [sq_nonneg probability]
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
def AdmissibleIndexOutput (index : Index) (output : HashOutput) : Prop :=
  Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index
theorem probEvent_uniformHashOutput_admissible_index (index : Index) :
    Pr[AdmissibleIndexOutput index | ($ᵗ HashOutput : ProbComp HashOutput)] =
      cachedIndexRate := by
  change Pr[fun output : HashOutput =>
    Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index |
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have h := probEvent_uniformHashOutput_admissible_view (fun view => view.1 = index)
  rw [probEvent_signerView_index] at h
  simpa only [signAttemptResultOfOutput_ne_none_iff, cachedIndexRate] using h
theorem expected_uniformHashOutput_index_choice (index : Index) (accepted rejected : ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if AdmissibleIndexOutput index output then accepted else rejected)) =
      cachedIndexRate * accepted +
        (1 - cachedIndexRate) * rejected := by
  have hnot : Pr[fun output => ¬ AdmissibleIndexOutput index output |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 1 - cachedIndexRate := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (AdmissibleIndexOutput index)
    rw [probFailure_of_liftM_PMF, tsub_zero, probEvent_uniformHashOutput_admissible_index, add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hsplit (output : HashOutput) :
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if AdmissibleIndexOutput index output then accepted else rejected) =
        (if AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬ AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    by_cases h : AdmissibleIndexOutput index output <;>
      simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false, zero_mul, zero_add, add_zero]
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite,
    probEvent_uniformHashOutput_admissible_index, hnot]
theorem bernoulliExcess_secondMoment_ennreal (score : ℝ) (probability : ENNReal)
    (hprob : probability ≤ 1) :
    probability * positiveScoreMoment (score + (1 - probability.toReal)) 2 +
        (1 - probability) * positiveScoreMoment (score + (-probability.toReal)) 2 ≤
      positiveScoreMoment score 2 + probability := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hprob
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness)
    (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hprob (by finiteness), ENNReal.toReal_one,
    positiveScoreMoment, ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _)]
  exact bernoulliExcess_secondMoment_le score probability.toReal ENNReal.toReal_nonneg
    ((ENNReal.toReal_mono (by finiteness) hprob).trans_eq ENNReal.toReal_one)
theorem positiveScoreMoment_mono (power : Nat) {before after : ℝ} (hle : before ≤ after) :
    positiveScoreMoment before power ≤ positiveScoreMoment after power :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _) (max_le_max hle le_rfl) power)
private theorem expected_cachedIndexScore_nonmessage_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hmessage : ¬ FtsProbeSimulation.MessageHashInput parameter input) (index : Index) (power : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) power) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
  simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
    hmessage, false_and, if_false, add_zero]
  calc
    _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
      apply ENNReal.tsum_le_tsum
      intro output
      exact mul_le_mul' le_rfl (positiveScoreMoment_mono power (sub_le_self _ (by positivity)))
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
theorem expected_cachedIndexScore_second_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (index : Index) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 + cachedIndexRate := by
  by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input
  · simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
      hmessage, true_and]
    have hchoice (output : HashOutput) :
        positiveScoreMoment (cachedIndexExcessScore parameter cache index +
          (if Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) -
          cachedIndexRate.toReal) 2 =
        if AdmissibleIndexOutput index output then
          positiveScoreMoment (cachedIndexExcessScore parameter cache index + (1 - cachedIndexRate.toReal)) 2
        else positiveScoreMoment (cachedIndexExcessScore parameter cache index + (-cachedIndexRate.toReal)) 2 := by
      unfold AdmissibleIndexOutput
      split_ifs <;> congr 1 <;> ring
    simp_rw [hchoice]
    rw [expected_uniformHashOutput_index_choice]
    exact bernoulliExcess_secondMoment_ennreal (cachedIndexExcessScore parameter cache index)
      cachedIndexRate cachedIndexRate_le_one
  · exact (expected_cachedIndexScore_nonmessage_le parameter cache hfinite input hfresh hmessage index 2).trans le_self_add
end SphincsSecurity.Concrete
end
end
-- ==== merged from T3_Gate6_ActualSearch ====
section

section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
abbrev Output := BitVec 256
abbrev History (Input : Type) := List (Input × Output)
structure Cache (Input : Type) where
  entries : List (Input × Output)
  unique : (entries.map Prod.fst).Nodup
def empty {Input : Type} : Cache Input := ⟨[],by simp⟩
def lookup {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) : Option Output :=
  cache.entries.lookup input
def insert {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) (output : Output)
    (fresh : lookup cache input=none) : Cache Input :=
  ⟨(input,output)::cache.entries,by
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,cache.unique⟩
    intro hi
    obtain ⟨pair,hpair,heq⟩ := List.mem_map.mp hi
    have h := List.lookup_eq_none_iff.mp fresh pair hpair
    simp [heq] at h⟩
def Matches (mark : MarkedLabel) (output : Output) : Prop :=
  DigestAccepted output ∧ (digestRecord output).1=mark
noncomputable def count {Input : Type} (mark : MarkedLabel) (cache : Cache Input) : Nat :=
  cache.entries.countP (fun pair => decide (Matches mark pair.2))
noncomputable def eRate : ENNReal := acceptance/2^59
noncomputable def rate : ℝ := eRate.toReal
noncomputable def Bad {Input : Type} (cache : Cache Input) : Prop :=
  ∃ mark : MarkedLabel, (cache.entries.length : ℝ)*rate+2^47 < count mark cache
theorem probability_matches (mark : MarkedLabel) :
    Pr[Matches mark | ($ᵗ Output : ProbComp Output)] = eRate := digest_mark_joint_exact mark
theorem eRate_finite : eRate ≠ ⊤ := by unfold eRate acceptance;finiteness
theorem eRate_le_one : eRate ≤ 1 := by
  rw [← probability_matches (0,fun _ => 0)]
  exact probEvent_le_one
theorem rate_value : rate =
    (6963897326262647489342145 : ℝ)/(19807040628566084398385987584*2^59) := by
  norm_num [rate,eRate,acceptance,ENNReal.toReal_div,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal]
theorem rate_nonneg : 0≤rate := ENNReal.toReal_nonneg
theorem rate_le_one : rate≤1 := by
  exact (ENNReal.toReal_mono (by finiteness) eRate_le_one).trans_eq ENNReal.toReal_one
theorem count_insert {Input : Type} [DecidableEq Input] (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    count mark (insert cache input output fresh) = count mark cache + if Matches mark output then 1 else 0 := by
  by_cases h : Matches mark output <;> simp [count,insert,List.countP_cons,h]
theorem insert_length {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input)
    (output : Output) (fresh : lookup cache input=none) :
    (insert cache input output fresh).entries.length=cache.entries.length+1 := rfl
theorem not_bad_empty {Input : Type} : ¬Bad (empty : Cache Input) := by
  rintro ⟨mark,h⟩
  norm_num [empty,count] at h
noncomputable def run {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) : Nat → History Input → Cache Input → ProbComp Bool
  | 0,_,cache => pure (decide (Bad cache))
  | steps+1,history,cache =>
    if Bad cache then pure true else do
      let input ← policy history
      match fresh : lookup cache input with
      | some output => run policy steps ((input,output)::history) cache
      | none => do
          let output ← ($ᵗ Output : ProbComp Output)
          run policy steps ((input,output)::history) (insert cache input output fresh)
end SigGolfResearch.Gate6.Cache
end
section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000
noncomputable def theta : ℝ := 1/4096
noncomputable def growth : ℝ := rate*theta/(1-theta)
theorem theta_pos : 0<theta := by norm_num [theta]
theorem theta_lt_one : theta<1 := by norm_num [theta]
theorem growth_ge_center : theta*rate≤growth := by
  unfold growth
  apply (le_div_iff₀ (by linarith [theta_lt_one])).mpr
  nlinarith [mul_nonneg rate_nonneg (sq_nonneg theta)]
theorem bernoulli_mgf_real : rate*Real.exp theta+(1-rate)≤Real.exp growth := by
  have he := (Real.exp_bound_div_one_sub_of_interval' theta_pos theta_lt_one).le
  calc
    _ ≤ rate*(1/(1-theta))+(1-rate) := by gcongr;exact rate_nonneg
    _ = 1+growth := by unfold growth;field_simp [(sub_pos.mpr theta_lt_one).ne'];ring
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp growth
theorem centered_initial_exponent (q : Nat) (hq : q≤2^127) :
    (q : ℝ)*(growth-theta*rate)-theta*2^47≤-1000 := by
  have hqR : (q : ℝ)≤2^127 := by exact_mod_cast hq
  calc
    _ ≤ (2^127 : ℝ)*(growth-theta*rate)-theta*2^47 := by
      gcongr
      exact sub_nonneg.mpr growth_ge_center
    _ ≤ -1000 := by norm_num [growth,theta,rate_value]
theorem initial_tail_real (q : Nat) (hq : q≤2^127) :
    Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)≤(2^759 : ℝ)⁻¹ := by
  have hlog : Real.log (2 : ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  calc
    _ ≤ Real.exp (-759*Real.log 2) := Real.exp_le_exp.mpr (by linarith [centered_initial_exponent q hq])
    _ = _ := by
      rw [neg_mul,Real.exp_neg]
      have he : Real.exp (759*Real.log 2)=(2 : ℝ)^759 := by
        simpa using (Real.exp_nat_mul (Real.log 2) 759).trans (congrArg (fun x : ℝ => x^759) (Real.exp_log (by norm_num : (0 : ℝ)<2)))
      rw [he]
theorem bernoulli_shift_real (x : ℝ) :
    rate*Real.exp (x+theta-growth)+(1-rate)*Real.exp (x-growth)≤Real.exp x := by
  have h := mul_le_mul_of_nonneg_left bernoulli_mgf_real (Real.exp_pos (x-growth)).le
  have he : Real.exp (x+theta-growth)=Real.exp (x-growth)*Real.exp theta := by rw [←Real.exp_add];congr 1;ring
  have hcancel : Real.exp (x-growth)*Real.exp growth=Real.exp x := by rw [←Real.exp_add];congr 1;ring
  rw [hcancel] at h
  rw [he]
  nlinarith
end SigGolfResearch.Gate6.Cache
end
section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 300000
noncomputable def score {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ℝ :=
  theta*(count mark cache : ℝ)+growth*((q : ℝ)-cache.entries.length)-theta*(rate*q+2^47)
noncomputable def weight {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight {Input : Type} (q : Nat) (cache : Cache Input) : ENNReal :=
  ∑ mark : MarkedLabel,weight q mark cache
theorem expected_choice (mark : MarkedLabel) (yes no : ENNReal) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no)) =
      eRate*yes+(1-eRate)*no := by
  have hnot : Pr[fun d => ¬Matches mark d | ($ᵗ Output : ProbComp Output)] = 1-eRate := by
    have h := probEvent_compl ($ᵗ Output : ProbComp Output) (Matches mark)
    rw [probFailure_of_liftM_PMF,tsub_zero,probability_matches,add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hs (output : Output) : Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no) =
      (if Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*yes+
      (if ¬Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*no := by
    by_cases h : Matches mark output <;> simp [h]
  simp_rw [hs,ENNReal.tsum_add,ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,probability_matches,hnot]
theorem weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    weight q mark (insert cache input output fresh) =
      if Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+theta-growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-growth)) := by
  unfold weight score
  rw [count_insert,insert_length]
  by_cases h : Matches mark output <;> simp only [h,if_true,if_false,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
  all_goals congr 2 <;> ring
theorem expected_weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      weight q mark (insert cache input output fresh))≤weight q mark cache := by
  simp_rw [weight_insert]
  rw [expected_choice]
  have heFinite := eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact bernoulli_shift_real (score q mark cache)
theorem expected_totalWeight_insert {Input : Type} [DecidableEq Input] (q : Nat)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      totalWeight q (insert cache input output fresh))≤totalWeight q cache := by
  simp only [totalWeight,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_le_sum fun mark _ => expected_weight_insert q mark cache input fresh
theorem weight_bad {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input)
    (hq : cache.entries.length≤q)
    (hbad : (cache.entries.length : ℝ)*rate+2^47 < count mark cache) : 1≤weight q mark cache := by
  have hqR : 0≤(q : ℝ)-cache.entries.length := sub_nonneg.mpr (by exact_mod_cast hq)
  have hprod := mul_nonneg (sub_nonneg.mpr growth_ge_center) hqR
  have hpositive := mul_nonneg theta_pos.le (sub_nonneg.mpr hbad.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  calc
    1 = ENNReal.ofReal (Real.exp 0) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
theorem totalWeight_bad {Input : Type} (q : Nat) (cache : Cache Input)
    (hq : cache.entries.length≤q) (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  exact (weight_bad q mark cache hq hmark).trans
    (show weight q mark cache≤totalWeight q cache from
      Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))
theorem totalWeight_empty {Input : Type} (q : Nat) :
    totalWeight q (empty : Cache Input) =
      (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark (empty : Cache Input) =
      ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
    unfold weight score count empty
    simp only [List.countP_nil,List.length_nil,Nat.cast_zero,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat]
theorem initial_totalWeight_le {Input : Type} (q : Nat) (hq : q≤2^127) :
    totalWeight q (empty : Cache Input)≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty]
  calc
    _ ≤ (2^59 : ENNReal)*ENNReal.ofReal ((2^759 : ℝ)⁻¹) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (initial_tail_real q hq))
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal (show (0 : ℝ)≤(2^759 : ℝ)⁻¹ by positivity)]
      rw [show (2 : ℝ)^759=2^59*2^700 by rw [←pow_add]]
      field_simp
end SigGolfResearch.Gate6.Cache
end
section
namespace SigGolfResearch.Gate6.NativeCache
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SphincsSecurity (Finite)
abbrev RCache := SigGolfCandidate.T3.Sampling.RCache
open SphincsSecurity.Concrete (enncard_cacheQuery_of_fresh)
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def entry (mark : MarkedLabel) (cache : RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun output => if Cache.Matches mark output then 1 else 0)
noncomputable def count (mark : MarkedLabel) (cache : RCache) : ENNReal := ∑' input,entry mark cache input
theorem count_empty (mark : MarkedLabel) : count mark ∅=0 := by simp [count,entry]
theorem count_cacheQuery (mark : MarkedLabel) (cache : RCache) (input : HashInput)
    (output : HashOutput) (hfresh : cache input=none) :
    count mark (cache.cacheQuery input output)=count mark cache+
      if Cache.Matches mark output then 1 else 0 := by
  unfold count
  rw [ENNReal.tsum_eq_add_tsum_ite (f := entry mark (cache.cacheQuery input output)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := entry mark cache) input]
  simp only [entry,QueryCache.cacheQuery_self,hfresh,Option.elim_none,Option.elim_some,zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other=input
  · simp [heq]
  · simp only [heq,if_false,QueryCache.cacheQuery_of_ne cache output heq]
theorem count_le_enncard (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≤ QueryCache.enncard cache := by
  unfold count
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hn : cache input=none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp [entry,hn])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset,(1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold entry
      cases cache input <;> simp only [Option.elim_none,Option.elim_some]
      · exact bot_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem enncard_ne_top (cache : RCache) (hfinite : Finite cache) : QueryCache.enncard cache ≠ ⊤ := by
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem count_ne_top (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≠ ⊤ := ne_top_of_le_ne_top (enncard_ne_top cache hfinite) (count_le_enncard mark cache hfinite)
noncomputable def Bad (cache : RCache) : Prop :=
  ∃ mark : MarkedLabel,(QueryCache.enncard cache).toReal*Cache.rate+2^47 < (count mark cache).toReal
noncomputable def score (q : Nat) (mark : MarkedLabel) (cache : RCache) : ℝ :=
  Cache.theta*(count mark cache).toReal+Cache.growth*((q : ℝ)-(QueryCache.enncard cache).toReal)-
    Cache.theta*(Cache.rate*q+2^47)
noncomputable def weight (q : Nat) (mark : MarkedLabel) (cache : RCache) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight (q : Nat) (cache : RCache) : ENNReal := ∑ mark : MarkedLabel,weight q mark cache
theorem score_cacheQuery (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (output : HashOutput) (hfresh : cache input=none) :
    score q mark (cache.cacheQuery input output)=score q mark cache+
      (if Cache.Matches mark output then Cache.theta else 0)-Cache.growth := by
  unfold score
  rw [count_cacheQuery mark cache input output hfresh,enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add (enncard_ne_top cache hfinite) (by finiteness),ENNReal.toReal_one]
  have hsum : (count mark cache+1).toReal=(count mark cache).toReal+1 := by
    rw [ENNReal.toReal_add (count_ne_top mark cache hfinite) ENNReal.one_ne_top,ENNReal.toReal_one]
  have hsum' : (1+count mark cache).toReal=1+(count mark cache).toReal := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top (count_ne_top mark cache hfinite),ENNReal.toReal_one]
  split_ifs <;> (try rw [hsum]) <;> (try rw [hsum']) <;> (try simp only [add_zero]) <;> ring
theorem expected_weight_fresh (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => weight q mark (cache.cacheQuery input output)) ≤ weight q mark cache := by
  have he (output : HashOutput) : weight q mark (cache.cacheQuery input output)=
      if Cache.Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+Cache.theta-Cache.growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-Cache.growth)) := by
    unfold weight
    rw [score_cacheQuery q mark cache hfinite input output hfresh]
    split_ifs <;> simp
  simp_rw [he]
  change (∑' output,Pr[=output | ($ᵗ Cache.Output : ProbComp Cache.Output)]*_)≤_
  rw [Cache.expected_choice]
  have heFinite := Cache.eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le Cache.eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact Cache.bernoulli_shift_real (score q mark cache)
theorem expected_totalWeight_fresh (q : Nat) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => totalWeight q (cache.cacheQuery input output)) ≤ totalWeight q cache := by
  unfold totalWeight
  rw [expectedValue_finsetSum]
  exact Finset.sum_le_sum fun mark _ => expected_weight_fresh q mark cache hfinite input hfresh
theorem totalWeight_bad (q : Nat) (cache : RCache) (hq : QueryCache.enncard cache≤q)
    (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  have hqR : 0≤(q : ℝ)-(QueryCache.enncard cache).toReal := by
    apply sub_nonneg.mpr
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hq
  have hprod := mul_nonneg (sub_nonneg.mpr Cache.growth_ge_center) hqR
  have hpositive := mul_nonneg Cache.theta_pos.le (sub_nonneg.mpr hmark.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  have hw : 1≤weight q mark cache := by
    calc
      1 = ENNReal.ofReal (Real.exp 0) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
  exact hw.trans (Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))
theorem totalWeight_empty (q : Nat) : totalWeight q ∅ =
    (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark ∅=
      ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
    unfold weight score
    simp only [count_empty,ENNReal.toReal_zero,QueryCache.enncard_empty,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
theorem initial_totalWeight_le (q : Nat) (hq : q≤2^127) : totalWeight q ∅≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty,← Cache.totalWeight_empty (Input := HashInput)]
  exact Cache.initial_totalWeight_le q hq
theorem not_bad_empty : ¬Bad ∅ := by
  rintro ⟨mark,h⟩
  norm_num [count_empty,QueryCache.enncard] at h
theorem clean_point_bound_arithmetic (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache≤budget) (hbudget : budget≤2^127)
    (hclean : ¬Bad cache) (mark : MarkedLabel) :
    1/(2 : ENNReal)^59+count mark cache/(2 : ENNReal)^128 ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have hex : (count mark cache).toReal ≤ (QueryCache.enncard cache).toReal*Cache.rate+2^47 :=
    le_of_not_gt (fun h => hclean ⟨mark,h⟩)
  have hcache : (QueryCache.enncard cache).toReal≤(budget : ℝ) := by
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hsize
  have hbudgetR : (budget : ℝ)≤2^127 := by exact_mod_cast hbudget
  have hscale := mul_le_mul_of_nonneg_right (hcache.trans hbudgetR) Cache.rate_nonneg
  apply (ENNReal.toReal_le_toReal (by have := count_ne_top mark cache hfinite;finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.div_ne_top (count_ne_top mark cache hfinite) (by norm_num))]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  calc
    _ ≤ 1/(2 : ℝ)^59+((2 : ℝ)^127*Cache.rate+2^47)/(2 : ℝ)^128 := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by norm_num [Cache.rate_value]
end SigGolfResearch.Gate6.NativeCache
end
section
namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def acceptedWeight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) : ENNReal :=
  expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => (decoder answer).elim 0 payoff)
theorem uniform_decoder_weight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) (rejected : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => (decoder answer).elim rejected payoff)=
      acceptedWeight decoder payoff+failMass decoder*rejected := by
  classical
  have hp (answer : HashOutput) :
      (decoder answer).elim rejected payoff=(decoder answer).elim 0 payoff+
        (if decoder answer=none then 1 else 0)*rejected := by
    cases decoder answer <;> simp
  simp_rw [hp]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_ite_one]
  have hf : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent decoder
  rw [← hf]
  rfl
def CachedTrialScoresBound {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal) (price : ENNReal)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer →
    (decoder answer).elim 0 weight ≤ price
theorem expected_publicSearch_completed_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim price payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
theorem digestTrial_nonce_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat}
    (he : digestTrial rho message counter=digestTrial rho' message' counter') : rho=rho' := by
  have h := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  exact (digestInput_injective h).1
noncomputable def decode (answer : HashOutput) : Option HashOutput :=
  if DigestAccepted answer then some answer else none
noncomputable def search (rho : Digest) (message : Message) (fuel : Nat) : M (Option (BitVec 32 × HashOutput)) :=
  publicProgram (searchLoop (digestTrial rho message) decode
    (fun c output => pure (BitVec.ofNat 32 c,output)) fuel 0)
noncomputable def hit (mark : MarkedLabel) (output : HashOutput) : ENNReal :=
  if (digestRecord output).1=mark then 1 else 0
noncomputable def completedScore (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) : ENNReal :=
  found.elim (1/2^59) (fun value => hit mark value.2)
theorem acceptance_le_one : acceptance≤1 := by
  rw [← digest_acceptance_exact]
  exact probEvent_le_one
theorem decoder_failure : failMass decode=1-acceptance := by
  rw [failMass_eq_probEvent]
  change Pr[fun output : HashOutput => decode output=none | ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have he : (fun output => decode output=none)=(fun output => ¬DigestAccepted output) := by
    funext output
    simp [decode]
  rw [he]
  have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) DigestAccepted
  rw [probFailure_of_liftM_PMF,tsub_zero,digest_acceptance_exact,add_comm] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) h
theorem accepted_hit (mark : MarkedLabel) : acceptedWeight decode (hit mark)=acceptance/2^59 := by
  unfold acceptedWeight
  have he (output : HashOutput) : (decode output).elim 0 (hit mark)=
      if DigestAccepted output ∧ (digestRecord output).1=mark then 1 else 0 := by
    simp only [decode,hit]
    split_ifs <;> simp_all [hit]
  simp_rw [he]
  rw [expectedValue_ite_one]
  exact digest_mark_joint_exact mark
theorem completedScore_le_one (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) :
    completedScore mark found≤1 := by
  cases found with
  | none => norm_num [completedScore]
  | some value => unfold completedScore hit;simp only [Option.elim_some];split_ifs <;> norm_num
noncomputable def CachedHit (rho : Digest) (message : Message) (fuel : Nat)
    (cache : RCache) (mark : MarkedLabel) : Prop :=
  ∃ c,c<fuel ∧ ∃ output,cache (digestTrial rho message c)=some output ∧
    Cache.Matches mark output
theorem completed_search_no_cached_hit (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel)
    (hno : ¬CachedHit rho message fuel cache mark) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤1/2^59 := by
  unfold search completedScore
  apply expected_publicSearch_completed_le_of_cached_scores secret (digestTrial rho message) decode
    (fun c output => (BitVec.ofNat 32 c,output)) (fun found => hit mark found.2)
    (hit mark) (fun _ _ => rfl) (1/2^59) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf output ha
    by_cases hadm : DigestAccepted output
    · have hnot : (digestRecord output).1≠mark := fun ht => hno ⟨c,hf,output,ha,hadm,ht⟩
      simp [decode,hadm,hit,hnot]
    · simp [decode,hadm]
  · rw [accepted_hit,decoder_failure]
    calc
      _ = (acceptance+(1-acceptance))*(1/2^59) := by simp only [div_eq_mul_inv,one_mul];ring
      _ = 1/2^59 := by rw [add_tsub_cancel_of_le acceptance_le_one,one_mul]
      _ ≤ _ := le_rfl
theorem completed_search_cached_event (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤
      1/2^59+if CachedHit rho message fuel cache mark then 1 else 0 := by
  by_cases h : CachedHit rho message fuel cache mark
  · rw [if_pos h]
    exact (expectedValue_le_of_le _ fun _ => completedScore_le_one mark _).trans (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact completed_search_no_cached_hit secret rho message fuel hlimit cache mark h
noncomputable def cachedNonces (message : Message) (fuel : Nat) (cache : RCache)
    (mark : MarkedLabel) : Finset Digest := Finset.univ.filter fun rho => CachedHit rho message fuel cache mark
theorem cachedNonces_card_le_count (message : Message) (fuel : Nat) (cache : RCache) (mark : MarkedLabel) :
    ((cachedNonces message fuel cache mark).card : ENNReal)≤NativeCache.count mark cache := by
  classical
  let nonces := cachedNonces message fuel cache mark
  have hw : ∀ rho : nonces,∃ counter,counter<fuel ∧ ∃ output,
      cache (digestTrial rho.val message counter)=some output ∧ Cache.Matches mark output := by
    intro rho
    exact (Finset.mem_filter.mp rho.property).2
  choose counter hc output ha htarget using hw
  let inputs (rho : nonces) := digestTrial rho.val message (counter rho)
  have hinj : Function.Injective inputs := by
    intro left right he
    exact Subtype.ext (digestTrial_nonce_injective he)
  have hentry (rho : nonces) : NativeCache.entry mark cache (inputs rho)=1 := by
    simp only [NativeCache.entry,inputs,ha,Option.elim_some,htarget,if_true]
  calc
    _ = ∑ rho : nonces,NativeCache.entry mark cache (inputs rho) := by
      simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,nonces]
    _ ≤ ∑' input,NativeCache.entry mark cache input := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comp_le_tsum_of_injective hinj (NativeCache.entry mark cache))
    _ = _ := rfl
theorem uniform_nonce_completed_point (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      1/(2 : ENNReal)^59+NativeCache.count mark cache/(2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        1/(2 : ENNReal)^59+if CachedHit rho message fuel cache mark then 1 else 0) :=
      expectedValue_mono _ fun rho => completed_search_cached_event secret rho message fuel hlimit cache mark
    _ = 1/(2 : ENNReal)^59+(cachedNonces message fuel cache mark).card/(2 : ENNReal)^128 := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,probEvent_uniformSample]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedNonces]
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right (cachedNonces_card_le_count message fuel cache mark) _)
theorem uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 :=
  (uniform_nonce_completed_point secret message fuel hlimit cache mark).trans
    (NativeCache.clean_point_bound_arithmetic cache hfinite q hsize hq hclean mark)
end SigGolfResearch.Gate6.NativeSearch
end
section
namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def completeLabel (found : Option (BitVec 32 × HashOutput)) : ProbComp MarkedLabel :=
  found.elim ($ᵗ MarkedLabel) (fun value => pure (digestRecord value.2).1)
noncomputable def complete {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : ProbComp (Record × MarkedLabel) := do
  let record ← program
  let label ← completeLabel (observed record)
  pure (record,label)
theorem complete_erasure {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : 𝒮[Prod.fst <$> complete observed program]=𝒮[program] := by
  unfold complete
  simp only [map_bind,map_pure]
  trans 𝒮[program >>= fun record => pure record]
  · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro record
    exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  · simp
theorem completeLabel_point (found : Option (BitVec 32 × HashOutput)) (mark : MarkedLabel) :
    Pr[=mark | completeLabel found]=completedScore mark found := by
  cases found with
  | none => norm_num [completeLabel,completedScore,probOutput_uniformSample,markedLabel_card]
  | some value => simp only [completeLabel,completedScore,Option.elim_some,probOutput_pure,hit,eq_comm]
theorem complete_point {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) (mark : MarkedLabel) :
    Pr[fun result => result.2=mark | complete observed program]=
      expectedValue program (fun record => completedScore mark (observed record)) := by
  rw [complete,probEvent_bind_eq_expectedValue]
  congr 1
  funext record
  rw [probEvent_bind_eq_expectedValue]
  simp only [probEvent_pure]
  rw [expectedValue_ite_one]
  rw [probEvent_eq_eq_probOutput]
  exact completeLabel_point (observed record) mark
noncomputable def recordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (search rho message fuel) cache))
theorem recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (1024/1025 : ENNReal)*((recordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  have hpoint := uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
  rw [← complete_point Prod.fst _ mark] at hpoint
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat]
  change (1024/1025 : ENNReal)*Pr[fun result => result.2=mark | complete Prod.fst
    (($ᵗ Digest : ProbComp Digest) >>= fun rho => roRun secret (search rho message fuel) cache)]≤_
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SigGolfResearch.Gate6.NativeSearch
end
section
namespace SigGolfResearch.Gate6.Source
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem actual_decoder_eq (output : HashOutput) :
    NativeSearch.decode output=SigGolfCandidate.T3.Sampling.digestDecode output := by
  unfold NativeSearch.decode SigGolfCandidate.T3.Sampling.digestDecode
  by_cases h : digestAdmissible output=true
  · simp [h,(actual_predicate_iff output).mp h]
  · have hn : ¬DigestAccepted output := fun hg => h ((actual_predicate_iff output).mpr hg)
    simp [h,hn]
theorem actual_search_eq (rho : Digest) (message : Message) (fuel : Nat) :
    NativeSearch.search rho message fuel=digestSearch rho message 0 fuel := by
  rw [digestSearch_public]
  unfold NativeSearch.search
  have he : NativeSearch.decode=SigGolfCandidate.T3.Sampling.digestDecode := funext actual_decoder_eq
  rw [he]
theorem actual_uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => NativeSearch.completedScore mark result.1) ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  simpa only [actual_search_eq] using
    NativeSearch.uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
noncomputable def actualRecordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (NativeSearch.complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (digestSearch rho message 0 fuel) cache))
theorem actual_recordLaw_eq (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    actualRecordLaw secret message fuel cache=NativeSearch.recordLaw secret message fuel cache := by
  simp only [actualRecordLaw,NativeSearch.recordLaw,actual_search_eq]
theorem actual_recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (1024/1025 : ENNReal)*((actualRecordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  rw [actual_recordLaw_eq]
  exact NativeSearch.recordLaw_scaled_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
end SigGolfResearch.Gate6.Source
end
end
-- ==== merged from T3_Gate6_Sampling ====
section

namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable def acceptedWeight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) : ENNReal :=
  expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => (decoder answer).elim 0 payoff)
noncomputable def geometricWeight (failure accepted : ENNReal) : Nat → ENNReal
  | 0 => 0
  | n+1 => accepted+failure*geometricWeight failure accepted n
theorem uniform_decoder_weight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) (rejected : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => (decoder answer).elim rejected payoff)=
      acceptedWeight decoder payoff+failMass decoder*rejected := by
  classical
  have hp (answer : HashOutput) :
      (decoder answer).elim rejected payoff=(decoder answer).elim 0 payoff+
        (if decoder answer=none then 1 else 0)*rejected := by
    cases decoder answer <;> simp
  simp_rw [hp]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_ite_one]
  have hf : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent decoder
  rw [← hf]
  rfl
theorem expected_publicSearch {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      (∀ c,counter ≤ c → c < bound → cache (inputs c)=none) →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff)=
      geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _
      simp [searchLoop,publicProgram,geometricWeight]
  | succ fuel ih =>
      intro counter hlimit cache hfresh
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind,
        expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      have hbranch (answer : HashOutput) :
          expectedValue
            (roRun secret (match decoder answer with
              | none => publicProgram (searchLoop inputs decoder
                  (fun c v => pure (result c v)) fuel (counter+1))
              | some value => pure (some (result counter value)))
              (cache.cacheQuery (inputs counter) answer))
            (fun output => output.1.elim 0 payoff)=
          (decoder answer).elim
            (geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel) weight := by
        cases hd : decoder answer with
        | some value => simp [hweight]
        | none =>
            apply ih (counter+1) (by omega) _
            intro c hstart hc
            rw [QueryCache.cacheQuery_of_ne]
            · exact hfresh c (by omega) hc
            · intro he
              have hh := hinj c counter hc (by omega) he
              omega
      calc
        _ = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer =>
            (decoder answer).elim
              (geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel) weight) := by
          congr 1
          funext answer
          exact hbranch answer
        _ = _ := uniform_decoder_weight decoder weight _
theorem geometricWeight_mul (failure accepted factor : ENNReal) (fuel : Nat) :
    geometricWeight failure (factor*accepted) fuel=
      factor*geometricWeight failure accepted fuel := by
  induction fuel with
  | zero => simp [geometricWeight]
  | succ fuel ih => simp only [geometricWeight,ih];ring
theorem digest_acceptedWeight (payoff : IndexBuckets → ENNReal) :
    acceptedWeight digestDecode (fun output => payoff (samplingData output).1)=
      finiteAverage payoff*acceptanceProbability := by
  unfold acceptedWeight
  calc
    _ = expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun output => if digestAdmissible output then payoff (samplingData output).1 else 0) := by
      congr 1
      funext output
      unfold digestDecode
      split <;> rfl
    _ = _ := accepted_samplingData payoff
theorem digestSearch_label_weight (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1))=
      finiteAverage payoff*geometricWeight (failMass digestDecode) acceptanceProbability fuel := by
  rw [digestSearch_public]
  rw [expected_publicSearch secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => payoff (samplingData found.2).1)
    (fun output => payoff (samplingData output).1) (fun _ _ => rfl) (2^32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh]
  rw [digest_acceptedWeight,geometricWeight_mul]
theorem digest_acceptanceProbability :
    Pr[fun output : HashOutput => digestAdmissible output=true |
      ($ᵗ HashOutput : ProbComp HashOutput)]=acceptanceProbability := by
  rw [← expectedValue_ite_one]
  have h := accepted_samplingData (fun _ => (1 : ENNReal))
  rw [BPORS.History.finiteAverage_constant,one_mul] at h
  exact h
theorem digest_acceptanceProbability_le_one : acceptanceProbability ≤ 1 := by
  rw [← digest_acceptanceProbability]
  exact probEvent_le_one
theorem digest_failMass : failMass digestDecode=1-acceptanceProbability := by
  have hf : failMass digestDecode=Pr[fun answer : HashOutput => digestDecode answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent digestDecode
  rw [hf]
  have he (answer : HashOutput) : digestDecode answer=none ↔ ¬digestAdmissible answer=true := by
    by_cases h : digestAdmissible answer=true
    · simp only [digestDecode,h,ite_true,reduceCtorEq,not_true_eq_false]
    · simp only [digestDecode,h,Bool.false_eq_true,ite_false,not_false_eq_true]
  simp_rw [he]
  rw [probEvent_not,digest_acceptanceProbability]
theorem geometricWeight_le_one (failure accepted : ENNReal) (hmass : accepted+failure ≤ 1)
    (fuel : Nat) : geometricWeight failure accepted fuel ≤ 1 := by
  induction fuel with
  | zero => exact bot_le
  | succ fuel ih =>
      exact (add_le_add le_rfl (mul_le_of_le_one_right' ih)).trans hmass
theorem digestSearch_label_weight_le (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) ≤
      finiteAverage payoff := by
  rw [digestSearch_label_weight secret rho message fuel counter hlimit cache hfresh payoff]
  apply mul_le_of_le_one_right'
  apply geometricWeight_le_one
  rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one]
theorem digestSearch_label_probability_le (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message counter fuel) cache] ≤
      targets.card/(2 : ENNReal)^59 := by
  classical
  have h := digestSearch_label_weight_le secret rho message fuel counter hlimit cache hfresh
    (fun label => if label ∈ targets then 1 else 0)
  have hs (result : Option (BitVec 32 × HashOutput) × RCache) :
      result.1.elim 0 (fun found => if (samplingData found.2).1 ∈ targets then (1 : ENNReal) else 0)=
      if ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets then 1 else 0 := by
    cases result.1 <;> simp
  simp_rw [hs] at h
  rw [expectedValue_ite_one] at h
  have hc : finiteAverage (fun label : IndexBuckets => if label ∈ targets then (1 : ENNReal) else 0)=
      targets.card/(2 : ENNReal)^59 := by
    rw [← expected_uniform_eq_finiteAverage,expectedValue_ite_one,probEvent_uniformSample]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    have hcard : Fintype.card IndexBuckets=2^59 := by
      norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
    rw [hcard]
    rw [Nat.cast_pow,Nat.cast_ofNat]
  rwa [hc] at h
def CachedTrialsReject {β : Type} (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer → decoder answer=none
theorem expected_publicSearch_le_of_cached_reject {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialsReject inputs decoder counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hd := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure,hd]
          exact ih (counter+1) (by omega) cache
            (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
theorem digestSearch_label_weight_le_of_cached_reject
    (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hcache : CachedTrialsReject (digestTrial rho message) digestDecode counter (2^32) cache)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) ≤
      finiteAverage payoff := by
  rw [digestSearch_public]
  apply expected_publicSearch_le_of_cached_reject secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => payoff (samplingData found.2).1)
    (fun output => payoff (samplingData output).1) (fun _ _ => rfl) (finiteAverage payoff) _ (2^32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hcache
  rw [digest_acceptedWeight]
  calc
    _ = finiteAverage payoff*(acceptanceProbability+failMass digestDecode) := by ring
    _ = finiteAverage payoff := by
      rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
    _ ≤ finiteAverage payoff := le_rfl
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
def CachedTrialScoresBound {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal) (price : ENNReal)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer →
    (decoder answer).elim 0 weight ≤ price
theorem expected_publicSearch_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
def CachedTarget (rho : Digest) (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) : Prop :=
  ∃ c,c < fuel ∧ ∃ answer,cache (digestTrial rho message c)=some answer ∧
    digestAdmissible answer=true ∧ (samplingData answer).1 ∈ targets
noncomputable def targetWeight (targets : Finset IndexBuckets) (label : IndexBuckets) : ENNReal :=
  if label ∈ targets then 1 else 0
theorem targetWeight_average (targets : Finset IndexBuckets) :
    finiteAverage (targetWeight targets)=targets.card/(2 : ENNReal)^59 := by
  classical
  unfold targetWeight
  rw [← expected_uniform_eq_finiteAverage,expectedValue_ite_one,probEvent_uniformSample]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hcard : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
theorem targetWeight_probability (targets : Finset IndexBuckets)
    (program : ProbComp (Option (BitVec 32 × HashOutput) × RCache)) :
    expectedValue program (fun result => result.1.elim 0
      (fun found => targetWeight targets (samplingData found.2).1))=
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets | program] := by
  classical
  have he (result : Option (BitVec 32 × HashOutput) × RCache) :
      result.1.elim 0 (fun found => targetWeight targets (samplingData found.2).1)=
      if ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets then 1 else 0 := by
    cases result.1 <;> simp [targetWeight]
  simp_rw [he]
  rw [expectedValue_ite_one]
theorem digestSearch_target_le_of_no_cached_hit (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) (hno : ¬CachedTarget rho message fuel cache targets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message 0 fuel) cache] ≤ targets.card/(2 : ENNReal)^59 := by
  classical
  rw [← targetWeight_probability,← targetWeight_average,digestSearch_public]
  apply expected_publicSearch_le_of_cached_scores secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => targetWeight targets (samplingData found.2).1)
    (fun output => targetWeight targets (samplingData output).1) (fun _ _ => rfl)
    (finiteAverage (targetWeight targets)) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf answer ha
    by_cases hadm : digestAdmissible answer=true
    · have hnot : (samplingData answer).1 ∉ targets :=
        fun ht => hno ⟨c,hf,answer,ha,hadm,ht⟩
      simp only [digestDecode,hadm,ite_true,Option.elim_some,targetWeight,hnot,ite_false]
      exact bot_le
    · simp only [digestDecode,hadm,Bool.false_eq_true,ite_false,Option.elim_none]
      exact bot_le
  · rw [digest_acceptedWeight]
    calc
      _ = finiteAverage (targetWeight targets)*(acceptanceProbability+failMass digestDecode) := by ring
      _ = finiteAverage (targetWeight targets) := by
        rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
      _ ≤ finiteAverage (targetWeight targets) := le_rfl
theorem digestSearch_target_le_cached_event (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message 0 fuel) cache] ≤
      targets.card/(2 : ENNReal)^59 + if CachedTarget rho message fuel cache targets then 1 else 0 := by
  classical
  by_cases h : CachedTarget rho message fuel cache targets
  · rw [if_pos h]
    exact probEvent_le_one.trans (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact digestSearch_target_le_of_no_cached_hit secret rho message fuel hlimit cache targets h
noncomputable def cachedTargetNonces (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) : Finset Digest := by
  classical
  exact Finset.univ.filter fun rho => CachedTarget rho message fuel cache targets
theorem uniform_nonce_target_bound (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      targets.card/(2 : ENNReal)^59+
        (cachedTargetNonces message fuel cache targets).card/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_bind_eq_expectedValue]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        targets.card/(2 : ENNReal)^59+if CachedTarget rho message fuel cache targets then 1 else 0) :=
      expectedValue_mono _ fun rho => digestSearch_target_le_cached_event secret rho message fuel hlimit cache targets
    _ = _ := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,probEvent_uniformSample]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedTargetNonces]
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity (Finite positiveScoreMoment positiveScoreMoment_ne_top)
open SphincsSecurity.Concrete (bernoulliExcess_secondMoment_ennreal enncard_cacheQuery_of_fresh)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch Finset.univ
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def AcceptedTarget (targets : Finset IndexBuckets) (answer : HashOutput) : Prop :=
  digestAdmissible answer=true ∧ (samplingData answer).1 ∈ targets
noncomputable def targetRate (targets : Finset IndexBuckets) : ENNReal :=
  targets.card/(2 : ENNReal)^59*acceptanceProbability
theorem acceptedTarget_probability (targets : Finset IndexBuckets) :
    Pr[AcceptedTarget targets | ($ᵗ HashOutput : ProbComp HashOutput)]=targetRate targets := by
  have h := accepted_samplingData (targetWeight targets)
  have hi (answer : HashOutput) :
      (if digestAdmissible answer then targetWeight targets (samplingData answer).1 else 0)=
      if AcceptedTarget targets answer then (1 : ENNReal) else 0 := by
    simp only [targetWeight,AcceptedTarget]
    split_ifs <;> simp_all
  simp_rw [hi] at h
  rw [expectedValue_ite_one,targetWeight_average] at h
  exact h
theorem targetRate_le_one (targets : Finset IndexBuckets) : targetRate targets ≤ 1 := by
  rw [← acceptedTarget_probability]
  exact probEvent_le_one
theorem digestTrial_nonce_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat}
    (he : digestTrial rho message counter=digestTrial rho' message' counter') : rho=rho' := by
  have h := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  exact (digestInput_injective h).1
noncomputable def cachedTargetEntry (targets : Finset IndexBuckets) (cache : RCache)
    (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if AcceptedTarget targets answer then 1 else 0)
noncomputable def cachedTargetCount (targets : Finset IndexBuckets) (cache : RCache) : ENNReal :=
  ∑' input,cachedTargetEntry targets cache input
theorem cachedTargetCount_empty (targets : Finset IndexBuckets) :
    cachedTargetCount targets ∅=0 := by
  simp [cachedTargetCount,cachedTargetEntry]
theorem cachedTargetCount_cacheQuery (targets : Finset IndexBuckets) (cache : RCache)
    (input : HashInput) (answer : HashOutput) (hfresh : cache input=none) :
    cachedTargetCount targets (cache.cacheQuery input answer)=cachedTargetCount targets cache+
      if AcceptedTarget targets answer then 1 else 0 := by
  unfold cachedTargetCount
  rw [ENNReal.tsum_eq_add_tsum_ite (f := cachedTargetEntry targets (cache.cacheQuery input answer)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := cachedTargetEntry targets cache) input]
  simp only [cachedTargetEntry,QueryCache.cacheQuery_self,hfresh,Option.elim_none,Option.elim_some,zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other=input
  · simp [heq]
  · simp only [heq,if_false,QueryCache.cacheQuery_of_ne cache answer heq]
theorem cachedTargetCount_le_enncard (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) : cachedTargetCount targets cache ≤ QueryCache.enncard cache := by
  unfold cachedTargetCount
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hn : cache input=none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp [cachedTargetEntry,hn])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset,(1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold cachedTargetEntry
      cases cache input <;> simp only [Option.elim_none,Option.elim_some]
      · exact bot_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem cachedTargetCount_ne_top (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) : cachedTargetCount targets cache ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedTargetCount_le_enncard targets cache hfinite)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem cachedTargetNonces_card_le_count (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) :
    ((cachedTargetNonces message fuel cache targets).card : ENNReal) ≤
      cachedTargetCount targets cache := by
  classical
  let nonces := cachedTargetNonces message fuel cache targets
  have hw : ∀ rho : nonces,∃ counter,counter < fuel ∧ ∃ answer,
      cache (digestTrial rho.val message counter)=some answer ∧ AcceptedTarget targets answer := by
    intro rho
    exact (Finset.mem_filter.mp rho.property).2
  choose counter hc answer ha htarget using hw
  let inputs (rho : nonces) := digestTrial rho.val message (counter rho)
  have hinj : Function.Injective inputs := by
    intro left right he
    exact Subtype.ext (digestTrial_nonce_injective he)
  have hentry (rho : nonces) : cachedTargetEntry targets cache (inputs rho)=1 := by
    simp only [cachedTargetEntry,inputs,ha,Option.elim_some,htarget,if_true]
  calc
    _ = ∑ rho : nonces,cachedTargetEntry targets cache (inputs rho) := by
      simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,nonces]
    _ ≤ ∑' input,cachedTargetEntry targets cache input := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comp_le_tsum_of_injective hinj (cachedTargetEntry targets cache))
    _ = _ := rfl
theorem uniform_nonce_target_bound_count (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets cache/(2 : ENNReal)^128 :=
  by
    have h := uniform_nonce_target_bound secret message fuel hlimit cache targets
    apply h.trans
    apply add_le_add le_rfl
    exact ENNReal.div_le_div_right (cachedTargetNonces_card_le_count message fuel cache targets) _
noncomputable def targetExcess (targets : Finset IndexBuckets) (cache : RCache) : ℝ :=
  (cachedTargetCount targets cache).toReal -
    (QueryCache.enncard cache).toReal*(targetRate targets).toReal
theorem targetExcess_cacheQuery (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input=none) :
    targetExcess targets (cache.cacheQuery input answer)=targetExcess targets cache+
      (if AcceptedTarget targets answer then 1 else 0)-(targetRate targets).toReal := by
  have hc := cachedTargetCount_ne_top targets cache hfinite
  have hn : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  unfold targetExcess
  rw [cachedTargetCount_cacheQuery targets cache input answer hfresh,
    enncard_cacheQuery_of_fresh cache input answer hfresh,
    ENNReal.toReal_add hn (by finiteness),ENNReal.toReal_one]
  split_ifs <;> simp only [add_zero,ENNReal.toReal_add hc (by finiteness),ENNReal.toReal_one] <;> ring
theorem expected_acceptedTarget_choice (targets : Finset IndexBuckets) (yes no : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if AcceptedTarget targets answer then yes else no)=
      targetRate targets*yes+(1-targetRate targets)*no := by
  have hnot : Pr[fun answer => ¬AcceptedTarget targets answer |
      ($ᵗ HashOutput : ProbComp HashOutput)]=1-targetRate targets := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (AcceptedTarget targets)
    rw [probFailure_of_liftM_PMF,tsub_zero,acceptedTarget_probability,add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hsplit (answer : HashOutput) :
      (if AcceptedTarget targets answer then yes else no)=
      (if AcceptedTarget targets answer then (1 : ENNReal) else 0)*yes+
        (if ¬AcceptedTarget targets answer then (1 : ENNReal) else 0)*no := by
    by_cases h : AcceptedTarget targets answer <;>
      simp only [h,if_true,if_false,not_true_eq_false,not_false_eq_true,one_mul,zero_mul,zero_add,add_zero]
  simp_rw [hsplit]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_mul_const,
    expectedValue_ite_one,expectedValue_ite_one,acceptedTarget_probability,hnot]
theorem expected_targetExcess_second_le (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => positiveScoreMoment (targetExcess targets (cache.cacheQuery input answer)) 2) ≤
      positiveScoreMoment (targetExcess targets cache) 2+targetRate targets := by
  simp_rw [targetExcess_cacheQuery targets cache hfinite input _ hfresh]
  have hchoice (answer : HashOutput) :
      positiveScoreMoment (targetExcess targets cache+
        (if AcceptedTarget targets answer then 1 else 0)-(targetRate targets).toReal) 2=
      if AcceptedTarget targets answer then
        positiveScoreMoment (targetExcess targets cache+(1-(targetRate targets).toReal)) 2
      else positiveScoreMoment (targetExcess targets cache+(-(targetRate targets).toReal)) 2 := by
    split_ifs <;> congr 1 <;> ring
  simp_rw [hchoice]
  rw [expected_acceptedTarget_choice]
  exact bernoulliExcess_secondMoment_ennreal _ _ (targetRate_le_one targets)
theorem singleton_targetRate_sum :
    (∑ point : IndexBuckets,targetRate {point})=acceptanceProbability := by
  simp only [targetRate,Finset.card_singleton,Nat.cast_one,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  have hc : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [hc,Nat.cast_pow,Nat.cast_ofNat,← mul_assoc]
  rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by finiteness),one_mul]
noncomputable def allTargetMoment (cache : RCache) : ENNReal :=
  ∑ point : IndexBuckets,positiveScoreMoment (targetExcess {point} cache) 2
attribute [local irreducible] allTargetMoment cachedTargetCount targetExcess targetRate acceptanceProbability
theorem allTargetMoment_empty : allTargetMoment ∅=0 := by
  simp [allTargetMoment,targetExcess,cachedTargetCount_empty,positiveScoreMoment]
theorem expected_allTargetMoment_fresh (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => allTargetMoment (cache.cacheQuery input answer)) ≤
      allTargetMoment cache+acceptanceProbability := by
  calc
    _ = ∑ point : IndexBuckets,expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun answer => positiveScoreMoment (targetExcess {point} (cache.cacheQuery input answer)) 2) := by
      unfold allTargetMoment
      exact expectedValue_finsetSum _ _ _
    _ ≤ ∑ point : IndexBuckets,(positiveScoreMoment (targetExcess {point} cache) 2+targetRate {point}) :=
      Finset.sum_le_sum (fun point _ => expected_targetExcess_second_le {point} cache hfinite input hfresh)
    _ = _ := by
      rw [Finset.sum_add_distrib,singleton_targetRate_sum]
      unfold allTargetMoment
      rfl
private theorem constant_hashQueryCharge (rate : ENNReal) (query : SphincsSecurity.OracleWorld.Domain)
    (cache : RCache) :
    SphincsSecurity.hashQueryCharge (fun _ _ => rate) cache query=
      (if query matches .inr _ then rate else 0) := by
  cases query <;> rfl
theorem expected_allTargetMoment_step (query : SphincsSecurity.OracleWorld.Domain)
    (cache : RCache) (hfinite : Finite cache) :
    (∑' result,Pr[= result | (SphincsSecurity.romImpl query).run cache]*allTargetMoment result.2) ≤
      allTargetMoment cache+(if query matches .inr _ then acceptanceProbability else 0) := by
  have h := SphincsSecurity.expected_potential_romImpl_le_charge allTargetMoment
    (fun _ _ => acceptanceProbability) (fun current hc input hf =>
      expected_allTargetMoment_fresh current hc input hf) query cache hfinite
  rw [constant_hashQueryCharge] at h
  exact h
theorem cachedTargetCount_singleton_native (cache : RCache) (point : IndexBuckets) :
    cachedTargetCount {point} cache=SigGolfResearch.Gate6.NativeCache.count point cache := by
  unfold cachedTargetCount SigGolfResearch.Gate6.NativeCache.count
  apply tsum_congr
  intro input
  unfold cachedTargetEntry SigGolfResearch.Gate6.NativeCache.entry
  cases cache input with
  | none => rfl
  | some output =>
      change (if AcceptedTarget {point} output then (1 : ENNReal) else 0)=
        if SigGolfResearch.Gate6.Cache.Matches point output then 1 else 0
      have he : AcceptedTarget {point} output ↔ SigGolfResearch.Gate6.Cache.Matches point output := by
        simp only [AcceptedTarget,Finset.mem_singleton,SigGolfResearch.Gate6.Cache.Matches,
          samplingData_mark,SigGolfResearch.Gate6.Source.actual_predicate_iff]
      by_cases hh : AcceptedTarget {point} output
      · rw [if_pos hh,if_pos (he.mp hh)]
      · rw [if_neg hh,if_neg (fun hn => hh (he.mpr hn))]
theorem singleton_targetRate_native (point : IndexBuckets) :
    targetRate {point}=SigGolfResearch.Gate6.Cache.eRate := by
  simp only [targetRate,Finset.card_singleton,Nat.cast_one,acceptanceProbability,
    SigGolfResearch.Gate6.Cache.eRate,div_eq_mul_inv]
  ring
def TargetCacheExceptional (cache : RCache) : Prop :=
  ∃ point : IndexBuckets,(2^47 : ℝ) < targetExcess {point} cache
theorem targetCacheExceptional_iff_native (cache : RCache) :
    TargetCacheExceptional cache ↔ SigGolfResearch.Gate6.NativeCache.Bad cache := by
  unfold TargetCacheExceptional SigGolfResearch.Gate6.NativeCache.Bad
  apply exists_congr
  intro point
  rw [targetExcess,cachedTargetCount_singleton_native,singleton_targetRate_native]
  change (2^47 : ℝ)<(SigGolfResearch.Gate6.NativeCache.count point cache).toReal-
    (QueryCache.enncard cache).toReal*SigGolfResearch.Gate6.Cache.rate ↔ _
  constructor <;> intro h <;> linarith
theorem targetCacheExceptional_moment (cache : RCache) (hbad : TargetCacheExceptional cache) :
    (2^94 : ENNReal) ≤ allTargetMoment cache := by
  obtain ⟨point,hpoint⟩ := hbad
  have hpower : (2^94 : ℝ) ≤ max (targetExcess {point} cache) 0^2 := by
    calc
      _ = (2^47 : ℝ)^2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hpoint.le.trans (le_max_left _ _)) 2
  have hreal := ENNReal.ofReal_le_ofReal hpower
  rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_ofNat] at hreal
  unfold allTargetMoment
  apply hreal.trans
  exact (Finset.single_le_sum (s := Finset.univ)
    (f := fun point => positiveScoreMoment (targetExcess {point} cache) 2)
    (fun _ _ => bot_le) (Finset.mem_univ point))
theorem adaptive_targetCache_exception {Result : Type}
    (program : OracleComp SphincsSecurity.OracleWorld Result) (budget : Nat) :
    Pr[fun result => result.1.2 ≤ budget ∧ TargetCacheExceptional result.2 |
      (simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅] ≤
      acceptanceProbability*budget/(2 : ENNReal)^94 := by
  have h := SphincsSecurity.expected_truncatedPotential_le allTargetMoment acceptanceProbability
    expected_allTargetMoment_step program ∅ SphincsSecurity.finite_empty budget
  rw [allTargetMoment_empty,zero_add] at h
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by finiteness))]
  calc
    _ = expectedValue
        ((simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅)
        (fun result => if result.1.2 ≤ budget ∧ TargetCacheExceptional result.2 then (2 : ENNReal)^94 else 0) := by
      rw [← expectedValue_ite_one,← expectedValue_mul_const]
      congr 1
      funext result
      split_ifs <;> simp
    _ ≤ expectedValue
        ((simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅)
        (fun result => SphincsSecurity.truncatedPotential allTargetMoment acceptanceProbability
          budget result.1.2 result.2) := by
      apply expectedValue_mono
      intro result
      by_cases hb : result.1.2 ≤ budget ∧ TargetCacheExceptional result.2
      · rw [if_pos hb,SphincsSecurity.truncatedPotential,if_pos hb.1]
        exact (targetCacheExceptional_moment result.2 hb.2).trans le_self_add
      · rw [if_neg hb]
        exact bot_le
    _ ≤ _ := h
theorem targetCount_bound_of_no_exception (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget)
    (hclean : ¬TargetCacheExceptional cache) (point : IndexBuckets) :
    cachedTargetCount {point} cache ≤ (budget : ENNReal)*targetRate {point}+(2 : ENNReal)^47 := by
  have hc := cachedTargetCount_ne_top {point} cache hfinite
  have hn : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hr : targetRate {point} ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (targetRate_le_one {point})
  apply (ENNReal.toReal_le_toReal hc (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul]
  have hcache := ENNReal.toReal_mono (by finiteness) hsize
  have hex : targetExcess {point} cache ≤ (2^47 : ℝ) :=
    le_of_not_gt (fun h => hclean ⟨point,h⟩)
  have hscale := mul_le_mul_of_nonneg_right hcache (ENNReal.toReal_nonneg (a := targetRate {point}))
  simp only [targetExcess] at hex
  norm_num at hcache hscale ⊢
  linarith
theorem uniform_nonce_point_bound_clean (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget)
    (hclean : ¬TargetCacheExceptional cache) (point : IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1=point |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      1/(2 : ENNReal)^59+
        ((budget : ENNReal)*targetRate {point}+(2 : ENNReal)^47)/(2 : ENNReal)^128 := by
  have h := uniform_nonce_target_bound_count secret message fuel hlimit cache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  apply h.trans
  apply add_le_add le_rfl
  exact ENNReal.div_le_div_right (targetCount_bound_of_no_exception cache hfinite budget hsize hclean point) _
theorem uniform_nonce_point_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional cache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1=point |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have h := uniform_nonce_target_bound_count secret message fuel hlimit cache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  apply h.trans
  rw [cachedTargetCount_singleton_native]
  exact SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic cache hfinite budget hsize hbudget
    (fun h => hclean ((targetCacheExceptional_iff_native cache).mpr h)) point
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
open SphincsSecurity (Finite)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch Finset.univ BPORS.finiteAverage DigestSampling.samplingData
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expected_publicSearch_completed_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim price payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
noncomputable def completedTargetScore (targets : Finset IndexBuckets)
    (found : Option (BitVec 32 × HashOutput)) : ENNReal :=
  found.elim (finiteAverage (targetWeight targets))
    (fun value => targetWeight targets (samplingData value.2).1)
theorem targetWeight_average_le_one (targets : Finset IndexBuckets) :
    finiteAverage (targetWeight targets) ≤ 1 := by
  rw [← expected_uniform_eq_finiteAverage]
  apply expectedValue_le_of_le
  intro label
  unfold targetWeight
  split_ifs <;> norm_num
private theorem option_weight_le_one {Value : Type} (found : Option Value)
    (fallback : ENNReal) (weight : Value → ENNReal)
    (hmiss : fallback ≤ 1) (hvalue : ∀ value,weight value ≤ 1) :
    found.elim fallback weight ≤ 1 := by
  cases found with
  | none => exact hmiss
  | some value => exact hvalue value
theorem completedTargetScore_le_one (targets : Finset IndexBuckets)
    (found : Option (BitVec 32 × HashOutput)) : completedTargetScore targets found ≤ 1 := by
  apply option_weight_le_one found _ _ (targetWeight_average_le_one targets)
  intro value
  unfold targetWeight
  split_ifs <;> norm_num
theorem completed_search_target_le_of_no_cached_hit (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) (hno : ¬CachedTarget rho message fuel cache targets) :
    expectedValue (roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤ finiteAverage (targetWeight targets) := by
  rw [digestSearch_public]
  apply expected_publicSearch_completed_le_of_cached_scores secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => targetWeight targets (samplingData found.2).1)
    (fun output => targetWeight targets (samplingData output).1) (fun _ _ => rfl)
    (finiteAverage (targetWeight targets)) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf answer ha
    by_cases hadm : digestAdmissible answer=true
    · have hnot : (samplingData answer).1 ∉ targets :=
        fun ht => hno ⟨c,hf,answer,ha,hadm,ht⟩
      simp only [digestDecode,hadm,ite_true,Option.elim_some,targetWeight,hnot,ite_false]
      exact bot_le
    · simp only [digestDecode,hadm,Bool.false_eq_true,ite_false,Option.elim_none]
      exact bot_le
  · rw [digest_acceptedWeight]
    calc
      _ = finiteAverage (targetWeight targets)*(acceptanceProbability+failMass digestDecode) := by ring
      _ = finiteAverage (targetWeight targets) := by
        rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
      _ ≤ _ := le_rfl
theorem completed_search_target_le_cached_event (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) :
    expectedValue (roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤
      finiteAverage (targetWeight targets)+if CachedTarget rho message fuel cache targets then 1 else 0 := by
  by_cases h : CachedTarget rho message fuel cache targets
  · rw [if_pos h]
    exact (expectedValue_le_of_le _ (fun _ => completedTargetScore_le_one targets _)).trans
      (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact completed_search_target_le_of_no_cached_hit secret rho message fuel hlimit cache targets h
theorem uniform_nonce_completed_target_bound (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets cache/(2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        finiteAverage (targetWeight targets)+if CachedTarget rho message fuel cache targets then 1 else 0) :=
      expectedValue_mono _ fun rho => completed_search_target_le_cached_event secret rho message fuel hlimit cache targets
    _ = targets.card/(2 : ENNReal)^59+
        (cachedTargetNonces message fuel cache targets).card/(2 : ENNReal)^128 := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,
        probEvent_uniformSample,targetWeight_average]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedTargetNonces]
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right
      (cachedTargetNonces_card_le_count message fuel cache targets) _)
noncomputable def completeLabel (observed : Option HashOutput) : ProbComp IndexBuckets :=
  observed.elim ($ᵗ IndexBuckets) (fun output => pure (samplingData output).1)
private theorem expectedValue_option {Value Label : Type} (observed : Option Value)
    (fallback : ProbComp Label) (next : Value → ProbComp Label) (payoff : Label → ENNReal) :
    expectedValue (observed.elim fallback next) payoff=
      observed.elim (expectedValue fallback payoff) (fun value => expectedValue (next value) payoff) := by
  cases observed <;> rfl
theorem completeLabel_expected (observed : Option HashOutput) (payoff : IndexBuckets → ENNReal) :
    expectedValue (completeLabel observed) payoff=
      observed.elim (finiteAverage payoff) (fun output => payoff (samplingData output).1) := by
  rw [completeLabel,expectedValue_option,expected_uniform_eq_finiteAverage]
  simp only [expectedValue_pure]
noncomputable def completeRecord {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) : ProbComp (Record × IndexBuckets) := do
  let record ← program
  let label ← completeLabel (observed record)
  pure (record,label)
theorem completeRecord_erasure {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) :
    𝒮[Prod.fst <$> completeRecord observed program]=𝒮[program] := by
  unfold completeRecord
  simp only [map_bind,map_pure]
  trans 𝒮[program >>= fun record => pure record]
  · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro record
    exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  · simp
theorem completeRecord_expected {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) (payoff : IndexBuckets → ENNReal) :
    expectedValue (completeRecord observed program) (fun result => payoff result.2)=
      expectedValue program (fun record =>
        (observed record).elim (finiteAverage payoff) (fun output => payoff (samplingData output).1)) := by
  rw [completeRecord,expectedValue_bind]
  apply congrArg
  funext record
  rw [expectedValue_bind]
  simp only [expectedValue_pure]
  exact completeLabel_expected _ payoff
theorem clean_point_bound_arithmetic (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional cache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    1/(2 : ENNReal)^59+cachedTargetCount {point} cache/(2 : ENNReal)^128 ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  rw [cachedTargetCount_singleton_native]
  exact SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic cache hfinite budget hsize hbudget
    (fun h => hclean ((targetCacheExceptional_iff_native cache).mpr h)) point
end SigGolfCandidate.T3.Sampling
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FiniteGraphSampling ====
section

namespace SphincsSecurity.Concrete.FiniteGraphSampling
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
variable {Node Cell Answer State : Type} [DecidableEq Cell]
def read (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (table : Cell → Answer) : List Node → State → State
  | [], state => state
  | node :: nodes, state => read input advance table nodes (advance node (table (input node state)) state)
def Separated (input : Node → State → Cell) : Prop :=
  ∀ left right, left ≠ right → ∀ before after, input left before ≠ input right after
omit [DecidableEq Cell] in
theorem read_congr (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (left right : Cell → Answer) (hagrees : ∀ node state, left (input node state) = right (input node state))
    (nodes : List Node) (state : State) : read input advance left nodes state = read input advance right nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      simp only [read, hagrees]
      exact ih _
theorem read_update_of_not_mem (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (table : Cell → Answer) (nodes : List Node) (node : Node) (hnode : node ∉ nodes)
    (before state : State) (answer : Answer) :
    read input advance (Function.update table (input node before) answer) nodes state =
      read input advance table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have hne : first ≠ node := fun h => hnode (by simp [h])
      have hrest : node ∉ rest := fun h => hnode (List.mem_cons_of_mem _ h)
      simp only [read, Function.update_of_ne (hsep first node hne state before)]
      exact ih hrest _
variable [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Cell → Answer)]
noncomputable def plant (input : Node → State → Cell)
    (advance : Node → Answer → State → State) : List Node → State → ProbComp (State × (Cell → Answer))
  | [], state => do
      let table ← $ᵗ (Cell → Answer)
      pure (state, table)
  | node :: nodes, state => do
      let answer ← $ᵗ Answer
      let result ← plant input advance nodes (advance node answer state)
      pure (result.1, Function.update result.2 (input node state) answer)
theorem evalDist_table_extract {Result : Type} (cell : Cell)
    (next : (Cell → Answer) → Answer → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)] =
      𝒮[do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer] := by
  have h := congrArg (fun distribution : SPMF (Cell → Answer) =>
    distribution >>= fun table => 𝒮[next table (table cell)])
    (evalSPMF_uniformSample_bind_update (R := Answer) cell)
  simpa only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind, Function.update_self] using h.symm
theorem evalDist_read_eq_plant (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (nodes : List Node) (hnodes : nodes.Nodup) (state : State) :
    𝒮[do
      let table ← ($ᵗ (Cell → Answer) : ProbComp _)
      pure (read input advance table nodes state, table)] =
      𝒮[plant input advance nodes state] := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      obtain ⟨hnode, hnodes⟩ := List.nodup_cons.mp hnodes
      simp only [read]
      rw [evalDist_table_extract (input node state)
        (fun table answer => pure (read input advance table nodes (advance node answer state), table))]
      simp_rw [read_update_of_not_mem input advance hsep _ nodes node hnode]
      change 𝒮[do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (read input advance table nodes (advance node answer state),
          Function.update table (input node state) answer)] = _
      simp only [plant]
      apply evalSPMF_bind_congr_left
      intro answer
      have h := congrArg (fun distribution : SPMF (State × (Cell → Answer)) =>
        distribution >>= fun result => pure (result.1, Function.update result.2 (input node state) answer))
        (ih hnodes (advance node answer state))
      simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
end SphincsSecurity.Concrete.FiniteGraphSampling
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FiniteGraphReplay ====
section

namespace SphincsSecurity.Concrete.FiniteGraphSampling
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
variable {Node Cell Answer State : Type} [DecidableEq Node] [DecidableEq Cell]
def replay (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) : List Node → State → State × (Cell → Answer)
  | [], state => (state, table)
  | node :: nodes, state =>
      let result := replay input advance answers table nodes (advance node (answers node) state)
      (result.1, Function.update result.2 (input node state) (answers node))
omit [DecidableEq Node] in
theorem replay_congr (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (left right : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (hagrees : ∀ node ∈ nodes, left node = right node) (state : State) :
    replay input advance left table nodes state = replay input advance right table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      have hfirst := hagrees node List.mem_cons_self
      have hrest := ih (fun other hother => hagrees other (List.mem_cons_of_mem _ hother))
      simp only [replay, hfirst, hrest]
theorem replay_update_of_not_mem (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (node : Node) (hnode : node ∉ nodes) (answer : Answer) (state : State) :
    replay input advance (Function.update answers node answer) table nodes state =
      replay input advance answers table nodes state := by
  apply replay_congr
  intro other hother
  have hne : other ≠ node := by
    intro heq
    subst other
    exact hnode hother
  rw [Function.update_of_ne hne]
def patch (input : Node → Cell) (answers : Node → Answer) (table : Cell → Answer) : List Node → Cell → Answer
  | [] => table
  | node :: nodes => Function.update (patch input answers table nodes) (input node) (answers node)
omit [DecidableEq Node] in
theorem patch_of_forall_ne (input : Node → Cell) (answers : Node → Answer) (table : Cell → Answer)
    (nodes : List Node) (cell : Cell) (hne : ∀ node ∈ nodes, cell ≠ input node) :
    patch input answers table nodes cell = table cell := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      rw [patch, Function.update_of_ne (hne node List.mem_cons_self)]
      exact ih (fun other hother => hne other (List.mem_cons_of_mem _ hother))
theorem patch_at (input : Node → Cell) (hinjective : Function.Injective input)
    (answers : Node → Answer) (table : Cell → Answer) (nodes : List Node) (node : Node) (hnode : node ∈ nodes) :
    patch input answers table nodes (input node) = answers node := by
  induction nodes with
  | nil => cases hnode
  | cons first rest ih =>
      by_cases heq : node = first
      · subst node
        exact Function.update_self _ _ _
      · rw [patch, Function.update_of_ne (fun h => heq (hinjective h))]
        exact ih ((List.mem_cons.mp hnode).resolve_left heq)
variable [_root_.Finite Node] [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Node → Answer)] [SampleableType (Cell → Answer)]
omit [_root_.Finite Cell] in
theorem evalDist_plant_eq_replay (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (nodes : List Node) (hnodes : nodes.Nodup) (state : State) :
    𝒮[plant input advance nodes state] =
      𝒮[do
        let answers ← ($ᵗ (Node → Answer) : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (replay input advance answers table nodes state)] := by
  induction nodes generalizing state with
  | nil =>
      simp only [plant, replay]
      exact (evalSPMF_bind_const_neverFails _ (by simp) _).symm
  | cons node nodes ih =>
      obtain ⟨hnode, hnodes⟩ := List.nodup_cons.mp hnodes
      have hextract := evalDist_table_extract node (fun answers answer => do
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        let result := replay input advance answers table nodes (advance node answer state)
        pure (result.1, Function.update result.2 (input node state) answer))
      change 𝒮[plant input advance (node :: nodes) state] =
        𝒮[do
          let answers ← ($ᵗ (Node → Answer) : ProbComp _)
          let table ← ($ᵗ (Cell → Answer) : ProbComp _)
          let result := replay input advance answers table nodes (advance node (answers node) state)
          pure (result.1, Function.update result.2 (input node state) (answers node))]
      rw [hextract]
      simp_rw [replay_update_of_not_mem input advance _ _ nodes node hnode]
      simp only [plant]
      apply evalSPMF_bind_congr_left
      intro answer
      have h := congrArg (fun distribution : SPMF (State × (Cell → Answer)) =>
        distribution >>= fun result => pure (result.1, Function.update result.2 (input node state) answer))
        (ih hnodes (advance node answer state))
      simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h
end SphincsSecurity.Concrete.FiniteGraphSampling
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingProbability ====
section

namespace SphincsSecurity
open OracleComp ENNReal
open scoped BigOperators
set_option maxRecDepth 100000
theorem evalDist_truncateHash_uniform :
    𝒮[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ Digest : ProbComp Digest)] := by
  change 𝒮[(fun output : HashOutput => output.extractLsb' 0 digestBits) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)
theorem probEvent_uniform_truncateHash_eq (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [show (fun output : HashOutput => truncateHash output = target) =
      (fun output => output = target) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]
theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun digest => digest ∈ targets) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_uniformSample]
  rw [Finset.filter_univ_mem]
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableConditioning ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem uniformFinset_restrict_mass {α : Type} (source target : Finset α)
    (hs : source.Nonempty) (ht : target.Nonempty) (hsub : target ⊆ source) (value : α) :
    (if value ∈ target then PMF.uniformOfFinset source hs value else 0) =
      ((target.card : ENNReal) / source.card) * PMF.uniformOfFinset target ht value := by
  by_cases hv : value ∈ target
  · rw [if_pos hv, PMF.uniformOfFinset_apply_of_mem hs (hsub hv), PMF.uniformOfFinset_apply_of_mem ht hv]
    have ht0 : (target.card : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht.card_pos
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel ht0 (by finiteness), one_mul]
  · simp only [hv, if_false, PMF.uniformOfFinset_apply_of_notMem ht hv, mul_zero]
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
noncomputable def uniformTable (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty) :
    PMF (ι → α) := PMF.uniformOfFinset (Fintype.piFinset allowed) (Fintype.piFinset_nonempty.mpr hallowed)
theorem uniformTable_apply (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty)
    (table : ι → α) :
    uniformTable allowed hallowed table =
      if ∀ coordinate, table coordinate ∈ allowed coordinate then
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)⁻¹ else 0 := by
  simp only [uniformTable, PMF.uniformOfFinset_apply, Fintype.mem_piFinset, Fintype.card_piFinset]
theorem uniformTable_restrict (allowed reduced : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (hr : ∀ coordinate, (reduced coordinate).Nonempty)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (table : ι → α) :
    (if ∀ coordinate, table coordinate ∈ reduced coordinate then uniformTable allowed ha table else 0) =
      (((∏ coordinate, (reduced coordinate).card : Nat) : ENNReal) /
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)) * uniformTable reduced hr table := by
  simpa only [uniformTable, Fintype.mem_piFinset, Fintype.card_piFinset] using
    uniformFinset_restrict_mass (Fintype.piFinset allowed) (Fintype.piFinset reduced)
      (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hr)
      (Fintype.piFinset_subset reduced allowed hsub) table
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableRestriction ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
omit [DecidableEq α] in
theorem piFinset_update_card (allowed : ι → Finset α) (coordinate : ι) (values : Finset α) :
    (Fintype.piFinset (Function.update allowed coordinate values)).card =
      values.card * ∏ other ∈ Finset.univ.erase coordinate, (allowed other).card := by
  rw [Fintype.card_piFinset]
  have h : (fun other => (Function.update allowed coordinate values other).card) =
      Function.update (fun other => (allowed other).card) coordinate values.card := by
    funext other
    by_cases heq : other = coordinate <;> simp only [Function.update_apply, heq, if_true, if_false]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ coordinate), Finset.sdiff_singleton_eq_erase]
omit [DecidableEq α] in
theorem piFinset_update_card_ratio (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α) :
    ((Fintype.piFinset (Function.update allowed coordinate values)).card : ENNReal) /
        (Fintype.piFinset allowed).card = (values.card : ENNReal) / (allowed coordinate).card := by
  rw [piFinset_update_card, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ (fun other => (allowed other).card) (Finset.mem_univ coordinate)]
  have hrest : ((∏ other ∈ Finset.univ.erase coordinate, (allowed other).card : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun other _ => Nat.ne_of_gt (ha other).card_pos)
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [ENNReal.mul_div_mul_right _ _ hrest (by finiteness)]
theorem uniformTable_update_restrict (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α)
    (hv : values.Nonempty) (hsub : values ⊆ allowed coordinate) (table : ι → α) :
    (if table coordinate ∈ values then uniformTable allowed ha table else 0) =
      ((values.card : ENNReal) / (allowed coordinate).card) *
        uniformTable (Function.update allowed coordinate values)
          (by intro other; by_cases heq : other = coordinate
              · simpa only [heq, Function.update_self] using hv
              · simpa only [Function.update_of_ne heq] using ha other) table := by
  classical
  letI : DecidableEq (ι → α) := Classical.decEq _
  let reduced := Function.update allowed coordinate values
  have hred : ∀ other, (reduced other).Nonempty := by
    intro other
    by_cases heq : other = coordinate <;> simp only [reduced, Function.update_apply, heq, if_true, if_false]
    · exact hv
    · exact ha other
  have hsub' : Fintype.piFinset reduced ⊆ Fintype.piFinset allowed := by
    apply Fintype.piFinset_subset
    intro other
    by_cases heq : other = coordinate <;> simp only [reduced, Function.update_apply, heq, if_true, if_false]
    · simpa only [heq] using hsub
    · exact Finset.Subset.refl _
  have h := uniformFinset_restrict_mass (Fintype.piFinset allowed) (Fintype.piFinset reduced)
    (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hred) hsub' table
  rw [show (Fintype.piFinset reduced).card =
      (Fintype.piFinset (Function.update allowed coordinate values)).card from rfl,
    piFinset_update_card_ratio allowed ha coordinate values] at h
  change (if table ∈ Fintype.piFinset reduced then uniformTable allowed ha table else 0) =
    ((values.card : ENNReal) / (allowed coordinate).card) * uniformTable reduced hred table at h
  rw [← h]
  by_cases ht : ∀ other, table other ∈ allowed other
  · have heq : table ∈ Fintype.piFinset reduced ↔ table coordinate ∈ values := by
      rw [Fintype.piFinset_update_eq_filter_piFinset_mem allowed coordinate hsub, Finset.mem_filter,
        Fintype.mem_piFinset]
      exact and_iff_right ht
    simp only [heq]
  · have hz : uniformTable allowed ha table = 0 := by rw [uniformTable_apply, if_neg ht]
    simp only [hz, ite_self]
theorem probEvent_uniformTable_member (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α)
    (hv : values.Nonempty) (hsub : values ⊆ allowed coordinate) :
    Pr[fun table => table coordinate ∈ values | uniformTable allowed ha] =
      (values.card : ENNReal) / (allowed coordinate).card := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    uniformTable_update_restrict allowed ha coordinate values hv hsub, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
theorem probEvent_uniformTable_eq (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (candidate : α) :
    Pr[fun table => table coordinate = candidate | uniformTable allowed ha] =
      if candidate ∈ allowed coordinate then ((allowed coordinate).card : ENNReal)⁻¹ else 0 := by
  by_cases hc : candidate ∈ allowed coordinate
  · have h := probEvent_uniformTable_member allowed ha coordinate {candidate} (Finset.singleton_nonempty _)
      (Finset.singleton_subset_iff.mpr hc)
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_div, hc, if_true] using h
  · simp only [hc, if_false, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro table
    by_cases heq : table coordinate = candidate
    · have hn : ¬ ∀ other, table other ∈ allowed other := fun h => hc (heq ▸ h coordinate)
      simp only [heq, if_true, uniformTable_apply, hn, if_false]
    · simp only [heq, if_false]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Base_UniformTableCompletion ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
def eraseTableValue (allowed : ι → Finset α) (coordinate : ι) (candidate : α) : ι → Finset α :=
  Function.update allowed coordinate ((allowed coordinate).erase candidate)
def pairedMissAllowed (allowed : ι → Finset α) (child : ι) (candidate : α) (parent : ι) (answer : α) :
    ι → Finset α := eraseTableValue (eraseTableValue allowed child candidate) parent answer
omit [Fintype ι] in
theorem pairedMissAllowed_membership (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (table : ι → α) :
    (∀ coordinate, table coordinate ∈ pairedMissAllowed allowed child candidate parent answer coordinate) ↔
      (∀ coordinate, table coordinate ∈ allowed coordinate) ∧ table child ≠ candidate ∧ table parent ≠ answer := by
  constructor
  · intro h
    have hchild := h child
    have hparent := h parent
    simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self,
      Function.update_of_ne hne.symm, Finset.mem_erase] at hchild hparent
    refine ⟨?_, hchild.1, hparent.1⟩
    intro coordinate
    by_cases hp : coordinate = parent
    · simpa only [hp] using hparent.2
    by_cases hc : coordinate = child
    · simpa only [hc] using hchild.2
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using h coordinate
  · rintro ⟨h, hc, hp⟩ coordinate
    by_cases heqp : coordinate = parent
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm,
        Finset.mem_erase]
      exact ⟨hp, h parent⟩
    by_cases heqc : coordinate = child
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self, Finset.mem_erase]
      exact ⟨hc, h child⟩
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne heqp, Function.update_of_ne heqc] using h coordinate
omit [Fintype ι] in
theorem pairedMissAllowed_card_lower (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (coordinate : ι) :
    (allowed coordinate).card - 1 ≤ (pairedMissAllowed allowed child candidate parent answer coordinate).card := by
  by_cases hp : coordinate = parent
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm] using
      (Finset.pred_card_le_card_erase (s := allowed parent) (a := answer))
  by_cases hc : coordinate = child
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed child) (a := candidate))
  simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using
    Nat.sub_le (allowed coordinate).card 1
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
def discloseTableValue (allowed : ι → Finset α) (coordinate : ι) (value : α) : ι → Finset α :=
  Function.update allowed coordinate {value}
omit [Fintype ι] [DecidableEq α] in
theorem discloseTableValue_nonempty (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (value : α) :
    ∀ other, (discloseTableValue allowed coordinate value other).Nonempty := by
  intro other
  by_cases heq : other = coordinate
  · subst other
    simp only [discloseTableValue, Function.update_self, Finset.singleton_nonempty]
  · simpa only [discloseTableValue, Function.update_of_ne heq] using ha other
theorem uniformTable_disclose_mass (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (value : α) (labels : ι → α) :
    PMF.uniformOfFinset (allowed coordinate) (ha coordinate) value *
        uniformTable (discloseTableValue allowed coordinate value)
          (discloseTableValue_nonempty allowed ha coordinate value) labels =
      if labels coordinate = value then uniformTable allowed ha labels else 0 := by
  rw [PMF.uniformOfFinset_apply]
  by_cases hvalue : value ∈ allowed coordinate
  · rw [if_pos hvalue]
    have h := uniformTable_update_restrict allowed ha coordinate {value} (Finset.singleton_nonempty _)
      (Finset.singleton_subset_iff.mpr hvalue) labels
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_div, discloseTableValue] using h.symm
  · rw [if_neg hvalue, zero_mul]
    by_cases hlabels : labels coordinate = value
    · rw [if_pos hlabels, uniformTable_apply,
        if_neg (fun h => hvalue (hlabels ▸ h coordinate))]
    · rw [if_neg hlabels]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.UniformTableCompletion
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def complete (allowed : Coordinate → Finset Value) : SPMF (Coordinate → Value) :=
  if h : ∀ coordinate, (allowed coordinate).Nonempty then liftM (uniformTable allowed h) else failure
noncomputable def cell (allowed : Finset Value) : SPMF Value :=
  if h : allowed.Nonempty then liftM (PMF.uniformOfFinset allowed h) else failure
omit [DecidableEq Value] in
theorem complete_of_nonempty (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    complete allowed = liftM (uniformTable allowed ha) := by rw [complete, dif_pos ha]
omit [DecidableEq Value] in
theorem complete_of_empty (allowed : Coordinate → Finset Value)
    (ha : ¬∀ coordinate, (allowed coordinate).Nonempty) : complete allowed = failure := by
  rw [complete, dif_neg ha]
theorem complete_apply (allowed : Coordinate → Finset Value) (labels : Coordinate → Value) :
    complete allowed labels = if ∀ coordinate, labels coordinate ∈ allowed coordinate then
      ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)⁻¹ else 0 := by
  by_cases ha : ∀ coordinate, (allowed coordinate).Nonempty
  · rw [complete_of_nonempty allowed ha, SPMF.liftM_apply, uniformTable_apply]
  · rw [complete_of_empty allowed ha, SPMF.failure_apply,
      if_neg (fun h => ha (fun coordinate => ⟨labels coordinate, h coordinate⟩))]
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem cell_apply (allowed : Finset Value) (value : Value) :
    cell allowed value = if value ∈ allowed then (allowed.card : ENNReal)⁻¹ else 0 := by
  by_cases ha : allowed.Nonempty
  · rw [cell, dif_pos ha, SPMF.liftM_apply, PMF.uniformOfFinset_apply]
    split <;> simp_all
  · rw [cell, dif_neg ha, SPMF.failure_apply, if_neg (fun h => ha ⟨value, h⟩)]
noncomputable def restrictionWeight (allowed reduced : Coordinate → Finset Value) : ENNReal :=
  ((∏ coordinate, (reduced coordinate).card : Nat) : ENNReal) /
    ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)
omit [DecidableEq Coordinate] [DecidableEq Value] in
theorem weight_of_empty (allowed reduced : Coordinate → Finset Value)
    (hr : ¬∀ coordinate, (reduced coordinate).Nonempty) : restrictionWeight allowed reduced = 0 := by
  obtain ⟨coordinate, hcoordinate⟩ := not_forall.mp hr
  have hcard : (reduced coordinate).card = 0 := by
    simpa only [Finset.card_eq_zero] using Finset.not_nonempty_iff_eq_empty.mp hcoordinate
  have hprod : (∏ coordinate, (reduced coordinate).card : Nat) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ coordinate) hcard
  simp only [restrictionWeight, hprod, Nat.cast_zero, ENNReal.zero_div]
omit [DecidableEq Value] in
theorem weight_tsum_complete (allowed reduced : Coordinate → Finset Value) :
    restrictionWeight allowed reduced * (∑' labels, complete reduced labels) = restrictionWeight allowed reduced := by
  by_cases hr : ∀ coordinate, (reduced coordinate).Nonempty
  · simp only [complete_of_nonempty reduced hr, SPMF.liftM_apply, PMF.tsum_coe, mul_one]
  · simp only [weight_of_empty allowed reduced hr, zero_mul]
theorem restrict_mass (allowed reduced : Coordinate → Finset Value)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (labels : Coordinate → Value) :
    (if ∀ coordinate, labels coordinate ∈ reduced coordinate then complete allowed labels else 0) =
      restrictionWeight allowed reduced * complete reduced labels := by
  by_cases hr : ∀ coordinate, (reduced coordinate).Nonempty
  · have ha : ∀ coordinate, (allowed coordinate).Nonempty := fun coordinate => (hr coordinate).mono (hsub coordinate)
    rw [complete_of_nonempty allowed ha, complete_of_nonempty reduced hr]
    simpa only [SPMF.liftM_apply, restrictionWeight] using uniformTable_restrict allowed reduced ha hr hsub labels
  · rw [complete_of_empty reduced hr, SPMF.failure_apply, mul_zero,
      if_neg (fun h => hr (fun coordinate => ⟨labels coordinate, h coordinate⟩))]
theorem restrict_guard (allowed reduced : Coordinate → Finset Value)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (event : (Coordinate → Value) → Prop)
    (hguard : ∀ labels, (∀ coordinate, labels coordinate ∈ reduced coordinate) ↔
      (∀ coordinate, labels coordinate ∈ allowed coordinate) ∧ event labels) (labels : Coordinate → Value) :
    (if event labels then complete allowed labels else 0) =
      restrictionWeight allowed reduced * complete reduced labels := by
  rw [← restrict_mass allowed reduced hsub labels]
  by_cases ha : ∀ coordinate, labels coordinate ∈ allowed coordinate
  · simp only [hguard, ha, implies_true, true_and]
  · simp only [complete_apply, ha, if_false, ite_self]
omit [Fintype Coordinate] in
theorem paired_subset (allowed : Coordinate → Finset Value) (child parent : Coordinate)
    (candidate answer : Value) :
    ∀ coordinate, pairedMissAllowed allowed child candidate parent answer coordinate ⊆ allowed coordinate := by
  intro coordinate
  unfold pairedMissAllowed eraseTableValue
  by_cases hp : coordinate = parent
  · subst coordinate
    rw [Function.update_self]
    apply Finset.Subset.trans (Finset.erase_subset _ _)
    by_cases hc : parent = child
    · subst parent
      rw [Function.update_self]
      exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hc]
  · rw [Function.update_of_ne hp]
    by_cases hc : coordinate = child
    · subst coordinate
      rw [Function.update_self]
      exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hc]
theorem paired_mass (allowed : Coordinate → Finset Value) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate answer : Value) (labels : Coordinate → Value) :
    (if labels child ≠ candidate ∧ labels parent ≠ answer then complete allowed labels else 0) =
      restrictionWeight allowed (pairedMissAllowed allowed child candidate parent answer) *
        complete (pairedMissAllowed allowed child candidate parent answer) labels := by
  have h := restrict_guard allowed _ (paired_subset allowed child parent candidate answer) _
    (pairedMissAllowed_membership allowed child parent hne candidate answer) labels
  by_cases hevent : labels child ≠ candidate ∧ labels parent ≠ answer
  · simpa only [if_pos hevent] using h
  · simpa only [if_neg hevent] using h
theorem single_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (value : Value)
    (labels : Coordinate → Value) :
    (if labels coordinate ≠ value then complete allowed labels else 0) =
      restrictionWeight allowed (eraseTableValue allowed coordinate value) *
        complete (eraseTableValue allowed coordinate value) labels := by
  have hsub : ∀ other, eraseTableValue allowed coordinate value other ⊆ allowed other := by
    intro other
    by_cases heq : other = coordinate
    · subst other
      simp only [eraseTableValue, Function.update_self]
      exact Finset.erase_subset _ _
    · rw [eraseTableValue, Function.update_of_ne heq]
  have hguard (labels : Coordinate → Value) :
      (∀ other, labels other ∈ eraseTableValue allowed coordinate value other) ↔
        (∀ other, labels other ∈ allowed other) ∧ labels coordinate ≠ value := by
    constructor
    · intro h
      refine ⟨fun other => hsub other (h other), ?_⟩
      have hc := h coordinate
      simp only [eraseTableValue, Function.update_self, Finset.mem_erase] at hc
      exact hc.1
    · rintro ⟨h, hne⟩ other
      by_cases heq : other = coordinate
      · subst other
        simpa only [eraseTableValue, Function.update_self, Finset.mem_erase] using And.intro hne (h coordinate)
      · simpa only [eraseTableValue, Function.update_of_ne heq] using h other
  have h := restrict_guard allowed _ hsub _ hguard labels
  by_cases hevent : labels coordinate ≠ value
  · simpa only [if_pos hevent] using h
  · simpa only [if_neg hevent] using h
theorem disclose_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (value : Value)
    (labels : Coordinate → Value) :
    cell (allowed coordinate) value * complete (discloseTableValue allowed coordinate value) labels =
      if labels coordinate = value then complete allowed labels else 0 := by
  by_cases ha : ∀ coordinate, (allowed coordinate).Nonempty
  · rw [complete_of_nonempty allowed ha, complete_of_nonempty _ (discloseTableValue_nonempty allowed ha coordinate value),
      cell, dif_pos (ha coordinate)]
    simpa only [SPMF.liftM_apply] using uniformTable_disclose_mass allowed ha coordinate value labels
  · rw [complete_of_empty allowed ha, SPMF.failure_apply, ite_self]
    by_cases hv : value ∈ allowed coordinate
    · have hr : ¬∀ other, (discloseTableValue allowed coordinate value other).Nonempty := by
        intro hr
        apply ha
        intro other
        by_cases heq : other = coordinate
        · subst other
          exact ⟨value, hv⟩
        · simpa only [discloseTableValue, Function.update_of_ne heq] using hr other
      rw [complete_of_empty _ hr, SPMF.failure_apply, mul_zero]
    · rw [cell_apply, if_neg hv, zero_mul]
theorem bind_disclose {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (next : Value → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (labels coordinate) labels) =
      (cell (allowed coordinate) >>= fun value =>
        complete (discloseTableValue allowed coordinate value) >>= next value) := by
  classical
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, disclose_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp
end SphincsSecurity.Concrete.UniformTableCompletion
end
end
-- ==== merged from SphincsSecurity_Proof_Residual_RetainedObservation ====
section

section
namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
inductive Probe (Coordinate : Type) where
  | pair (child parent : Coordinate) (distinct : child ≠ parent) (candidate : Digest)
  | output (parent : Coordinate)
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
def Probe.keep (probe : Probe Coordinate) (labels : Coordinate → Digest) (answer : HashOutput) : Prop :=
  match probe with
  | .pair child parent _ candidate => labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
  | .output parent => labels parent ≠ truncateHash answer
def Probe.restrict (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) : Coordinate → Finset Digest :=
  match probe with
  | .pair child parent _ candidate => pairedMissAllowed allowed child candidate parent (truncateHash answer)
  | .output parent => eraseTableValue allowed parent (truncateHash answer)
omit [Fintype Coordinate] in
theorem Probe.card_lower (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (coordinate : Coordinate) :
    (allowed coordinate).card - 1 ≤ (probe.restrict allowed answer coordinate).card := by
  cases probe with
  | pair child parent distinct candidate =>
      exact pairedMissAllowed_card_lower allowed child parent distinct candidate (truncateHash answer) coordinate
  | output parent =>
      by_cases heq : coordinate = parent
      · subst coordinate
        simpa only [Probe.restrict, eraseTableValue, Function.update_self] using
          (Finset.pred_card_le_card_erase (s := allowed parent) (a := truncateHash answer))
      · simpa only [Probe.restrict, eraseTableValue, Function.update_of_ne heq] using Nat.sub_le (allowed coordinate).card 1
theorem Probe.mass (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels := by
  cases probe with
  | pair child parent distinct candidate =>
      have h := paired_mass allowed child parent distinct candidate (truncateHash answer) labels
      by_cases hk : labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h
  | output parent =>
      have h := single_mass allowed parent (truncateHash answer) labels
      by_cases hk : labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h
noncomputable def response (labels : Coordinate → Digest) (probe : Probe Coordinate) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_apply (labels : Coordinate → Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    response labels probe answer = if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
noncomputable def lazyResponse (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe
theorem lazyResponse_apply (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    lazyResponse allowed probe answer = PMF.uniformOfFintype HashOutput answer *
      restrictionWeight allowed (probe.restrict allowed answer) := by
  rw [lazyResponse, SPMF.bind_apply_eq_tsum]
  simp only [response_apply, mul_ite, mul_zero]
  calc
    _ = PMF.uniformOfFintype HashOutput answer *
        ∑' labels, restrictionWeight allowed (probe.restrict allowed answer) *
          complete (probe.restrict allowed answer) labels := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro labels
      rw [← Probe.mass]
      split <;> simp only [mul_comm, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_left, weight_tsum_complete]
theorem posterior_mass (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    lazyResponse allowed probe answer * complete (probe.restrict allowed answer) labels =
      complete allowed labels * response labels probe answer := by
  rw [lazyResponse_apply, mul_assoc, ← Probe.mass, response_apply]
  split <;> simp only [mul_comm, zero_mul]
theorem lazyResponse_nonempty (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (h : lazyResponse allowed probe answer ≠ 0) :
    ∀ coordinate, (probe.restrict allowed answer coordinate).Nonempty := by
  by_contra hnonempty
  rw [lazyResponse_apply, weight_of_empty _ _ hnonempty, mul_zero] at h
  exact h rfl
end SphincsSecurity.Concrete.HiddenLabelObservation
end
section
namespace SphincsSecurity.Concrete.RetainedObservation
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Label Answer Result : Type}
theorem bind_comm (p : SPMF Label) (q : SPMF Answer) (next : Label → Answer → SPMF Result) :
    (p >>= fun label => q >>= next label) = (q >>= fun answer => p >>= fun label => next label answer) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro answer
  apply tsum_congr
  intro label
  exact mul_left_comm _ _ _
theorem bind_congr (p : SPMF Label) (f g : Label → SPMF Result)
    (h : ∀ label, p label ≠ 0 → f label = g label) : (p >>= f) = (p >>= g) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum]
  apply tsum_congr
  intro label
  by_cases hp : p label = 0
  · simp only [hp, zero_mul]
  · rw [h label hp]
theorem bind_nonzero (p : SPMF Label) (next : Label → SPMF Result) (result : Result) :
    (p >>= next) result ≠ 0 ↔ ∃ label, p label ≠ 0 ∧ next label result ≠ 0 := by
  rw [← SPMF.mem_support_iff, SPMF.support_bind]
  simp only [Set.mem_iUnion, SPMF.mem_support_iff, exists_prop]
theorem lift_bind_const (p : PMF Label) (next : SPMF Result) :
    ((liftM p : SPMF Label) >>= fun _ => next) = next := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
theorem toPMF_bind_lift (p : PMF Label) (next : Label → SPMF Answer) :
    ((liftM p : SPMF Label) >>= next).toPMF = p.bind (fun label => (next label).toPMF) := by
  rw [SPMF.toPMF_bind, SPMF.liftM_eq_map, SPMF.toPMF_mk]
  simp only [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
  rfl
noncomputable def observe (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) : SPMF Result :=
  (liftM response.toPMF : SPMF (Option Answer)) >>= fun
    | none => stopped
    | some answer => next answer
theorem observe_apply (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result = response.toPMF none * stopped result +
      ∑' answer, response answer * next answer result := by
  rw [observe, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.liftM_apply]
  rw [tsum_option _ ENNReal.summable]
  rfl
theorem observe_nonzero (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result ≠ 0 ↔
      (response.toPMF none ≠ 0 ∧ stopped result ≠ 0) ∨
        ∃ answer, response answer ≠ 0 ∧ next answer result ≠ 0 := by
  rw [observe, bind_nonzero]
  constructor
  · rintro ⟨answer, hanswer, hresult⟩
    cases answer with
    | none => exact Or.inl ⟨by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    | some answer =>
        refine Or.inr ⟨answer, ?_, hresult⟩
        rw [SPMF.apply_eq_toPMF_some response answer]
        simpa only [SPMF.liftM_apply] using hanswer
  · rintro (⟨hanswer, hresult⟩ | ⟨answer, hanswer, hresult⟩)
    · exact ⟨none, by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    · refine ⟨some answer, ?_, hresult⟩
      rw [SPMF.liftM_apply, ← SPMF.apply_eq_toPMF_some response answer]
      exact hanswer
theorem observe_bind {Other : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (after : Result → SPMF Other) :
    (observe response stopped next >>= after) =
      observe response (stopped >>= after) (fun answer => next answer >>= after) := by
  simp only [observe, bind_assoc]
  congr 1
  funext answer
  cases answer <;> rfl
theorem observe_congr (response : SPMF Answer) (stopped : SPMF Result)
    (f g : Answer → SPMF Result) (h : ∀ answer, response answer ≠ 0 → f answer = g answer) :
    observe response stopped f = observe response stopped g := by
  apply SPMF.ext
  intro result
  simp only [observe_apply]
  apply congrArg (response.toPMF none * stopped result + ·)
  apply tsum_congr
  intro answer
  by_cases hp : response answer = 0
  · simp only [hp, zero_mul]
  · rw [h answer hp]
theorem posterior_observe (prior : PMF Label) (response : Label → SPMF Answer)
    (predictive : SPMF Answer) (posterior : Answer → SPMF Label)
    (hpredictive : predictive = ((liftM prior : SPMF Label) >>= response))
    (hmass : ∀ answer label, predictive answer * posterior answer label = prior label * response label answer)
    (stopped : SPMF Result) (next : Answer → Label → SPMF Result) :
    ((liftM prior : SPMF Label) >>= fun label => observe (response label) stopped (fun answer => next answer label)) =
      observe predictive stopped (fun answer => posterior answer >>= next answer) := by
  have hnone : (∑' label, prior label * (response label).toPMF none) = predictive.toPMF none := by
    rw [hpredictive, toPMF_bind_lift, PMF.bind_apply]
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, observe_apply, mul_add, ENNReal.tsum_add]
  apply congrArg₂ (· + ·)
  · simpa only [← mul_assoc, ENNReal.tsum_mul_right] using congrArg (· * stopped result) hnone
  · simp only [← ENNReal.tsum_mul_left, ← mul_assoc, hmass]
    rw [ENNReal.tsum_comm]
end SphincsSecurity.Concrete.RetainedObservation
namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp UniformTableCompletion RetainedObservation
theorem bind_response_stopped {Coordinate Result : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (allowed : Coordinate → Finset Digest) (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (probe : Probe Coordinate) (stopped : SPMF Result) (next : HashOutput → (Coordinate → Digest) → SPMF Result) :
    (complete allowed >>= fun labels => observe (response labels probe) stopped (fun answer => next answer labels)) =
      observe (lazyResponse allowed probe) stopped (fun answer => complete (probe.restrict allowed answer) >>= next answer) := by
  have h := posterior_observe (uniformTable allowed ha) (fun labels => response labels probe)
    (lazyResponse allowed probe) (fun answer => complete (probe.restrict allowed answer))
    (by rw [lazyResponse, complete_of_nonempty allowed ha])
    (fun answer labels => by
      simpa only [complete_of_nonempty allowed ha, SPMF.liftM_apply] using posterior_mass allowed probe answer labels)
    stopped next
  simpa only [complete_of_nonempty allowed ha] using h
end SphincsSecurity.Concrete.HiddenLabelObservation
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_AdaptiveHiddenHazard ====
section

section
namespace SphincsSecurity.Concrete.HiddenLabelProbe
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
noncomputable def law (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) : PMF ((Coordinate → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)
def Match (child parent : Coordinate) (candidate : Digest)
    (result : (Coordinate → Digest) × HashOutput) : Prop :=
  result.1 child = candidate ∨ truncateHash result.2 = result.1 parent
theorem prob_truncate_eq (target : Digest) :
    Pr[fun answer => truncateHash answer = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply] using probEvent_uniform_truncateHash_eq target
theorem prob_truncate_ne (target : Digest) :
    Pr[fun answer => truncateHash answer ≠ target | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := probEvent_compl (PMF.uniformOfFintype HashOutput) (fun answer => truncateHash answer = target)
  rw [prob_truncate_eq, probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by finiteness) (by rwa [add_comm])
theorem prob_survive (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest) :
    Pr[fun result => ¬Match child parent candidate result | law allowed ha] =
      Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] *
        (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun result => ¬Match child parent candidate result |
    (uniformTable allowed ha) >>= fun labels =>
      (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (labels : Coordinate → Digest) :
      Pr[(fun result => ¬Match child parent candidate result) ∘ (fun answer => (labels, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if labels child ≠ candidate then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hc : labels child = candidate
    · simp [Function.comp_def, Match, hc]
    · simpa only [Function.comp_def, Match, hc, false_or, if_pos hc] using prob_truncate_ne (labels parent)
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]
theorem prob_child_miss (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest) :
    Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] =
      1 - Pr[fun labels => labels child = candidate | uniformTable allowed ha] := by
  have h := probEvent_compl (uniformTable allowed ha) (fun labels => labels child = candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) (by rwa [add_comm])
theorem prob_child_hit_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[fun labels => labels child = candidate | uniformTable allowed ha] ≤ (minimum : ENNReal)⁻¹ := by
  rw [probEvent_uniformTable_eq]
  split
  · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmin)
  · exact bot_le
theorem prob_survive_ge (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    (1 - (minimum : ENNReal)⁻¹) ^ 2 ≤
      Pr[fun result => ¬Match child parent candidate result | law allowed ha] := by
  have hspace : minimum ≤ Fintype.card Digest := hmin.trans (Finset.card_le_univ _)
  rw [prob_survive, prob_child_miss, pow_two]
  exact mul_le_mul' (tsub_le_tsub_left (prob_child_hit_le allowed ha child candidate minimum hmin) _)
    (tsub_le_tsub_left (ENNReal.inv_le_inv.mpr (by exact_mod_cast hspace)) _)
theorem prob_match_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤ 1 - (1 - (minimum : ENNReal)⁻¹) ^ 2 := by
  have h := probEvent_compl (law allowed ha) (Match child parent candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq' (by simp) h
  rw [heq]
  exact tsub_le_tsub_left (prob_survive_ge allowed ha child parent candidate minimum hmin) _
theorem prob_match_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 :=
  prob_match_le allowed ha child parent candidate _ hmin
end SphincsSecurity.Concrete.HiddenLabelProbe
end
section
namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_failure (labels : Coordinate → Digest) (probe : Probe Coordinate) :
    (response labels probe).toPMF none =
      Pr[fun answer => ¬probe.keep labels answer | PMF.uniformOfFintype HashOutput] := by
  rw [response, toPMF_bind_lift, PMF.bind_apply, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, not_true_eq_false, if_false, SPMF.toPMF_pure, PMF.pure_apply,
      reduceCtorEq, mul_zero]
  · simp only [h, if_false, not_false_eq_true, if_true, SPMF.toPMF_failure, PMF.pure_apply,
      mul_one, PMF.probOutput_eq_apply]
theorem lazyResponse_pair_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none =
      Pr[HiddenLabelProbe.Match child parent candidate | HiddenLabelProbe.law allowed ha] := by
  rw [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[HiddenLabelProbe.Match child parent candidate |
    (uniformTable allowed ha) >>= fun labels => (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro labels
  apply congrArg (uniformTable allowed ha labels * ·)
  rw [response_failure]
  apply congrArg (fun event => Pr[event | PMF.uniformOfFintype HashOutput])
  funext answer
  apply propext
  simp only [Probe.keep, HiddenLabelProbe.Match, Function.comp_def, not_and_or, not_not, eq_comm]
theorem lazyResponse_pair_failure_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 := by
  rw [lazyResponse_pair_failure allowed ha child parent hne candidate]
  exact HiddenLabelProbe.prob_match_le_rounds allowed ha child parent candidate rounds hmin
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_output_failure (labels : Coordinate → Digest) (parent : Coordinate) :
    (response labels (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [response_failure]
  simpa only [Probe.keep, not_not, eq_comm] using HiddenLabelProbe.prob_truncate_eq (labels parent)
theorem lazyResponse_output_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (parent : Coordinate) :
    (lazyResponse allowed (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply,
    response_output_failure, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end SphincsSecurity.Concrete.HiddenLabelObservation
namespace SphincsSecurity.Concrete.AdaptiveHiddenLabels
open _root_.OracleComp OracleSpec ENNReal HiddenLabelObservation
end SphincsSecurity.Concrete.AdaptiveHiddenLabels
end
end
-- ==== merged from SphincsSecurity_Proof_Residual_ResidualProbeCompletion ====
section

section
namespace SphincsSecurity.Concrete.ResidualTableCompletion
open _root_.OracleComp ENNReal UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
abbrev Cache (Cell : Type) := Cell → Option HashOutput
def allowed (cache : Cache Cell) : Cell → Finset HashOutput :=
  fun input => match cache input with
    | none => Finset.univ
    | some answer => {answer}
omit [Fintype Cell] [DecidableEq Cell] in
theorem allowed_nonempty (cache : Cache Cell) : ∀ input, (allowed cache input).Nonempty := by
  intro input
  cases h : cache input <;> simp only [allowed, h]
  · exact Finset.univ_nonempty
  · exact Finset.singleton_nonempty _
noncomputable def completeRows (cache : Cache Cell) : SPMF (Cell → HashOutput) :=
  complete (allowed cache)
noncomputable def reply (cache : Cache Cell) (input : Cell) : SPMF HashOutput :=
  match cache input with
  | none => liftM (PMF.uniformOfFintype HashOutput)
  | some answer => pure answer
theorem completeRows_empty :
    completeRows (Cell := Cell) (fun _ => none) = liftM (PMF.uniformOfFintype (Cell → HashOutput)) := by
  apply SPMF.ext
  intro table
  simp only [completeRows, complete_apply, allowed, Finset.mem_univ, implies_true, if_true,
    Finset.card_univ, Finset.prod_const, Finset.card_univ, SPMF.liftM_apply, PMF.uniformOfFintype_apply, Fintype.card_fun]
omit [Fintype Cell] [DecidableEq Cell] in
theorem cell_eq_reply (cache : Cache Cell) (input : Cell) : cell (allowed cache input) = reply cache input := by
  apply SPMF.ext
  intro answer
  cases h : cache input with
  | none => simp only [cell_apply, allowed, h, Finset.mem_univ, if_true, Finset.card_univ,
      reply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  | some value => simp only [cell_apply, allowed, h, Finset.mem_singleton, Finset.card_singleton,
      Nat.cast_one, inv_one, reply, SPMF.pure_apply]
omit [Fintype Cell] in
theorem allowed_update (cache : Cache Cell) (input : Cell) (answer : HashOutput) :
    discloseTableValue (allowed cache) input answer = allowed (Function.update cache input (some answer)) := by
  funext other
  by_cases h : other = input
  · subst other
    simp only [discloseTableValue, Function.update_self, allowed]
  · simp only [discloseTableValue, Function.update_of_ne h, allowed]
theorem bind_read {Result : Type} (cache : Cache Cell) (input : Cell)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table => next (table input) table) =
      (reply cache input >>= fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [completeRows, bind_disclose, cell_eq_reply]
  simp only [allowed_update, completeRows]
theorem bind_fresh {Result : Type} (cache : Cache Cell) (input : Cell) (hfresh : cache input = none)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table => next (table input) table) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_read, reply, hfresh]
theorem completeRows_bind_const {Result : Type} (cache : Cache Cell) (next : SPMF Result) :
    (completeRows cache >>= fun _ => next) = next := by
  rw [completeRows, complete_of_nonempty _ (allowed_nonempty cache)]
  exact RetainedObservation.lift_bind_const _ _
end SphincsSecurity.Concrete.ResidualTableCompletion
end
section
namespace SphincsSecurity.Concrete.ResidualProbeCompletion
open _root_.OracleComp OracleSpec HiddenLabelObservation UniformTableCompletion RetainedObservation ResidualTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Cell Result : Type} [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Cell] [DecidableEq Cell]
omit [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell] in
theorem observe_response (labels : Coordinate → Digest) (probe : Probe Coordinate)
    (stopped : SPMF Result) (next : HashOutput → SPMF Result) :
    observe (response labels probe) stopped next =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        if probe.keep labels answer then next answer else stopped) := by
  rw [observe, response, toPMF_bind_lift]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, bind_assoc]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, SPMF.toPMF_pure, SPMF.lift_pure, pure_bind]
  · simp only [h, if_false, SPMF.toPMF_failure, SPMF.lift_pure, pure_bind]
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem fixedLabels_fresh (labels : Coordinate → Digest) (cache : Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coordinate) (stopped : SPMF Result)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) table else stopped) =
        observe (response labels probe) stopped
          (fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_fresh cache input hfresh (fun answer table => if probe.keep labels answer then next answer table else stopped),
    observe_response]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true]
  · simp only [h, if_false, completeRows_bind_const]
theorem bind_fresh_probe (candidates : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (candidates coordinate).Nonempty) (cache : Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coordinate) (stopped : SPMF Result)
    (next : HashOutput → (Coordinate → Digest) → (Cell → HashOutput) → SPMF Result) :
    (complete candidates >>= fun labels => completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) labels table else stopped) =
        observe (lazyResponse candidates probe) stopped (fun answer =>
          complete (probe.restrict candidates answer) >>= fun labels =>
            completeRows (Function.update cache input (some answer)) >>= next answer labels) := by
  have hfixed (labels : Coordinate → Digest) := fixedLabels_fresh labels cache input hfresh probe stopped
    (fun answer table => next answer labels table)
  simp_rw [hfixed]
  exact bind_response_stopped candidates ha probe stopped
    (fun answer labels => completeRows (Function.update cache input (some answer)) >>= next answer labels)
end SphincsSecurity.Concrete.ResidualProbeCompletion
end
end
-- ==== merged from SphincsSecurity_Proof_Deterministic_Replay ====
section

open OracleComp OracleSpec
namespace DeterministicSigning
set_option backward.isDefEq.respectTransparency false
variable {D R : Type} [DecidableEq D]
inductive Resolves (cache : QueryCache (D →ₒ R)) {α : Type} : OracleComp (D →ₒ R) α → α → Prop
  | pure (value : α) : Resolves cache (pure value) value
  | query (input : D) (answer : R) (hanswer : cache input = some answer)
      (next : R → OracleComp (D →ₒ R) α) (value : α)
      (tail : Resolves cache (next answer) value) :
      Resolves cache (liftM ((D →ₒ R).query input) >>= next) value
omit [DecidableEq D] in
theorem Resolves.mono {α : Type} {left right : QueryCache (D →ₒ R)}
    {computation : OracleComp (D →ₒ R) α} {value : α}
    (h : Resolves left computation value) (hle : left ≤ right) : Resolves right computation value := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih => exact .query input answer (hle hanswer) next value ih
variable [SampleableType R]
theorem cache_le_of_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before)) : before ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨step, hstep, htail⟩ := h
      exact (QueryImpl.withCaching_cache_le _ input before step hstep).trans (ih step.1 step.2 result htail)
theorem query_caches (input : D) (before : QueryCache (D →ₒ R))
    (result : R × QueryCache (D →ₒ R))
    (h : result ∈ support ((randomOracle (spec := D →ₒ R) input).run before)) :
    result.2 input = some result.1 := by
  cases hc : before input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at h
      obtain ⟨answer, _, rfl⟩ := h
      exact QueryCache.cacheQuery_self _ _ _
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at h
      subst result
      exact hc
theorem resolves_of_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before)) :
    Resolves result.2 computation result.1 := by
  induction computation using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
      subst result
      exact .pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨step, hstep, htail⟩ := h
      have hle := cache_le_of_run (next step.1) step.2 result htail
      exact .query input step.1 (hle (query_caches input before step hstep)) next result.1
        (ih step.1 step.2 result htail)
theorem Resolves.run_eq_pure {α : Type} {cache : QueryCache (D →ₒ R)}
    {computation : OracleComp (D →ₒ R) α} {value : α}
    (h : Resolves cache computation value) :
    (simulateQ randomOracle computation).run cache = Pure.pure (value, cache) := by
  induction h with
  | pure value => rfl
  | query input answer hanswer next value _ ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hanswer, pure_bind, ih]
theorem replay_run {α : Type} (computation : OracleComp (D →ₒ R) α)
    (before : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (h : result ∈ support ((simulateQ randomOracle computation).run before))
    (after : QueryCache (D →ₒ R)) (hle : result.2 ≤ after) :
    (simulateQ randomOracle computation).run after = pure (result.1, after) :=
  ((resolves_of_run computation before result h).mono hle).run_eq_pure
end DeterministicSigning
end
-- ==== merged from SphincsSecurity_Proof_Fts_ProposalWordDistribution ====
section

namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
theorem pmf_map_injective_apply {α β : Type*} (law : PMF α) (f : α → β)
    (hinjective : Function.Injective f) (value : α) : (law.map f) (f value) = law value := by
  rw [PMF.map_apply, tsum_eq_single value]
  · simp only [↓reduceIte]
  · intro other hne
    exact if_neg (fun h => hne (hinjective h).symm)
theorem pmf_map_apply_zero_of_not_image {α β : Type*} (law : PMF α) (f : α → β) (value : β)
    (h : ∀ source, value ≠ f source) : (law.map f) value = 0 := by
  letI : DecidableEq β := Classical.decEq β
  rw [PMF.map_apply]
  exact (tsum_congr (fun source => if_neg (h source))).trans tsum_zero
noncomputable def independentProposalWord {α : Type*} (law : PMF α) : Nat → PMF (List α)
  | 0 => pure []
  | steps + 1 => law.bind fun next => (independentProposalWord law steps).map (next :: ·)
theorem independentProposalWord_apply {α : Type*} (law : PMF α) (steps : Nat) (word : List α) :
    independentProposalWord law steps word = if word.length = steps then (word.map law).prod else 0 := by
  classical
  letI : DecidableEq α := Classical.decEq α
  induction steps generalizing word with
  | zero => cases word <;> simp [independentProposalWord, PMF.pure_apply]
  | succ steps ih =>
      cases word with
      | nil => simp [independentProposalWord, PMF.bind_apply, PMF.map_apply]
      | cons next rest =>
          rw [independentProposalWord, PMF.bind_apply]
          have hm (head : α) : ((independentProposalWord law steps).map (head :: ·)) (next :: rest) =
              if next = head then independentProposalWord law steps rest else 0 := by
            by_cases h : next = head
            · subst next
              rw [if_pos rfl]
              exact pmf_map_injective_apply _ _ (fun _ _ h => (List.cons.inj h).2) rest
            · rw [if_neg h]
              exact pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => h (List.cons.inj heq).1)
          simp only [hm, tsum_ite_eq', mul_ite, mul_zero, ih, List.length_cons,
            Nat.add_right_cancel_iff, List.map_cons, List.prod_cons]
noncomputable def proposalFailureCount (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF Nat :=
  ⟨fun count => accept * (1 - accept) ^ count, by
    apply ENNReal.summable.hasSum_iff.mpr
    have hdouble : 1 - (1 - accept) = accept :=
      ENNReal.sub_eq_of_eq_add_rev' (by finiteness) (tsub_add_cancel_of_le hle).symm
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hdouble,
      ENNReal.mul_inv_cancel hpos (ne_top_of_le_ne_top (by finiteness) hle)]⟩
theorem proposalFailureCount_apply (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (count : Nat) :
    proposalFailureCount accept hpos hle count = accept * (1 - accept) ^ count := rfl
noncomputable def rejectedProposalWord {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (List α) :=
  (proposalFailureCount accept hpos hle).bind (independentProposalWord law)
theorem rejectedProposalWord_apply {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (word : List α) :
    rejectedProposalWord law accept hpos hle word =
      accept * (1 - accept) ^ word.length * (word.map law).prod := by
  classical
  simp only [rejectedProposalWord, PMF.bind_apply, independentProposalWord_apply, mul_ite, mul_zero,
    tsum_ite_eq', proposalFailureCount_apply]
theorem rejectedProposalWord_nil {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    rejectedProposalWord law accept hpos hle [] = accept := by
  simp only [rejectedProposalWord_apply, List.length_nil, pow_zero, List.map_nil, List.prod_nil, mul_one]
theorem rejectedProposalWord_cons {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (next : α) (rest : List α) :
    rejectedProposalWord law accept hpos hle (next :: rest) =
      (1 - accept) * law next * rejectedProposalWord law accept hpos hle rest := by
  simp only [rejectedProposalWord_apply, List.length_cons, pow_succ, List.map_cons, List.prod_cons]
  ring
noncomputable def recordProposalBridge {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (List α × Ω) :=
  record.bind fun outcome => (rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))
theorem recordProposalBridge_apply {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (word : List α) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle (word, outcome) =
      record outcome * rejectedProposalWord rejected accept hpos hle word := by
  classical
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [recordProposalBridge, PMF.bind_apply]
  have hm (value : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, value))) (word, outcome) =
        if outcome = value then rejectedProposalWord rejected accept hpos hle word else 0 := by
    by_cases h : outcome = value
    · subst outcome
      rw [if_pos rfl]
      exact pmf_map_injective_apply _ _ (fun _ _ h => (Prod.mk.inj h).1) word
    · rw [if_neg h]
      exact pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => h (Prod.mk.inj heq).2)
  simp only [hm, mul_ite, mul_zero, tsum_ite_eq']
theorem recordProposalBridge_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map Prod.snd = record := by
  unfold recordProposalBridge
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (rejectedProposalWord rejected accept hpos hle).map (Function.const (List α) outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]
theorem recordProposalBridge_nil {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle ([], outcome) = accept * record outcome := by
  rw [recordProposalBridge_apply, rejectedProposalWord_nil, mul_comm]
theorem recordProposalBridge_cons {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (next : α) (rest : List α) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle (next :: rest, outcome) =
      (1 - accept) * rejected next * recordProposalBridge record rejected accept hpos hle (rest, outcome) := by
  rw [recordProposalBridge_apply, recordProposalBridge_apply, rejectedProposalWord_cons]
  ring
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ProposalBridgeKernel ====
section

namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
theorem proposalResidual_sum {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hcap : ∀ index : α, accept * target index ≤ base index) :
    (∑' index : α, (base index - accept * target index)) = 1 - accept := by
  apply ENNReal.eq_sub_of_add_eq' (by finiteness)
  calc
    _ = ∑' index : α, ((base index - accept * target index) + accept * target index) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, target.tsum_coe, mul_one]
    _ = ∑' index, base index := tsum_congr (fun index => tsub_add_cancel_of_le (hcap index))
    _ = 1 := base.tsum_coe
noncomputable def proposalResidualLaw {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) : PMF α :=
  PMF.normalize (fun index => base index - accept * target index)
    (by rw [proposalResidual_sum base target accept hcap]; exact ne_of_gt (tsub_pos_iff_lt.mpr hlt))
    (by rw [proposalResidual_sum base target accept hcap]; finiteness)
theorem proposalResidualLaw_apply {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) (index : α) :
    proposalResidualLaw base target accept hlt hcap index =
      (base index - accept * target index) * (1 - accept)⁻¹ := by
  simp only [proposalResidualLaw, PMF.normalize_apply, proposalResidual_sum base target accept hcap]
theorem proposalResidualLaw_scaled {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) (index : α) :
    (1 - accept) * proposalResidualLaw base target accept hlt hcap index = base index - accept * target index := by
  rw [proposalResidualLaw_apply]
  calc
    _ = (base index - accept * target index) * ((1 - accept) * (1 - accept)⁻¹) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hlt)) (by finiteness), mul_one]
noncomputable def proposalAcceptanceCoin (accept : ENNReal) (hle : accept ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun accepted => if accepted then accept else 1 - accept) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
    exact (add_comm _ _).trans (tsub_add_cancel_of_le hle))
theorem proposalAcceptanceCoin_bind_apply {Ω : Type*} (accept : ENNReal) (hle : accept ≤ 1)
    (continuation : Bool → PMF Ω) (outcome : Ω) :
    (proposalAcceptanceCoin accept hle).bind continuation outcome =
      (1 - accept) * continuation false outcome + accept * continuation true outcome := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Fintype.sum_bool, proposalAcceptanceCoin, PMF.ofFintype_apply, Bool.false_eq_true, if_false, if_true]
  exact add_comm _ _
noncomputable def proposalRecordStep {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) : PMF (α ⊕ Ω) :=
  (proposalAcceptanceCoin accept hlt.le).bind fun accepted =>
    if accepted then record.map Sum.inr
    else (proposalResidualLaw base (record.map label) accept hlt hcap).map Sum.inl
theorem proposalRecordStep_reject {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) (index : α) :
    proposalRecordStep base record label accept hlt hcap (.inl index) = base index - accept * (record.map label) index := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [proposalRecordStep, proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.map_apply, Sum.inl.injEq, Sum.inl_ne_inr,
    tsum_ite_eq', if_false, tsum_zero, mul_zero, add_zero, proposalResidualLaw_scaled]
theorem proposalRecordStep_accept {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) (outcome : Ω) :
    proposalRecordStep base record label accept hlt hcap (.inr outcome) = accept * record outcome := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [proposalRecordStep, proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.map_apply, Sum.inr.injEq, Sum.inr_ne_inl,
    tsum_ite_eq', if_false, tsum_zero, mul_zero, zero_add]
theorem proposalRecordStep_label {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) :
    (proposalRecordStep base record label accept hlt hcap).map (Sum.elim id label) = base := by
  unfold proposalRecordStep
  rw [PMF.map_bind]
  have hbranch (accepted : Bool) :
      (if accepted then record.map Sum.inr
        else (proposalResidualLaw base (record.map label) accept hlt hcap).map Sum.inl).map (Sum.elim id label) =
      if accepted then record.map label else proposalResidualLaw base (record.map label) accept hlt hcap := by
    cases accepted <;> simp only [Bool.false_eq_true, if_false, if_true, PMF.map_comp, Function.comp_def, Sum.elim_inl,
      Sum.elim_inr, id_eq]
    exact PMF.map_id _
  simp_rw [hbranch]
  ext index
  rw [proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, proposalResidualLaw_scaled, tsub_add_cancel_of_le (hcap index)]
noncomputable def cappedRecordProposalBridge {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) : PMF (List α × Ω) :=
  recordProposalBridge record (proposalResidualLaw base (record.map label) accept hlt hcap) accept hpos hlt.le
theorem cappedRecordProposalBridge_nil {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (outcome : Ω) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap ([], outcome) =
      proposalRecordStep base record label accept hlt hcap (.inr outcome) := by
  rw [cappedRecordProposalBridge, recordProposalBridge_nil, proposalRecordStep_accept]
theorem cappedRecordProposalBridge_cons {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (head : α) (rest : List α) (outcome : Ω) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap (head :: rest, outcome) =
      proposalRecordStep base record label accept hlt hcap (.inl head) *
        cappedRecordProposalBridge base record label accept hpos hlt hcap (rest, outcome) := by
  rw [cappedRecordProposalBridge, recordProposalBridge_cons, proposalResidualLaw_scaled, proposalRecordStep_reject]
def prependProposalRecord {α Ω : Type*} (head : α) (result : List α × Ω) : List α × Ω :=
  (head :: result.1, result.2)
private theorem prependProposalRecord_apply {α Ω : Type*} [DecidableEq α]
    (law : PMF (List α × Ω)) (head : α) (word : List α) (outcome : Ω) :
    (law.map (prependProposalRecord head)) (word, outcome) =
      match word with
      | [] => 0
      | next :: rest => if next = head then law (rest, outcome) else 0 := by
  cases word with
  | nil =>
      apply pmf_map_apply_zero_of_not_image
      intro source heq
      have h := congrArg Prod.fst heq
      change [] = head :: source.1 at h
      cases h
  | cons next rest =>
      change (law.map (prependProposalRecord head)) (next :: rest, outcome) =
        if next = head then law (rest, outcome) else 0
      by_cases h : next = head
      · subst next
        rw [if_pos rfl]
        apply pmf_map_injective_apply law (prependProposalRecord head) _ (rest, outcome)
        intro left right h
        have hfirst := congrArg Prod.fst h
        have hsecond := congrArg Prod.snd h
        change head :: left.1 = head :: right.1 at hfirst
        change left.2 = right.2 at hsecond
        exact Prod.ext (List.cons.inj hfirst).2 hsecond
      · rw [if_neg h]
        exact pmf_map_apply_zero_of_not_image _ _ _
          (fun source heq => h (List.cons.inj (congrArg Prod.fst heq)).1)
noncomputable def proposalBridgeContinuation {α Ω : Type*} (law : PMF (List α × Ω)) : α ⊕ Ω → PMF (List α × Ω)
  | .inl head => law.map (prependProposalRecord head)
  | .inr outcome => PMF.pure ([], outcome)
theorem cappedRecordProposalBridge_step {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap =
      (proposalRecordStep base record label accept hlt hcap).bind
        (proposalBridgeContinuation (cappedRecordProposalBridge base record label accept hpos hlt hcap)) := by
  letI : DecidableEq α := Classical.decEq α
  let law := cappedRecordProposalBridge base record label accept hpos hlt hcap
  let rejected := proposalResidualLaw base (record.map label) accept hlt hcap
  have hexpand : (proposalRecordStep base record label accept hlt hcap).bind (proposalBridgeContinuation law) =
      (proposalAcceptanceCoin accept hlt.le).bind (fun accepted =>
        if accepted then record.map (fun outcome => ([], outcome))
        else rejected.bind (fun head => law.map (prependProposalRecord head))) := by
    rw [proposalRecordStep, PMF.bind_bind]
    apply congrArg (PMF.bind (proposalAcceptanceCoin accept hlt.le))
    funext accepted
    cases accepted <;> simp only [Bool.false_eq_true, if_false, if_true, PMF.bind_map,
      Function.comp_def, proposalBridgeContinuation]
    all_goals rfl
  change law = _
  rw [hexpand]
  ext result
  rcases result with ⟨word, outcome⟩
  rw [proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true]
  have hrej : (rejected.bind (fun head => law.map (prependProposalRecord head))) (word, outcome) =
      match word with
      | [] => 0
      | next :: rest => rejected next * law (rest, outcome) := by
    rw [PMF.bind_apply]
    simp only [prependProposalRecord_apply]
    cases word <;> simp only [mul_zero, tsum_zero, mul_ite, tsum_ite_eq']
  rw [hrej]
  cases word with
  | nil =>
      rw [pmf_map_injective_apply record (fun outcome => ([], outcome))
        (fun _ _ h => congrArg Prod.snd h) outcome, mul_zero, zero_add]
      exact (cappedRecordProposalBridge_nil base record label accept hpos hlt hcap outcome).trans
        (proposalRecordStep_accept base record label accept hlt hcap outcome)
  | cons head rest =>
      have hacc : (record.map (fun outcome => ([], outcome))) (head :: rest, outcome) = 0 :=
        pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => by
          have h := congrArg Prod.fst heq
          change head :: rest = [] at h
          cases h)
      rw [hacc, mul_zero, add_zero]
      change cappedRecordProposalBridge base record label accept hpos hlt hcap (head :: rest, outcome) = _
      rw [cappedRecordProposalBridge_cons, proposalRecordStep_reject, ← proposalResidualLaw_scaled base (record.map label) accept hlt hcap head]
      exact mul_assoc _ _ _
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TerminalProposalWord ====
section

namespace SphincsSecurity.Concrete
open ENNReal
noncomputable def completeProposalWord {α : Type*} (base : PMF α) : Nat → List α → PMF (List α)
  | 0, _ => PMF.pure []
  | total + 1, [] => independentProposalWord base (total + 1)
  | total + 1, head :: rest => (completeProposalWord base total rest).map (head :: ·)
theorem completeProposalWord_nil {α : Type*} (base : PMF α) (total : Nat) :
    completeProposalWord base total [] = independentProposalWord base total := by
  cases total <;> rfl
theorem completeProposalWord_eq_padding {α : Type*} (base : PMF α) (total : Nat) (consumed : List α) :
    completeProposalWord base total consumed =
      (independentProposalWord base (total - consumed.length)).map (fun word => consumed.take total ++ word) := by
  induction consumed generalizing total with
  | nil =>
      simp only [completeProposalWord_nil, List.length_nil, Nat.sub_zero, List.take_nil, List.nil_append]
      exact (PMF.map_id _).symm
  | cons head rest ih =>
      cases total with
      | zero => simp only [completeProposalWord, Nat.zero_sub, independentProposalWord,
          PMF.monad_pure_eq_pure, PMF.pure_map, List.take_zero, List.nil_append]
      | succ total =>
          rw [completeProposalWord, ih, PMF.map_comp]
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, List.take_succ_cons]
          rfl
theorem complete_cappedRecordProposalBridge {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (total : Nat) :
    (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
        (fun result => completeProposalWord base total (result.1 ++ [label result.2])) =
      independentProposalWord base total := by
  induction total with
  | zero => simp only [completeProposalWord, PMF.bind_const, independentProposalWord, PMF.monad_pure_eq_pure]
  | succ total ih =>
      rw [cappedRecordProposalBridge_step, PMF.bind_bind]
      have hbranch (branch : α ⊕ Ω) :
          (proposalBridgeContinuation (cappedRecordProposalBridge base record label accept hpos hlt hcap) branch).bind
              (fun result => completeProposalWord base (total + 1) (result.1 ++ [label result.2])) =
            (independentProposalWord base total).map (Sum.elim id label branch :: ·) := by
        cases branch with
        | inl head =>
            rw [proposalBridgeContinuation, PMF.bind_map]
            change (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
                (fun result => (completeProposalWord base total (result.1 ++ [label result.2])).map (head :: ·)) = _
            rw [← PMF.map_bind, ih]
            rfl
        | inr outcome =>
            simp only [proposalBridgeContinuation, PMF.pure_bind, List.nil_append,
              completeProposalWord, completeProposalWord_nil, Sum.elim_inr]
      simp_rw [hbranch]
      change (proposalRecordStep base record label accept hlt hcap).bind
          ((fun index => (independentProposalWord base total).map (index :: ·)) ∘ Sum.elim id label) = _
      rw [← PMF.bind_map, proposalRecordStep_label]
      rfl
theorem complete_cappedRecordProposalBridge_prefix {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (total : Nat) (consumed : List α) :
    (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
        (fun result => completeProposalWord base total (consumed ++ (result.1 ++ [label result.2]))) =
      completeProposalWord base total consumed := by
  induction consumed generalizing total with
  | nil =>
      simpa only [List.nil_append, completeProposalWord_nil] using
        complete_cappedRecordProposalBridge base record label accept hpos hlt hcap total
  | cons head rest ih =>
      cases total with
      | zero => simp only [completeProposalWord, PMF.bind_const]
      | succ total =>
          simp only [List.cons_append, completeProposalWord]
          rw [← PMF.map_bind, ih]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ConcreteTargetShapeQuery ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem normalizedTargetLogProduct_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (remaining : Finset IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    normalizedTargetLogProduct key after log payload target remaining = normalizedTargetLogProduct key before log payload target remaining := by
  simp only [normalizedTargetLogProduct, normalizedTargetLogMatch, eligibleSigningViews_cache_stable key before after log payload hcache hsigned]
theorem sourceSubsetMatch_family (target source : FewTimeView) (family : Finset (Finset IndexGroup)) :
    (∏ group ∈ family, sourceSubsetMatch target source group) =
      sourceSubsetMatch target source (groupCoordinates family) := by
  induction family using Finset.induction_on with
  | empty => simp [sourceSubsetMatch, groupCoordinates]
  | @insert group family hnot ih =>
      rw [Finset.prod_insert hnot, ih, sourceSubsetMatch_mul, groupCoordinates_insert]
theorem normalizedSourceSubsetMatch_family (target source : FewTimeView) (family : Finset (Finset IndexGroup))
    (hdisjoint : (family : Set (Finset IndexGroup)).PairwiseDisjoint id) :
    (∏ group ∈ family, normalizedSourceSubsetMatch target source group) =
      normalizedSourceSubsetMatch target source (groupCoordinates family) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_family]
  congr 2
  exact (Finset.card_biUnion hdisjoint).symm
theorem TargetShapeValid.pairwiseDisjoint {groups family : Finset (Finset IndexGroup)} {remaining : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hfamily : family ⊆ groups) :
    (family : Set (Finset IndexGroup)).PairwiseDisjoint id :=
  fun first hfirst second hsecond hne => hvalid.disjoint first (hfamily hfirst) second (hfamily hsecond) hne
theorem prod_add_family_expand (groups : Finset (Finset IndexGroup)) (a x : Finset IndexGroup → ENNReal) (c : ENNReal) :
    (∏ group ∈ groups, (a group + x group)) * c =
      ∑ removed ∈ groups.powerset, (∏ group ∈ removed, x group) * ((∏ group ∈ groups \ removed, a group) * c) := by
  rw [show (∏ group ∈ groups, (a group + x group)) = ∏ group ∈ groups, (x group + a group) by
    simp only [add_comm], Finset.prod_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem expected_cacheQuery_targetShapeMoments (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : FtsProbeSimulation.MessageHashInput key.parameter input) (hne : input ≠ tweakableHashInput key.parameter .message payload) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) =
        targetShapeQuery (arrivalRate target) (targetShapeMoments key before log payload target) groups remaining := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  have hexpand (output : HashOutput) :
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining =
        ∑ removed ∈ groups.powerset, (∏ group ∈ removed,
          (if Admissible (truncateMessageDigest output) then
            normalizedSourceSubsetMatch target (hashOutputFewTimeView output) group else 0)) *
          targetShapeMoments key before log payload target (groups \ removed) remaining := by
    simp only [targetShapeMoments,
      normalizedTargetLogProduct_cache_stable key before _ log payload target _ (QueryCache.le_cacheQuery before hfresh) hsigned,
      normalizedCachedTargetSubsetMatch_cacheQuery key.parameter before _ target _ input output hfresh hmessage hne]
    exact prod_add_family_expand groups _ _ _
  have hfamily (output : HashOutput) (removed : Finset (Finset IndexGroup)) (hremoved : removed ∈ groups.powerset.erase ∅) :
      (∏ group ∈ removed, (if Admissible (truncateMessageDigest output) then
          normalizedSourceSubsetMatch target (hashOutputFewTimeView output) group else 0)) =
        if Admissible (truncateMessageDigest output) then
          normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groupCoordinates removed) else 0 := by
    by_cases hadmissible : Admissible (truncateMessageDigest output)
    · simp only [hadmissible, if_true]
      exact normalizedSourceSubsetMatch_family target _ removed
        (hvalid.pairwiseDisjoint (Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2))
    · simp only [hadmissible, if_false]
      obtain ⟨group, hgroup⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hremoved).1
      exact Finset.prod_eq_zero hgroup rfl
  simp only [hexpand, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset groups)]
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
  unfold targetShapeQuery targetArrivalStep
  congr 1
  · rw [ENNReal.tsum_mul_right, hmass, one_mul]
  · apply Finset.sum_congr rfl
    intro removed hremoved
    simp only [← mul_assoc, ENNReal.tsum_mul_right]
    congr 1
    rw [← expected_hash_normalizedSourceSubsetMatch target (groupCoordinates removed)]
    apply tsum_congr
    intro output
    rw [hfamily output removed hremoved]
theorem targetShapeMoments_cacheQuery_unchanged (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hskip : ¬ FtsProbeSimulation.MessageHashInput key.parameter input ∨ input = tweakableHashInput key.parameter .message payload) :
    targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining =
      targetShapeMoments key before log payload target groups remaining := by
  simp only [targetShapeMoments,
    normalizedTargetLogProduct_cache_stable key before _ log payload target remaining (QueryCache.le_cacheQuery before hfresh) hsigned]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  rcases hskip with hmessage | rfl
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery key.parameter before _ target group input output hfresh,
      hmessage, false_and, if_false, add_zero]
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery_self key.parameter before _ target group output hfresh]
theorem expected_randomOracle_targetShapeMoments_le (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      targetShapeMoments key result.2 log payload target groups remaining) ≤
        targetShapeQuery (arrivalRate target)
          (targetShapeMoments key before log payload target) groups remaining := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) ≤ _
    by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input
    · by_cases heq : input = tweakableHashInput key.parameter .message payload
      · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inr heq),
          ENNReal.tsum_mul_right, hmass, one_mul]
        exact le_self_add
      · exact (expected_cacheQuery_targetShapeMoments key before log payload target groups remaining hvalid input hfresh hsigned hmessage heq).le
    · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inl hmessage),
        ENNReal.tsum_mul_right, hmass, one_mul]
      exact le_self_add
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    exact le_self_add
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_DigestCompletionCacheGrowth ====
section

section





section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def successfulSignerInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some signature, some view => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)) view
  | _, _ => 0
noncomputable def cachedSignerInputWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) : ENNReal :=
  match before input with
  | none => 0
  | some output =>
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then weight input (hashOutputFewTimeView output) else 0
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cachedSignerInputWeight_le_cacheMessageEntryWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message before weight input ≤ cacheMessageEntryWeight key.parameter weight before input := by
  unfold cachedSignerInputWeight cacheMessageEntryWeight
  cases before input with
  | none => exact le_rfl
  | some output =>
      simp only
      split_ifs with hsource htarget
      · exact le_rfl
      · obtain ⟨randomness, heq⟩ := hsource.1
        exact (htarget ⟨⟨messageDigestPayload key.root message randomness, heq.symm⟩, hsource.2⟩).elim
      · exact bot_le
      · exact le_rfl
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def onlyInputCache (cache : QueryCache HashSpec) (target : HashInput) :
    QueryCache HashSpec :=
  fun input => if input = target then cache input else none
theorem onlyInputCache_le (cache : QueryCache HashSpec) (target : HashInput) :
    onlyInputCache cache target ≤ cache := by
  intro input output hcached
  by_cases hinput : input = target
  · simpa [onlyInputCache, hinput] using hcached
  · simp [onlyInputCache, hinput] at hcached
theorem cachedMessageEntryCountWhere_onlyInput_le_one
    (cache : QueryCache HashSpec) (target : HashInput)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (onlyInputCache cache target) parameter root message P ≤ 1 := by
  have hsubsingleton :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).Subsingleton := by
    rintro ⟨leftInput, leftOutput⟩ hleft ⟨rightInput, rightOutput⟩ hright
    have hleftInput : leftInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hleft
    have hrightInput : rightInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hright
    subst leftInput
    subst rightInput
    have houtputs : leftOutput = rightOutput := by
      apply Option.some.inj
      exact hleft.1.1.symm.trans hright.1.1
    subst rightOutput
    rfl
  have hencard :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.2 hsubsingleton
  simpa only [cachedMessageEntryCountWhere, ENat.toENNReal_one] using
    ENat.toENNReal_mono hencard
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
def selectedLoopInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal) (result : DigestLoopRecord) : ENNReal :=
  match result.1 with
  | none => 0
  | some (randomness, index, leaves) => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness))
      (selectedFewTimeView index leaves)
theorem probEvent_signDigestLoop_fixedPrehit_le_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (input : HashInput) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView (onlyInputCache cache input) key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] ≤
      exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message
    (onlyInputCache cache input) cache (onlyInputCache_le cache input), cachedDigestAttemptRate_eq_count]
  calc
    _ = cachedMessageEntryCountWhere (onlyInputCache cache input) key.parameter key.root message P *
        exactDigestReuseWeight key message cache := by unfold exactDigestReuseWeight; ring
    _ ≤ 1 * exactDigestReuseWeight key message cache := mul_le_mul'
      (cachedMessageEntryCountWhere_onlyInput_le_one cache input key.parameter key.root message P) le_rfl
    _ = _ := one_mul _
theorem selectedLoopInputWeight_le_fresh_add_prehit
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (result : DigestLoopRecord)
    (hresult : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)) :
    selectedLoopInputWeight key message weight result ≤
      (∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
      (∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
        cachedSignerInputWeight key message before weight input else 0) := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp only [selectedLoopInputWeight]; exact bot_le
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
      let view := selectedFewTimeView index leaves
      change weight input view ≤ _
      cases hbefore : before input with
      | none =>
          have hfresh : FreshSelectedView before key message (· = view) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, hbefore, rfl⟩
          apply (hweight input view).trans
          apply le_trans ?_ le_self_add
          exact (le_of_eq (if_pos hfresh).symm).trans (ENNReal.le_tsum view)
      | some output =>
          have hattempt := signDigestLoop_initial_cached_result digestAttemptLimit key message randomness
            index leaves before after output hbefore hresult
          have hview : view = hashOutputFewTimeView output := signAttemptResultOfOutput_view output index leaves hattempt
          have hadmissible : Admissible (truncateMessageDigest output) :=
            (signAttemptResultOfOutput_ne_none_iff output).mp (by rw [hattempt]; exact Option.some_ne_none _)
          have hsource : cachedSignerInputWeight key message before weight input = weight input view := by
            simp only [cachedSignerInputWeight, hbefore]
            rw [if_pos ⟨⟨randomness, rfl⟩, hadmissible⟩, ← hview]
          have hprehit : PrehitSelectedView (onlyInputCache before input) key message (fun _ => True)
              (some (randomness, index, leaves), after) := by
            refine ⟨randomness, index, leaves, rfl, output, ?_, hattempt, trivial⟩
            simpa [onlyInputCache, input] using hbefore
          apply le_trans ?_ (le_add_left le_rfl)
          rw [← hsource]
          exact (le_of_eq (if_pos hprehit).symm).trans (ENNReal.le_tsum input)
theorem expected_selectedLoopInputWeight_le_exactReuse
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before := by
  have hexpect {α : Type} (event : α → DigestLoopRecord → Prop) (value : α → ENNReal) :
      (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ∑' index, if event index result then value index else 0) =
      ∑' index, Pr[event index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * value index := by
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro index
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro result
    split_ifs <;> simp
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ((∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
          ∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
            cachedSignerInputWeight key message before weight input else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
      · exact mul_le_mul' le_rfl (selectedLoopInputWeight_le_fresh_add_prehit key message before weight uniformWeight hweight result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' view, Pr[FreshSelectedView before key message (· = view) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * uniformWeight view) +
        ∑' input, Pr[PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
            cachedSignerInputWeight key message before weight input := by
      simp only [mul_add, ENNReal.tsum_add, hexpect]
    _ ≤ (∑' view, (freshDigestSelectionProbability key message before *
          Pr[= view | signerViewSample]) * uniformWeight view) +
        ∑' input, exactDigestReuseWeight key message before * cachedSignerInputWeight key message before weight input := by
      apply add_le_add
      · apply ENNReal.tsum_le_tsum
        intro view
        apply mul_le_mul' _ le_rfl
        exact le_of_eq (by
          simpa only [probEvent_eq_eq_probOutput, freshDigestSelectionProbability] using
            (probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message before before (· = view)
              (onlyRejectedNewMessageEntries_self before key message)))
      · exact ENNReal.tsum_le_tsum (fun input => mul_le_mul'
          (probEvent_signDigestLoop_fixedPrehit_le_exactWeight key message before input (fun _ => True)) le_rfl)
    _ = _ := by simp only [mul_assoc, ENNReal.tsum_mul_left]; rw [mul_comm (exactDigestReuseWeight key message before)]
theorem expected_freshSelectedLoopInputWeight_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : FewTimeView → ENNReal) :
    (∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * weight source := by
  have hzero (input : HashInput) : cachedSignerInputWeight key message before
      (fun input source => if before input = none then weight source else 0) input = 0 := by
    unfold cachedSignerInputWeight
    cases hc : before input with
    | none => rfl
    | some output => simp only [hc, reduceCtorEq, if_false, ite_self]
  have hbound := expected_selectedLoopInputWeight_le_exactReuse key message before
    (fun input source => if before input = none then weight source else 0) weight (by
      intro input source
      split_ifs; exact le_rfl; exact bot_le)
  simpa only [hzero, tsum_zero, zero_mul, add_zero] using hbound
def DigestCompletionConsistent (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  result.1.2 = selectedLoopView? loop ∧
    ∀ signature, result.1.1 = some signature →
      ∃ index leaves, loop.1 = some (signature.randomness, index, leaves)
theorem successfulSignerInputWeight_le_selectedLoopInputWeight
    (key : SecretKey) (message : Message) (weight : HashInput → FewTimeView → ENNReal)
    (loop : DigestLoopRecord) (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : DigestCompletionConsistent loop result) :
    successfulSignerInputWeight key message weight result ≤ selectedLoopInputWeight key message weight loop := by
  cases hs : result.1.1 with
  | none => simp only [successfulSignerInputWeight, hs]; exact bot_le
  | some signature =>
      obtain ⟨index, leaves, hloop⟩ := hconsistent.2 signature hs
      simp only [successfulSignerInputWeight, hs, hconsistent.1, selectedLoopView?, hloop,
        Option.map_some, selectedLoopInputWeight, le_refl]
theorem expected_digestCompletion_cost_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal)
    (weight : HashInput → FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤ selectedLoopInputWeight key message weight loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop := by
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro loop
  by_cases hl : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
  · apply mul_le_mul' le_rfl
    calc
      _ ≤ ∑' result, Pr[= result | finish loop] * selectedLoopInputWeight key message weight loop := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (finish loop)
        · exact mul_le_mul' le_rfl (hcost loop hl result hr)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [probOutput_eq_zero_of_not_mem_support hl, zero_mul, zero_mul]
theorem expected_digestCompletion_successfulInputWeight_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop :=
  expected_digestCompletion_cost_le_selected key message before finish
    (fun result => successfulSignerInputWeight key message weight (record result)) weight
    (fun loop hl result hr => successfulSignerInputWeight_le_selectedLoopInputWeight
      key message weight loop (record result) (hconsistent loop hl result hr))
theorem expected_digestCompletion_freshCost_le {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal) (weight : FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤
        selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * weight source :=
  (expected_digestCompletion_cost_le_selected key message before finish cost _ hcost).trans
    (expected_freshSelectedLoopInputWeight_le key message before weight)
theorem expected_digestCompletion_successfulInputWeight_le_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before :=
  (expected_digestCompletion_successfulInputWeight_le_selected key message before finish record hconsistent weight).trans
    (expected_selectedLoopInputWeight_le_exactReuse key message before weight uniformWeight hweight)
theorem expected_digestCompletion_successfulInputWeight_le_allMessage {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      cacheMessageWeight key.parameter weight before * reuse :=
  (expected_digestCompletion_successfulInputWeight_le_exactReuse key message before finish record hconsistent
    weight uniformWeight hweight).trans (add_le_add le_rfl (mul_le_mul'
      (ENNReal.tsum_le_tsum (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before weight)) hreuse))
end SphincsSecurity.Concrete
end
end

section









section
set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem normalizedSourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset IndexGroup)
    (hdisjoint : Disjoint left right) :
    normalizedSourceSubsetMatch target source left * normalizedSourceSubsetMatch target source right =
      normalizedSourceSubsetMatch target source (left ∪ right) := by
  unfold normalizedSourceSubsetMatch
  rw [Finset.card_union_of_disjoint hdisjoint, pow_add, ← sourceSubsetMatch_mul, Nat.cast_mul]
  ring
theorem normalizedSourceSubsetMatch_singletons (target source : FewTimeView) (required : Finset IndexGroup) :
    (∏ tree ∈ required, normalizedSourceSubsetMatch target source {tree}) = normalizedSourceSubsetMatch target source required := by
  simp only [normalizedSourceSubsetMatch, sourceSubsetMatch, Finset.card_singleton, pow_one,
    Finset.prod_singleton, Finset.prod_mul_distrib, Finset.prod_const, Nat.cast_prod]
noncomputable def targetCacheArrivalPolynomial (cached : Fin m → ENNReal) (groups : Fin m → Finset IndexGroup)
    (target source : FewTimeView) : ENNReal :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
      ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot
theorem targetCacheProduct_add_arrival (cached : Fin m → ENNReal) (groups : Fin m → Finset IndexGroup)
    (target source : FewTimeView) :
    (∏ slot : Fin m, cached slot) + targetCacheArrivalPolynomial cached groups target source =
      ∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot)) := by
  rw [show (∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot))) =
    ∏ slot : Fin m, (normalizedSourceSubsetMatch target source (groups slot) + cached slot) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul, targetCacheArrivalPolynomial]
theorem targetLogProduct_insert_expansion (logged : IndexGroup → ENNReal) (required : Finset IndexGroup) (target source : FewTimeView) :
    (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
      ∑ selected ∈ required.powerset, normalizedSourceSubsetMatch target source selected *
        ∏ tree ∈ required \ selected, logged tree := by
  rw [show (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
    ∏ tree ∈ required, (normalizedSourceSubsetMatch target source {tree} + logged tree) by simp only [add_comm]]
  rw [Finset.prod_add]
  simp only [normalizedSourceSubsetMatch_singletons]
noncomputable def targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : IndexGroup → ENNReal)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (target source : FewTimeView) : ENNReal :=
  targetCacheArrivalPolynomial cached groups target source *
    ∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})
theorem expected_targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : IndexGroup → ENNReal)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (target : FewTimeView)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required) :
    (∑' source, Pr[= source | signerViewSample] *
      targetMixedGrowthPolynomial cached logged groups required target source) =
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          ∑ trees ∈ required.powerset,
            signerRate target (selected.biUnion groups ∪ trees) *
              ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
                ∏ tree ∈ required \ trees, logged tree) := by
  simp only [targetMixedGrowthPolynomial, targetCacheArrivalPolynomial, targetLogProduct_insert_expansion]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro trees htrees
  have hselectedNonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  have hpair : (selected : Set (Fin m)).PairwiseDisjoint groups := fun i _ j _ hij => hdisjoint hij
  have hsep : Disjoint (selected.biUnion groups) trees := by
    rw [Finset.disjoint_biUnion_left]
    intro slot _
    exact (hremaining slot).mono_right (Finset.mem_powerset.mp htrees)
  have hpoint (source : FewTimeView) :
      (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
        (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
          (normalizedSourceSubsetMatch target source trees * ∏ tree ∈ required \ trees, logged tree) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups ∪ trees) *
        ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) * ∏ tree ∈ required \ trees, logged tree) := by
    rw [normalizedSourceSubsetMatch_prod target source groups selected hpair, ← normalizedSourceSubsetMatch_mul target source _ _ hsep]
    ring
  simp only [hpoint, ← mul_assoc, ENNReal.tsum_mul_right]
  rfl
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) : ENNReal :=
  ∑ selected ∈ required.powerset.erase ∅, normalizedSourceSubsetMatch target source selected *
    normalizedTargetLogProduct key cache log payload target (required \ selected)
theorem normalizedTargetLogProduct_add_increment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) :
    normalizedTargetLogProduct key cache log payload target required + normalizedTargetLogIncrement key cache log payload target required source =
      ∏ tree ∈ required, (normalizedTargetLogMatch key cache log payload target tree + normalizedSourceSubsetMatch target source {tree}) := by
  rw [targetLogProduct_insert_expansion, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset required)]
  simp only [normalizedSourceSubsetMatch, Finset.card_empty, pow_zero, sourceSubsetMatch,
    Finset.prod_empty, Nat.cast_one, one_mul, Finset.sdiff_empty, normalizedTargetLogIncrement, normalizedTargetLogProduct]
theorem normalizedTargetLogProduct_append_none (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none) :
    normalizedTargetLogProduct key after (log ++ [entry]) payload target required =
      normalizedTargetLogProduct key before log payload target required := by
  apply Finset.prod_congr rfl
  intro tree _
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero,
    eligibleSigningViews_cache_stable key before after log payload hcache hsigned] at hstep
  exact congrArg (fun count : Nat => coverNormalization * (count : ENNReal)) hstep
theorem expected_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    (∑' source, Pr[= source | signerViewSample] * normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        signerRate target selected * normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  simp only [normalizedTargetLogIncrement, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  rfl
theorem cached_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    cacheMessageWeight key.parameter (fun input source => if input = tweakableHashInput key.parameter .message payload then 0
      else normalizedTargetLogIncrement key cache log payload target required source) cache =
      ∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  have hpoint (input : HashInput) (source : FewTimeView) :
      (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedSourceSubsetMatch target source selected) *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
    unfold normalizedTargetLogIncrement
    split_ifs <;> simp only [zero_mul, Finset.sum_const_zero]
  simp only [hpoint, cacheMessageWeight_sum, cacheMessageWeight_mul_right, normalizedCachedTargetSubsetMatch_eq_weight]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem signDigestLoop_selected_cached_output (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = selectedFewTimeView index leaves := by
  have hreplay := replayRom_of_mem_support (signDigestLoop attempts key message) before
    (some (randomness, index, leaves)) after hloop (fromCache after) (agreesWithFn_fromCache after)
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message attempts randomness index leaves
    before after after hreplay le_rfl (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, houtput, hdigest ▸ hadmissible, ?_⟩
  simp only [hashOutputFewTimeView, fullDigestView, selectedFewTimeView, ← hdigest, hindex, hleaves]
theorem signAfterDigest_message_cache_eq (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (before after : QueryCache HashSpec) (signature : Option Signature)
    (hfinish : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) (payload : HashInput) :
    after (tweakableHashInput key.parameter .message payload) = before (tweakableHashInput key.parameter .message payload) := by
  cases hbefore : before (tweakableHashInput key.parameter .message payload) with
  | none => exact signAfterDigest_cache_message_none key randomness index leaves before after signature hfinish payload hbefore
  | some output =>
      have hcache : before ≤ after :=
        (replay_of_mem_support (signAfterDigest key randomness index leaves) before signature after hfinish
          (fromCache after) (agreesWithFn_fromCache after)).1
      exact hcache hbefore
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signWithView
def DigestCompletionPreservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  DigestCompletionConsistent loop result ∧ messageAnswers key.parameter result.2 = messageAnswers key.parameter loop.2
theorem digestCompletion_successful_cached_output (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (signature : Signature) (hs : result.1.1 = some signature) :
    ∃ output, result.2 (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message signature.randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ result.1.2 = some (hashOutputFewTimeView output) := by
  obtain ⟨index, leaves, hselected⟩ := hcompletion.1.2 signature hs
  have hloop' : (some (signature.randomness, index, leaves), loop.2) ∈ support
      ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before) := by
    have heq : loop = (some (signature.randomness, index, leaves), loop.2) := Prod.ext hselected rfl
    rwa [← heq]
  obtain ⟨output, hcached, hadmissible, hview⟩ := signDigestLoop_selected_cached_output
    digestAttemptLimit key message before loop.2 signature.randomness index leaves hloop'
  refine ⟨output, ?_, hadmissible, ?_⟩
  · exact (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).trans hcached
  · simp only [hcompletion.1.1, selectedLoopView?, hselected, Option.map_some, ← hview]
noncomputable def originalDigestCompletion (key : SecretKey) (loop : DigestLoopRecord) :
    ProbComp ((Option Signature × Option FewTimeView) × QueryCache HashSpec) :=
  match loop.1 with
  | none => pure ((none, none), loop.2)
  | some (randomness, index, leaves) =>
      (fun result => ((result.1, some (selectedFewTimeView index leaves)), result.2)) <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2
theorem signWithView_run_eq_digestCompletion (key : SecretKey) (message : Message) (before : QueryCache HashSpec) :
    (simulateQ romImpl (signWithView key message)).run before =
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= originalDigestCompletion key := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro loop
  cases hl : loop.1 with
  | none => simp only [originalDigestCompletion, hl, simulateQ_pure, StateT.run_pure]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        simulateQ_romImpl_liftM, map_eq_bind_pure_comp]
      rfl
theorem originalDigestCompletion_preservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hr : result ∈ support (originalDigestCompletion key loop)) :
    DigestCompletionPreservesMessages key loop result := by
  cases hl : loop.1 with
  | none =>
      have heq : result = ((none, none), loop.2) := by
        simpa only [originalDigestCompletion, hl, support_pure, Set.mem_singleton_iff] using hr
      subst result
      simp only [DigestCompletionPreservesMessages, DigestCompletionConsistent, selectedLoopView?, hl,
        Option.map_none, reduceCtorEq, false_implies, implies_true, and_self]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, support_map] at hr
      obtain ⟨⟨signature, after⟩, hfinish, rfl⟩ := hr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [selectedLoopView?, hl, Option.map_some]
      · intro successful hs
        have hfinish' : (some successful, after) ∈ support
            ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2) := by
          rwa [← hs]
        have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loop.2 after successful hfinish'
        exact ⟨index, leaves, by simpa only [hrandomness] using hl⟩
      · funext payload
        exact signAfterDigest_message_cache_eq key randomness index leaves loop.2 after signature hfinish payload
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem digestCompletion_normalizedTargetLogProduct_le_input
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message (fun input source =>
          if input = tweakableHashInput key.parameter .message payload then 0
          else normalizedTargetLogIncrement key before log payload target required source) result := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have hproject : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩]) payload target required := by
    unfold normalizedTargetLogProduct normalizedTargetLogMatch
    rw [hcompletion.2]
  rw [hproject]
  cases hs : result.1.1 with
  | none =>
      rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
        (by simp [eligibleSigningView?])]
      simp only [successfulSignerInputWeight, hs, add_zero, le_refl]
  | some signature =>
      obtain ⟨output, houtput, _, hview⟩ := digestCompletion_successful_cached_output key message before loop hloop result hcompletion signature hs
      have hcached : loop.2 (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message signature.randomness)) = some output :=
        (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).symm.trans houtput
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
          (by simp [eligibleSigningView?, hsame])]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        simp only [successfulSignerInputWeight, hs, hview, if_neg hinput]
        rw [normalizedTargetLogProduct_add_increment]
        apply Finset.prod_le_prod'
        intro tree _
        exact normalizedTargetLogMatch_le_of_eligibleView key before loop.2 log ⟨message, some signature⟩ payload target
          (hashOutputFewTimeView output) tree hcache hsigned (Or.inr (by
            simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, hcached]))
theorem expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetLogProduct key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
          (∑ selected ∈ required.powerset.erase ∅,
            signerRate target selected * normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * reuse := by
  let computation := (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  have hweight (input : HashInput) (source : FewTimeView) :
      weight input source ≤ normalizedTargetLogIncrement key before log payload target required source := by
    unfold weight
    split_ifs; exact bot_le; exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (normalizedTargetLogProduct key before log payload target required + successfulSignerInputWeight key message weight (record result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · change result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨loop, hl, hf⟩ := hr
        exact mul_le_mul' le_rfl (digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required
          hsigned loop hl (record result) (hcompletion loop hl result hf))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        ∑' result, Pr[= result | computation] * successfulSignerInputWeight key message weight (record result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ _ := by
      have hbound := (expected_digestCompletion_successfulInputWeight_le_allMessage key message before finish record
        (fun loop hl result hr => (hcompletion loop hl result hr).1) weight _ hweight reuse hreuse).trans
          (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)
      simp only [weight, expected_normalizedTargetLogIncrement, cached_normalizedTargetLogIncrement] at hbound
      simpa only [add_assoc, computation, weight] using add_le_add
        (le_refl (normalizedTargetLogProduct key before log payload target required)) hbound
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cacheMessageWeight_of_no_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after)
    (hnoNew : ∀ input output, before input = none → MessageHashInput parameter input → after input = some output →
      ¬ Admissible (truncateMessageDigest output)) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  have hzero : cacheMessageWeight parameter (fun input source => if before input = none then weight input source else 0) after = 0 := by
    unfold cacheMessageWeight
    apply ENNReal.tsum_eq_zero.mpr
    intro input
    unfold cacheMessageEntryWeight
    cases houtput : after input with
    | none => rfl
    | some output =>
        simp only
        by_cases hgood : MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output)
        · rw [if_pos hgood]
          by_cases hfresh : before input = none
          · exact (hnoNew input output hfresh hgood.1 houtput hgood.2).elim
          · simp only [hfresh, if_false]
        · simp only [hgood, if_false]
  rw [hzero, add_zero]
theorem cacheMessageWeight_of_single_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : MessageHashInput parameter input) (hafter : after input = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (hunique : ∀ other answer, before other = none → MessageHashInput parameter other → after other = some answer →
      Admissible (truncateMessageDigest answer) → other = input) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before + weight input (hashOutputFewTimeView output) := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  congr 1
  unfold cacheMessageWeight
  rw [tsum_eq_single input]
  · simp only [cacheMessageEntryWeight, hafter, hmessage, hadmissible, and_self, if_true, hfresh]
  · intro other hne
    unfold cacheMessageEntryWeight
    cases hanswer : after other with
    | none => rfl
    | some answer =>
        simp only
        by_cases hgood : MessageHashInput parameter other ∧ Admissible (truncateMessageDigest answer)
        · rw [if_pos hgood]
          by_cases hbefore : before other = none
          · exact (hne (hunique other answer hbefore hgood.1 hanswer hgood.2)).elim
          · simp only [hbefore, if_false]
        · simp only [hgood, if_false]
end SphincsSecurity.Concrete
end
section
set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem signDigestLoop_new_payload_eq_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message randomness := by
  obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
  have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
  exact hpayload.trans (congrArg _ hrandomness.symm)
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def targetMixedSigningGrowth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) : ENNReal :=
  (normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups -
    normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups) *
      normalizedTargetLogProduct key after log payload target required
noncomputable def newTargetMixedGrowthWeight (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (source : FewTimeView) : ENNReal :=
  targetMixedGrowthPolynomial
    (fun slot => normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot))
    (normalizedTargetLogMatch key before log payload target) groups required target source
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem signDigestLoop_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight loop.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  obtain ⟨selected, after⟩ := loop
  cases selected with
  | none =>
      simp only [selectedLoopInputWeight, add_zero]
      apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
      intro input output hfresh hmessage hafter hadmissible
      obtain ⟨payload, rfl⟩ := hmessage
      obtain ⟨_, _, _, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
        before after none hloop payload output hfresh hafter hadmissible
      contradiction
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · obtain ⟨output, houtput, hadmissible, hview⟩ := signDigestLoop_selected_cached_output digestAttemptLimit key message
          before after randomness index leaves hloop
        simp only [selectedLoopInputWeight, hfresh, if_true]
        rw [← hview]
        apply cacheMessageWeight_of_single_new key.parameter weight before after hcache _ output hfresh
          ⟨messageDigestPayload key.root message randomness, rfl⟩ houtput hadmissible
        intro other answer hbefore hmessage hafter hgood
        obtain ⟨payload, rfl⟩ := hmessage
        exact congrArg (tweakableHashInput key.parameter .message)
          (signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after randomness index leaves hloop
            payload answer hbefore hafter hgood)
      · simp only [selectedLoopInputWeight, if_neg hfresh, add_zero]
        apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
        intro input output hbefore hmessage hafter hadmissible
        obtain ⟨payload, rfl⟩ := hmessage
        have hpayload := signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after
          randomness index leaves hloop payload output hbefore hafter hadmissible
        exact hfresh (hpayload ▸ hbefore)
theorem digestCompletion_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight result.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  rw [cacheMessageWeight_messageAnswers_congr key.parameter result.2 loop.2 hcompletion.2]
  exact signDigestLoop_cacheMessageWeight_eq key message before loop hloop weight
theorem digestCompletion_targetCacheProduct_le_of_fresh (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) :
    normalizedTargetCacheProduct key.parameter result.2 targetInput target groups ≤
      normalizedTargetCacheProduct key.parameter before targetInput target groups +
        targetCacheArrivalPolynomial (fun slot => normalizedCachedTargetSubsetMatch key.parameter before targetInput target (groups slot))
          groups target (selectedFewTimeView index leaves) := by
  unfold normalizedTargetCacheProduct
  rw [targetCacheProduct_add_arrival]
  apply Finset.prod_le_prod'
  intro slot _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
  apply add_le_add le_rfl
  split_ifs; exact bot_le; exact le_rfl
theorem digestCompletion_targetLogProduct_le_view (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves)) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      ∏ tree ∈ required, (normalizedTargetLogMatch key before log payload target tree +
        normalizedSourceSubsetMatch target (selectedFewTimeView index leaves) {tree}) := by
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  calc
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message weight result :=
      digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required hsigned loop hloop result hcompletion
    _ ≤ normalizedTargetLogProduct key before log payload target required + selectedLoopInputWeight key message weight loop :=
      add_le_add le_rfl (successfulSignerInputWeight_le_selectedLoopInputWeight key message weight loop result hcompletion.1)
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        normalizedTargetLogIncrement key before log payload target required (selectedFewTimeView index leaves) := by
      apply add_le_add le_rfl
      simp only [selectedLoopInputWeight, hselected, weight]
      split_ifs; exact bot_le; exact le_rfl
    _ = _ := normalizedTargetLogProduct_add_increment key before log payload target required (selectedFewTimeView index leaves)
theorem digestCompletion_targetMixedGrowth_le_freshInput (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required ≤
      selectedLoopInputWeight key message (fun input source => if before input = none then
        newTargetMixedGrowthWeight key before log payload target groups required source else 0) loop := by
  by_cases hnew : ∃ randomness index leaves, loop.1 = some (randomness, index, leaves) ∧
      before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
  · obtain ⟨randomness, index, leaves, hselected, hfresh⟩ := hnew
    have hproduct := digestCompletion_targetCacheProduct_le_of_fresh key message before loop hloop result hcompletion
      randomness index leaves hselected hfresh (tweakableHashInput key.parameter .message payload) target groups
    have hlog := digestCompletion_targetLogProduct_le_view key message before log payload target required hsigned loop hloop result hcompletion
      randomness index leaves hselected
    simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
    exact mul_le_mul' (tsub_le_iff_right.mpr (hproduct.trans_eq (add_comm _ _))) hlog
  · have hzero (weight : HashInput → FewTimeView → ENNReal) : selectedLoopInputWeight key message
        (fun input source => if before input = none then weight input source else 0) loop = 0 := by
      cases hs : loop.1 with
      | none => simp only [selectedLoopInputWeight, hs]
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ≠ none :=
            fun hc => hnew ⟨randomness, index, leaves, hs, hc⟩
          simp only [selectedLoopInputWeight, hs, if_neg hfresh]
    have hcounts (slot : Fin m) : normalizedCachedTargetSubsetMatch key.parameter result.2
        (tweakableHashInput key.parameter .message payload) target (groups slot) =
        normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot) := by
      simp only [normalizedCachedTargetSubsetMatch_eq_weight]
      rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion, hzero, add_zero]
    simp only [targetMixedSigningGrowth, normalizedTargetCacheProduct, hcounts, tsub_self, zero_mul, zero_le]
theorem expected_digestCompletion_targetMixedGrowth_le_freshMass {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      targetMixedSigningGrowth key before (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * newTargetMixedGrowthWeight key before log payload target groups required source :=
  expected_digestCompletion_freshCost_le key message before finish _ _ (fun loop hl result hr =>
    digestCompletion_targetMixedGrowth_le_freshInput key message before log payload target groups required hsigned
      loop hl (record result) (hcompletion loop hl result hr))
end SphincsSecurity.Concrete
end
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_DigestCompletionNewTarget ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem expected_uniformFewTimeView_eq_leafAverage (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target) =
      (Fintype.card Index : ENNReal)⁻¹ * ∑ index : Index, leafAverage (fun leaves => f (index, leaves)) := by
  simp only [probOutput_uniformFewTimeView, tsum_fintype, Fintype.sum_prod_type, leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro leaves _
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  ring
theorem expected_signerViewSample_le (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | signerViewSample] * f target) ≤
      admissibleProbability⁻¹ * ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro target
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  have h := probOutput_uniformFewTimeView_admissible target
  have hle : admissibleProbability * Pr[= target | signerViewSample] ≤
      Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
    rw [← h]
    split_ifs <;> simp
  calc
    Pr[= target | signerViewSample] =
        admissibleProbability⁻¹ * (admissibleProbability * Pr[= target | signerViewSample]) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel admissibleProbability_pos admissibleProbability_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hle
theorem expected_fresh_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card := by
  rw [expected_uniformFewTimeView_eq_leafAverage]
  apply mul_le_mul' le_rfl
  rw [← targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
  calc
    _ ≤ ∑ index : Index, targetShapeEnvelope (constRate (Fintype.card Index : ENNReal)⁻¹) reuse (constRate cachedIndexRate)
        queries signings (liftTargetIndexVector (indexPowerMoments key cache log index)) groups remaining := by
      apply Finset.sum_le_sum
      intro index _
      have hfubini := leafAverage_targetShapeEnvelope_le (L := FtsLeaf)
        (F := fun leaves => targetShapeMoments key cache log payload (index, leaves))
        (rate := fun leaves => signerRate (index, leaves)) (arrival := fun leaves => arrivalRate (index, leaves)) reuse
        (targetShapeMoments_shapeLocal key cache log payload index) (signerRate_local index) (arrivalRate_local index)
        (fun coords hne => leafAverage_signerRate_le index coords hne)
        (fun coords hne => leafAverage_arrivalRate_le index coords hne) queries signings groups remaining hvalid
      refine hfubini.trans ?_
      exact targetShapeEnvelope_mono _ _ _ queries signings
        (averagedShape_targetShapeMoments_le key cache log payload hfresh hsigned index) groups remaining hvalid
    _ = _ := by
      have hsum : liftTargetIndexVector (targetIndexMoments key cache log) =
          fun G R => ∑' index : Index, liftTargetIndexVector (indexPowerMoments key cache log index) G R := by
        funext G R
        simp only [liftTargetIndexVector, targetIndexMoments, indexPowerMoments, tsum_fintype]
      rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]
theorem targetShapeMoments_cacheQuery_self_vector (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload target =
      targetShapeMoments key before log payload target := by
  funext groups remaining
  exact targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining _ output hfresh hsigned (Or.inr rfl)
theorem expected_cacheQuery_freshTargetEnvelope_le (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        targetShapeEnvelope (signerRate (hashOutputFewTimeView output)) reuse (arrivalRate (hashOutputFewTimeView output))
          queries signings
          (targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload
            (hashOutputFewTimeView output)) groups remaining else 0)) ≤
      (Fintype.card Index : ENNReal)⁻¹ *
        targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
          (targetIndexMoments key before log) groups.card remaining.card := by
  simp only [targetShapeMoments_cacheQuery_self_vector key before log payload _ _ hfresh hsigned]
  exact (expected_uniformHashOutput_admissible_weight_le_uniform
    (fun target => targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
      (targetShapeMoments key before log payload target) groups remaining)).trans
    (expected_fresh_targetShapeEnvelope_le key before log payload hfresh hsigned reuse queries signings groups remaining hvalid)
theorem expected_signer_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | signerViewSample] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card) :=
  (expected_signerViewSample_le _).trans (mul_le_mul' le_rfl
    (expected_fresh_targetShapeEnvelope_le key cache log payload hfresh hsigned reuse queries signings groups remaining hvalid))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cacheMessageWeight_exclude_fresh (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (hfresh : cache targetInput = none) (weight : FewTimeView → ENNReal) :
    cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else weight source) cache =
      cacheMessageWeight parameter (fun _ source => weight source) cache := by
  unfold cacheMessageWeight
  apply tsum_congr
  intro input
  by_cases heq : input = targetInput
  · subst input
    simp only [cacheMessageEntryWeight, hfresh]
  · unfold cacheMessageEntryWeight
    cases cache input <;> simp only [heq, if_false]
theorem targetShapeMoments_fresh_payload_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (first second : HashInput)
    (hfirst : cache (tweakableHashInput key.parameter .message first) = none)
    (hsecond : cache (tweakableHashInput key.parameter .message second) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (target : FewTimeView) :
    targetShapeMoments key cache log first target = targetShapeMoments key cache log second target := by
  funext groups remaining
  unfold targetShapeMoments normalizedTargetLogProduct normalizedTargetLogMatch
  simp only [normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hfirst,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hsecond,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log first hfirst hsigned,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log second hsecond hsigned]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def newTargetEnvelopeCharge (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => if before input = none then
    targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
      (targetShapeMoments key after log (payloadOf input) target) groups remaining else 0) after
theorem newTargetEnvelopeCharge_of_no_new (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hnone : ∀ payload output, before (tweakableHashInput key.parameter .message payload) = none →
      after (tweakableHashInput key.parameter .message payload) = some output → ¬ Admissible (truncateMessageDigest output)) :
    newTargetEnvelopeCharge key before after log reuse queries signings groups remaining = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases houtput : after input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood hfresh
      · obtain ⟨payload, rfl⟩ := hgood.1
        exact (hnone payload output hfresh houtput hgood.2).elim
      · rfl
      · rfl
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem digestCompletion_new_targetShapeMoments_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (target : FewTimeView) :
    targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target =
      targetShapeMoments key before log (messageDigestPayload key.root message randomness) target := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have heligible : eligibleSigningView? (messageAnswers key.parameter loop.2) key.root
      (messageDigestPayload key.root message randomness) ⟨message, result.1.1⟩ = none := by
    cases hs : result.1.1 with
    | none => simp [eligibleSigningView?]
    | some signature =>
        obtain ⟨otherIndex, otherLeaves, hother⟩ := hcompletion.1.2 signature hs
        have hr : signature.randomness = randomness := congrArg Prod.fst (Option.some.inj (hother.symm.trans hselected))
        simp [eligibleSigningView?, hr]
  have hlog (required : Finset IndexGroup) :
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target required =
        normalizedTargetLogProduct key before log (messageDigestPayload key.root message randomness) target required := by
    have heq : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required := by
      unfold normalizedTargetLogProduct normalizedTargetLogMatch
      rw [hcompletion.2]
    rw [heq]
    exact normalizedTargetLogProduct_append_none key before loop.2 log _ _ target required hcache hsigned heligible
  funext groups remaining
  unfold targetShapeMoments
  rw [hlog]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true, add_zero]
theorem digestCompletion_newTargetEnvelopeCharge_eq_selected
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) reuse queries signings groups remaining =
      selectedLoopInputWeight key message (fun input target => if before input = none then
        targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
          (targetShapeMoments key before log (payloadOf input) target) groups remaining else 0) loop := by
  unfold newTargetEnvelopeCharge
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion,
    cacheMessageWeight_fresh_restriction, zero_add]
  cases hs : loop.1 with
  | none => simp only [selectedLoopInputWeight, hs]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput]
        rw [digestCompletion_new_targetShapeMoments_eq key message before loop hloop result hcompletion
          log hsigned randomness index leaves hs hfresh]
      · simp only [selectedLoopInputWeight, hs, if_neg hfresh]
theorem expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining) ≤
      freshDigestSelectionProbability key message before *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key before log) groups.card remaining.card)) := by
  by_cases hexists : ∃ payload, before (tweakableHashInput key.parameter .message payload) = none
  · obtain ⟨reference, hreference⟩ := hexists
    let weight := fun source => targetShapeEnvelope (signerRate source) reuse (arrivalRate source) queries signings
      (targetShapeMoments key before log reference source) groups remaining
    have hbound := expected_digestCompletion_freshCost_le key message before finish
      (fun result => newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining) weight (by
          intro loop hl result hr
          rw [digestCompletion_newTargetEnvelopeCharge_eq_selected key message before loop hl (record result)
            (hcompletion loop hl result hr) log hsigned]
          cases hs : loop.1 with
          | none => simp only [selectedLoopInputWeight, hs, le_refl]
          | some selected =>
              obtain ⟨randomness, index, leaves⟩ := selected
              by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
              · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput, weight]
                rw [targetShapeMoments_fresh_payload_eq key before log _ reference hfresh hreference hsigned]
              · simp only [selectedLoopInputWeight, hs, if_neg hfresh, le_refl])
    exact hbound.trans (mul_le_mul' le_rfl
      (expected_signer_targetShapeEnvelope_le key before log reference hreference hsigned
        reuse queries signings groups remaining hvalid))
  · have hzero (result : α) : newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining = 0 :=
      newTargetEnvelopeCharge_of_no_new key before (record result).2 _ reuse queries signings groups remaining
        (fun payload _ hfresh _ _ => hexists ⟨payload, hfresh⟩)
    simp only [hzero, mul_zero, tsum_zero, zero_le]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_ExactTargetShapeSigning ====
section

set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def observedTargetShapeVector (key : SecretKey) (payload : HashInput) (target : FewTimeView) (state : CoverLogState) : TargetShapeVector :=
  targetShapeMoments key state.1 state.2 payload target
theorem expected_fresh_targetShape_le (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      observedTargetShapeVector key payload target (before.cacheQuery input output, log) groups remaining) ≤
        targetShapeQuery (arrivalRate target)
          (observedTargetShapeVector key payload target (before, log)) groups remaining := by
  have h := expected_randomOracle_targetShapeMoments_le key before log payload target groups remaining hvalid input hsigned
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul] at h
  exact h
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def reuseTargetMixedSigningEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (reuse : ENNReal) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    (normalizedTargetLogProduct key cache log payload target required +
      (∑ selected ∈ required.powerset.erase ∅,
        signerRate target selected * normalizedTargetLogProduct key cache log payload target (required \ selected)) +
      (∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected)) * reuse) +
      ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
        ∑ trees ∈ required.powerset,
          signerRate target (selected.biUnion groups ∪ trees) *
            ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected,
              normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target (groups slot)) *
                normalizedTargetLogProduct key cache log payload target (required \ trees))
theorem digestCompletion_normalizedTargetMixedMoment_eq_frozen_add_growth (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) :
    normalizedTargetMixedMoment key result.2 log payload target groups required =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        normalizedTargetLogProduct key result.2 log payload target required +
          targetMixedSigningGrowth key before result.2 log payload target groups required := by
  have hmono : normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups ≤
      normalizedTargetCacheProduct key.parameter result.2 (tweakableHashInput key.parameter .message payload) target groups := by
    apply Finset.prod_le_prod'
    intro slot _
    simp only [normalizedCachedTargetSubsetMatch_eq_weight]
    rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
    exact le_self_add
  unfold normalizedTargetMixedMoment targetMixedSigningGrowth
  rw [← add_mul, add_tsub_cancel_of_le hmono]
theorem expected_digestCompletion_normalizedTargetMixedMoment_le_of_exactReuse {α : Type} (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetMixedMoment key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) ≤
      reuseTargetMixedSigningEnvelope key before log payload target groups required reuse := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetMixedMoment key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) =
      normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups *
        (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
          normalizedTargetLogProduct key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target required) +
      ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
        targetMixedSigningGrowth key before (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish)
    · rw [mem_support_bind_iff] at hresult
      obtain ⟨loop, hl, hr⟩ := hresult
      rw [digestCompletion_normalizedTargetMixedMoment_eq_frozen_add_growth key message before loop hl (record result)
        (hcompletion loop hl result hr) _ payload target groups required]
      ring
    · rw [probOutput_eq_zero_of_not_mem_support hresult]
      simp only [zero_mul, mul_zero, add_zero]
  rw [heq]
  apply add_le_add
  · exact mul_le_mul' le_rfl (expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse key message before finish record hcompletion log payload target required hsigned reuse hreuse)
  · apply ((expected_digestCompletion_targetMixedGrowth_le_freshMass key message before finish record hcompletion
      log payload target groups required hsigned).trans
        (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))).trans_eq
    exact expected_targetMixedGrowthPolynomial _ _ groups required target hgroups hdisjoint hremaining
theorem targetShapeSigning_eq_reuseIndexedEnvelope (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) (reuse : ENNReal) :
    targetShapeSigning (signerRate target) reuse
      (targetShapeMoments key cache log payload target) groups remaining =
        reuseTargetMixedSigningEnvelope key cache log payload target (targetGroupAt groups) remaining reuse := by
  let cached : Finset IndexGroup → ENNReal := fun group => normalizedCachedTargetSubsetMatch key.parameter cache
    (tweakableHashInput key.parameter .message payload) target group
  let logged : Finset IndexGroup → ENNReal := fun required => normalizedTargetLogProduct key cache log payload target required
  have hmoments (kept : Finset (Finset IndexGroup)) (required : Finset IndexGroup) :
      targetShapeMoments key cache log payload target kept required = (∏ group ∈ kept, cached group) * logged required := rfl
  have hfirst : (∑ selected ∈ remaining.powerset,
      if (∅ : Finset (Finset IndexGroup)) = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        signerRate target (groupCoordinates ∅ ∪ selected) *
          targetShapeMoments key cache log payload target (groups \ ∅) (remaining \ selected)) =
      (∏ group ∈ groups, cached group) *
        ∑ selected ∈ remaining.powerset.erase ∅, signerRate target selected * logged (remaining \ selected) := by
    rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset remaining), if_pos ⟨rfl, rfl⟩, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected hselected
    rw [if_neg (fun h => (Finset.mem_erase.mp hselected).1 h.2), Finset.sdiff_empty, hmoments]
    simp only [groupCoordinates, Finset.biUnion_empty, Finset.empty_union]
    ring
  have hrest : (∑ removed ∈ groups.powerset.erase ∅, ∑ selected ∈ remaining.powerset,
      if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        signerRate target (groupCoordinates removed ∪ selected) *
          targetShapeMoments key cache log payload target (groups \ removed) (remaining \ selected)) =
      ∑ selected ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
        ∑ trees ∈ remaining.powerset,
          signerRate target (selected.biUnion (targetGroupAt groups) ∪ trees) *
            ((∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ selected, cached (targetGroupAt groups slot)) *
              logged (remaining \ trees)) := by
    rw [← sum_targetGroupAt_nonempty groups]
    apply Finset.sum_congr rfl
    intro selected hselected
    have hne : selected.image (targetGroupAt groups) ≠ ∅ := by
      intro h
      exact (Finset.mem_erase.mp hselected).1 (Finset.image_eq_empty.mp h)
    apply Finset.sum_congr rfl
    intro trees _
    rw [if_neg (fun h => hne h.1), hmoments, prod_targetGroupAt_compl, biUnion_targetGroupAt]
    rfl
  unfold targetShapeSigning targetFreshStep
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset groups), hfirst, hrest,
    targetShapeMoments_reuse_eq key cache log payload target groups remaining hvalid]
  unfold reuseTargetMixedSigningEnvelope
  simp only [normalizedTargetCacheProduct, prod_targetGroupAt, hmoments]
  ring
theorem expected_digestCompletion_targetShapeMoments_le_of_exactReuse {α : Type} (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      targetShapeMoments key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups remaining) ≤
        targetShapeSigning (signerRate target) reuse
          (targetShapeMoments key before log payload target) groups remaining := by
  simp only [targetShapeMoments_eq_indexed]
  rw [targetShapeSigning_eq_reuseIndexedEnvelope key before log payload target groups remaining hvalid reuse]
  exact expected_digestCompletion_normalizedTargetMixedMoment_le_of_exactReuse key message before finish record hcompletion log payload target (targetGroupAt groups) remaining
    (fun slot => hvalid.nonempty _ (targetGroupAt_mem groups slot))
    (fun i j hij => hvalid.disjoint _ (targetGroupAt_mem groups i) _ (targetGroupAt_mem groups j)
      (fun heq => hij (targetGroupAt_injective groups heq)))
    (fun slot => hvalid.remaining _ (targetGroupAt_mem groups slot)) hsigned reuse hreuse
theorem expected_signWithView_targetShapeMoments_le_of_exactReuse (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups remaining) ≤
        targetShapeSigning (signerRate target) reuse
          (targetShapeMoments key before log payload target) groups remaining := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_targetShapeMoments_le_of_exactReuse key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log payload target groups remaining hvalid hsigned reuse hreuse
theorem expected_logTraced_sign_targetShape_le_of_exactReuse (key : SecretKey) (reuse : ENNReal)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (message : Message) (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedTargetShapeVector key payload target result.2 groups remaining) ≤
        targetShapeSigning (signerRate target) reuse
          (observedTargetShapeVector key payload target state) groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  have heq := congrArg (fun computation : ProbComp (Option Signature × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] *
      observedTargetShapeVector key payload target (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) hrun
  rw [tsum_probOutput_map_mul] at heq
  exact heq.le.trans (expected_signWithView_targetShapeMoments_le_of_exactReuse key message state.1 state.2
    payload target groups remaining hvalid hsigned reuse hreuse)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_BoundaryTrace ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
abbrev SigningBoundaryTrace := FreeMonoid (Option (HashInput × HashOutput))
noncomputable def signingBoundaryTrace (parameter : PublicParameter) :
    (input : OracleWorld.Domain) → OracleWorld.Range input → SigningBoundaryTrace
  | .inl _, _ => 1
  | .inr input, output => FreeMonoid.of
      (if FtsProbeSimulation.MessageHashInput parameter input then some (input, output) else none)
def SigningBoundaryTrace.hashCalls (trace : SigningBoundaryTrace) : Nat := trace.toList.length
def SigningBoundaryTrace.messageCalls (trace : SigningBoundaryTrace) : List (HashInput × HashOutput) :=
  trace.toList.filterMap id
theorem signingBoundaryTrace_nonmessage (parameter : PublicParameter) (input : HashInput) (output : HashOutput)
    (hinput : ¬ FtsProbeSimulation.MessageHashInput parameter input) :
    signingBoundaryTrace parameter (.inr input) output = FreeMonoid.of none := by
  simp only [signingBoundaryTrace, if_neg hinput]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ProposalQueryProjection ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
theorem evalDist_sampleUniformProposalWord {α : Type} [SampleableType α] [Fintype α] [Nonempty α] (steps : Nat) :
    𝒮[sampleUniformProposalWord α steps] =
      (liftM (independentProposalWord (PMF.uniformOfFintype α) steps) : SPMF (List α)) := by
  induction steps with
  | zero => simp only [sampleUniformProposalWord, independentProposalWord, evalSPMF_pure]
  | succ steps ih =>
      simp only [sampleUniformProposalWord, evalSPMF_bind, evalSPMF_pure, evalSPMF_uniformSample, ih,
        independentProposalWord, PMF.map, Function.comp_def, ← PMF.monad_bind_eq_bind, PMF.evalSPMF_eq]
      simp only [← PMF.monad_pure_eq_pure, liftM_pure]
noncomputable def targetProposalAcceptance : ENNReal := targetProposalOverhead⁻¹
theorem targetProposalAcceptance_ne_zero : targetProposalAcceptance ≠ 0 := by
  rw [targetProposalAcceptance, ENNReal.inv_ne_zero]
  unfold targetProposalOverhead
  finiteness
theorem targetProposalAcceptance_lt_one : targetProposalAcceptance < 1 := by
  rw [targetProposalAcceptance, ENNReal.inv_lt_one]
  unfold targetProposalOverhead
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem targetProposalAcceptance_cap {Ω : Type*} (record : PMF Ω) (label : Ω → Index)
    (hbound : ∀ index, (record.map label) index ≤ targetProposalIndexRate) (index : Index) :
    targetProposalAcceptance * (record.map label) index ≤ PMF.uniformOfFintype Index index := by
  rw [PMF.uniformOfFintype_apply, targetProposalAcceptance]
  calc
    _ ≤ targetProposalOverhead⁻¹ * targetProposalIndexRate := mul_le_mul' le_rfl (hbound index)
    _ = _ := by
      have hpositive : 0 < targetProposalOverhead :=
        zero_lt_one.trans (ENNReal.inv_lt_one.mp targetProposalAcceptance_lt_one)
      rw [targetProposalIndexRate, ← mul_assoc,
        ENNReal.inv_mul_cancel hpositive.ne'
          (by unfold targetProposalOverhead; finiteness), one_mul]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
private theorem probCompLift_apply {α : Type} (comp : ProbComp α) (value : α) :
    (liftM comp : PMF α) value = Pr[= value | comp] := by
  rw [← PMF.probOutput_eq_apply]
  rfl
theorem probOutput_completeSigningIndex_eq_loop (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signWithView key message)).run cache >>=
      fun result => completeSelectedIndex result.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, bind_assoc]
  apply probOutput_bind_congr
  rintro ⟨selected, loopCache⟩ _
  cases selected with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind, selectedLoopView?, Option.map_none]
  | some selected =>
      obtain ⟨randomness, selectedIndex, leaves⟩ := selected
      simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure, StateT.run_pure,
        pure_bind, selectedLoopView?, Option.map_some]
      simp
abbrev TracedSigningRecord (ω : Type) :=
  ((Option Signature × Option FewTimeView) × ω) × QueryCache HashSpec
noncomputable def tracedSigningRun {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ProbComp (TracedSigningRecord ω) :=
  ((simulateQ (romImpl.withTrace trace) (signWithView key message)).run).run cache
theorem tracedSigningRun_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result : TracedSigningRecord ω => (result.1.1, result.2)) <$>
      tracedSigningRun trace key message cache = (simulateQ romImpl (signWithView key message)).run cache := by
  have h := congrArg (fun comp : StateT (QueryCache HashSpec) ProbComp (Option Signature × Option FewTimeView) => comp.run cache)
    (QueryImpl.fst_map_run_withTrace romImpl trace (signWithView key message))
  simpa only [StateT.run_map, tracedSigningRun] using h
def signingRecordResponse {ω : Type} (result : TracedSigningRecord ω) :
    (Option Signature × ω) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2)
theorem tracedSigningRun_signature {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    signingRecordResponse <$> tracedSigningRun trace key message cache =
      ((simulateQ (romImpl.withTrace trace) (sign key message)).run).run cache := by
  change (fun result : TracedSigningRecord ω => ((result.1.1.1, result.1.2), result.2)) <$>
    tracedSigningRun trace key message cache = _
  have h := congrArg (fun comp : OracleComp OracleWorld (Option Signature) =>
    ((simulateQ (romImpl.withTrace trace) comp).run).run cache) (signWithView_fst key message)
  simpa only [simulateQ_map, WriterT.run_map, StateT.run_map, tracedSigningRun] using h
theorem probOutput_tracedSigningIndex_eq_loop {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [← probOutput_completeSigningIndex_eq_loop, ← tracedSigningRun_forget trace key message cache]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
noncomputable def completedSigningRecord {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : PMF (TracedSigningRecord ω × Index) :=
  (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)).bind fun result =>
    (liftM (completeSelectedIndex result.1.1.2) : PMF Index).map (fun index => (result, index))
theorem completedSigningRecord_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.fst =
      (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.fst = PMF.pure result := by
    rw [PMF.map_comp]
    exact PMF.map_const _ result
  simp_rw [hbranch]
  exact PMF.bind_pure _
theorem completedSigningRecord_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.snd =
      (liftM (tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2) : PMF Index) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.snd = liftM (completeSelectedIndex result.1.1.2) := by
    rw [PMF.map_comp]
    exact PMF.map_id _
  simp_rw [hbranch]
  exact (liftM_bind (m := ProbComp) (n := PMF) _ _).symm
theorem completedSigningRecord_index_le {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (spent : Nat) (hspent : spent ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ MessageDeficitExceptional key cache)
    (hindex : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) (index : Index) :
    ((completedSigningRecord trace key message cache).map Prod.snd) index ≤ targetProposalIndexRate := by
  rw [completedSigningRecord_index, probCompLift_apply, probOutput_tracedSigningIndex_eq_loop]
  exact probOutput_completeSelectedLoopIndex_le_proposalRate key message cache spent hspent hcache hclean hindex index
theorem completedSigningRecord_selected_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (record : TracedSigningRecord ω) (index : Index) (view : FewTimeView)
    (hr : (record, index) ∈ (completedSigningRecord trace key message cache).support)
    (hview : record.1.1.2 = some view) : index = view.1 := by
  rw [completedSigningRecord, PMF.mem_support_bind_iff] at hr
  obtain ⟨source, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨selected, hselected, heq⟩ := hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  simpa only [hview, completeSelectedIndex, Option.elim_some, liftM_pure,
    PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff] using hselected
structure ProposalCacheBound (key : SecretKey) (cache : QueryCache HashSpec) (spent : Nat) : Prop where
  spent_le : spent ≤ 2 ^ 127
  cache_le : QueryCache.enncard cache ≤ spent
  no_deficit : ¬ MessageDeficitExceptional key cache
  index_le : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
    (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)
theorem completedSigningRecord_acceptance_cap {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) (index : Index) :
    targetProposalAcceptance * ((completedSigningRecord trace key message cache).map Prod.snd) index ≤
      PMF.uniformOfFintype Index index :=
  targetProposalAcceptance_cap (completedSigningRecord trace key message cache) Prod.snd
    (completedSigningRecord_index_le trace key message cache spent hbound.spent_le hbound.cache_le
      hbound.no_deficit hbound.index_le) index
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
theorem independentProposalWord_length {α : Type*} (law : PMF α) (steps : Nat) :
    (independentProposalWord law steps).map List.length = PMF.pure steps := by
  induction steps with
  | zero => exact PMF.pure_map _ _
  | succ steps ih =>
      rw [independentProposalWord, PMF.map_bind]
      have hbranch (head : α) :
          ((independentProposalWord law steps).map (head :: ·)).map List.length =
            PMF.pure (steps + 1) := by
        calc
          _ = ((independentProposalWord law steps).map List.length).map Nat.succ := by
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = _ := by rw [ih, PMF.pure_map]
      simp_rw [hbranch]
      exact PMF.bind_const _ _
theorem rejectedProposalWord_length {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map List.length =
      proposalFailureCount accept hpos hle := by
  rw [rejectedProposalWord, PMF.map_bind]
  simp_rw [independentProposalWord_length]
  exact PMF.bind_pure _
noncomputable def proposalBlockLength (accept : ENNReal) (hpos : accept ≠ 0)
    (hle : accept ≤ 1) : PMF Nat :=
  (proposalFailureCount accept hpos hle).map Nat.succ
theorem proposalBlockLength_zero (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    proposalBlockLength accept hpos hle 0 = 0 :=
  pmf_map_apply_zero_of_not_image _ _ _ (fun _ => Nat.zero_ne_add_one _)
theorem proposalBlockLength_succ (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (failures : Nat) :
    proposalBlockLength accept hpos hle (failures + 1) = accept * (1 - accept) ^ failures :=
  (pmf_map_injective_apply _ _ Nat.succ_injective failures).trans rfl
theorem rejectedProposalWord_blockLength {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map (fun word => word.length + 1) =
      proposalBlockLength accept hpos hle := by
  change _ = ((proposalFailureCount accept hpos hle).map Nat.succ)
  rw [← rejectedProposalWord_length law accept hpos hle, PMF.map_comp]
  rfl
noncomputable def recordLengthBridge {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (Nat × Ω) :=
  record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (fun length => (length, outcome))
theorem recordProposalBridge_length_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map
      (fun result => (result.1.length + 1, result.2)) = recordLengthBridge record accept hpos hle := by
  rw [recordProposalBridge, PMF.map_bind]
  have hbranch (outcome : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))).map
        (fun result => (result.1.length + 1, result.2)) =
      (proposalBlockLength accept hpos hle).map (fun length => (length, outcome)) := by
    rw [← rejectedProposalWord_blockLength rejected accept hpos hle, PMF.map_comp, PMF.map_comp]
    rfl
  simp_rw [hbranch]
  rfl
theorem recordLengthBridge_record {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.snd = record := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (Function.const Nat outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]
theorem recordLengthBridge_length {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.fst = proposalBlockLength accept hpos hle := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun _ => (proposalBlockLength accept hpos hle).map id) = _
  rw [PMF.map_id, PMF.bind_const]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def pmfSumImpl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    QueryImpl (leftSpec + rightSpec) (StateT σ PMF)
  | .inl input => StateT.mk fun state => liftM ((left input).run state)
  | .inr input => StateT.mk fun state => liftM ((right input).run state)
theorem pmfSumImpl_inl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : leftSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inl input)).run state = (liftM ((left input).run state) : PMF _) := rfl
theorem pmfSumImpl_inr {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : rightSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inr input)).run state = (liftM ((right input).run state) : PMF _) := rfl
theorem pmfSumImpl_eq_lift_add {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    pmfSumImpl left right = fun input => StateT.mk fun state =>
      (liftM (((left + right) input).run state) : PMF _) := by
  funext input
  cases input <;> rfl
theorem simulateQ_liftProbCompImpl_run {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (computation : OracleComp spec α) (state : σ) :
    (simulateQ (fun input => StateT.mk fun current => (liftM ((impl input).run current) : PMF _))
      computation).run state = (liftM ((simulateQ impl computation).run state) : PMF _) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (liftM_pure (m := ProbComp) (n := PMF) _).symm
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, StateT.run_mk]
      rw [liftM_bind (m := ProbComp) (n := PMF)]
      exact congrArg (fun continuation => (liftM ((impl input).run state) : PMF _).bind continuation)
        (funext fun result => ih result.1 result.2)
noncomputable def proposalRecordImpl {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT (List α × σ) PMF) :=
  fun input => StateT.mk fun state =>
    if active input state.2 then
      (recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
        (fun result => (response input result.2,
          (state.1 ++ result.1 ++ [label input result.2],
            advance input state.2 (result.1.length + 1) result.2)))
    else
      (record input state.2).map fun outcome =>
        (response input outcome, (state.1, advance input state.2 0 outcome))
noncomputable def lengthRecordImpl {ι σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT σ PMF) :=
  fun input => StateT.mk fun state =>
    if active input state then
      (recordLengthBridge (record input state) accept hpos hle).map
        (fun result => (response input result.2, advance input state result.1 result.2))
    else
      (record input state).map fun outcome => (response input outcome, advance input state 0 outcome)
theorem proposalRecordImpl_project {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (input : spec.Domain) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      ((proposalRecordImpl record response advance label rejected active accept hpos hle) input).run state =
    ((lengthRecordImpl record response advance active accept hpos hle) input).run state.2 := by
  change PMF.map (Prod.map id Prod.snd) _ = _
  simp only [proposalRecordImpl, lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state.2 = true
  · simp only [hactive, if_true]
    calc
      _ = ((recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
          (fun result => (result.1.length + 1, result.2))).map
            (fun result => (response input result.2, advance input state.2 result.1 result.2)) := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by rw [recordProposalBridge_length_record]
  · simp only [hactive, Bool.false_eq_true, if_false, PMF.map_comp]
    rfl
theorem simulateQ_proposalRecordImpl_project {ι α σ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (computation : OracleComp spec β) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalRecordImpl record response advance label rejected active accept hpos hle)
        computation).run state =
    (simulateQ (lengthRecordImpl record response advance active accept hpos hle)
      computation).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (proposalRecordImpl_project record response advance label rejected active accept hpos hle)
    computation state
theorem lengthRecordImpl_project {ι σ τ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (input : spec.Domain) (state : σ) :
    Prod.map id project <$> ((lengthRecordImpl record response advance active accept hpos hle) input).run state =
      (base input).run (project state) := by
  change PMF.map (Prod.map id project) _ = _
  simp only [lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state = true
  · simp only [hactive, if_true, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
    calc
      _ = ((recordLengthBridge (record input state) accept hpos hle).map Prod.snd).map
          (fun outcome => (response input outcome, next input state outcome)) := by
        rw [PMF.map_comp]
        rfl
      _ = _ := by rw [recordLengthBridge_record, hrecord]
  · simpa only [hactive, Bool.false_eq_true, if_false, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
      using hrecord input state
theorem simulateQ_lengthRecordImpl_project {ι σ τ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (computation : OracleComp spec β) (state : σ) :
    Prod.map id project <$>
      (simulateQ (lengthRecordImpl record response advance active accept hpos hle) computation).run state =
      (simulateQ base computation).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ project
    (lengthRecordImpl_project record response advance active accept hpos hle base project next hnext hrecord)
    computation state
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_OriginalProposalExecution ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
private theorem probCompLift_map {α β : Type} (comp : ProbComp α) (f : α → β) :
    (liftM comp : PMF α).map f = (liftM (f <$> comp) : PMF β) :=
  (liftM_map (m := ProbComp) (n := PMF) _ _).symm
private theorem tracedSigningRun_output {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result : TracedSigningRecord ω => (result.1.1.1, result.2)) <$>
      tracedSigningRun trace key message cache = (simulateQ romImpl (sign key message)).run cache := by
  calc
    _ = (fun result => (result.1.1, result.2)) <$>
        ((fun result : TracedSigningRecord ω => (result.1.1, result.2)) <$>
          tracedSigningRun trace key message cache) := by simp only [Functor.map_map]
    _ = _ := by rw [tracedSigningRun_forget, simulateQ_signWithView_fst_run]
private theorem completedSigningRecord_output {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map (fun result => (result.1.1.1.1, result.1.2)) =
      (liftM ((simulateQ romImpl (sign key message)).run cache) : PMF _) := by
  calc
    _ = ((completedSigningRecord trace key message cache).map Prod.fst).map
        (fun result : TracedSigningRecord ω => (result.1.1.1, result.2)) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [completedSigningRecord_forget, probCompLift_map, tracedSigningRun_output]
structure ProposalExecutionRecord (input : (OracleWorld + SigningSpec).Domain) where
  output : (OracleWorld + SigningSpec).Range input
  cache : QueryCache HashSpec
  trace : SigningBoundaryTrace
  selectedView : Option FewTimeView
  index : Index
noncomputable def originalProposalRecord (key : SecretKey) :
    (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec → PMF (ProposalExecutionRecord input)
  | .inl world, cache =>
      (liftM ((romImpl world).run cache) : PMF _).map fun result =>
        ⟨result.1, result.2, signingBoundaryTrace key.parameter world result.1, none, 0⟩
  | .inr message, cache =>
      (completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map fun result =>
        ⟨result.1.1.1.1, result.1.2, result.1.1.2, result.1.1.1.2, result.2⟩
noncomputable def originalAdversaryPMFImpl (key : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) PMF) :=
  pmfSumImpl romImpl (fun message => simulateQ romImpl (sign key message))
theorem originalAdversaryImpl_split (key : SecretKey) :
    (romImpl + (fun message => simulateQ romImpl (sign key message))) = unloggedMappedAdversaryImpl key := by
  funext input
  cases input with
  | inl world => rfl
  | inr message =>
      change simulateQ romImpl (sign key message) = simulateQ romImpl (scheme.sign key message)
      have hsign : scheme.sign = sign := rfl
      rw [hsign]
theorem simulateQ_originalAdversaryPMFImpl {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (simulateQ (originalAdversaryPMFImpl key) computation).run cache =
      (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run cache) : PMF _) := by
  rw [originalAdversaryPMFImpl, pmfSumImpl_eq_lift_add, simulateQ_liftProbCompImpl_run,
    originalAdversaryImpl_split]
theorem originalProposalRecord_project (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (originalProposalRecord key input cache).map (fun result => (result.output, result.cache)) =
      (originalAdversaryPMFImpl key input).run cache := by
  cases input with
  | inl world =>
      rw [originalAdversaryPMFImpl, pmfSumImpl_inl, originalProposalRecord, PMF.map_comp]
      exact PMF.map_id _
  | inr message =>
      rw [originalAdversaryPMFImpl, pmfSumImpl_inr, originalProposalRecord, PMF.map_comp]
      exact completedSigningRecord_output (signingBoundaryTrace key.parameter) key message cache
theorem originalProposalRecord_index (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (originalProposalRecord key (.inr message) cache).map (fun result => result.index) =
      (completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map Prod.snd := by
  rw [originalProposalRecord, PMF.map_comp]
  rfl
theorem originalProposalRecord_cap (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (spent : Nat) (hbound : ProposalCacheBound key cache spent) (index : Index) :
    targetProposalAcceptance *
      ((originalProposalRecord key (.inr message) cache).map (fun result => result.index)) index ≤
      PMF.uniformOfFintype Index index := by
  rw [originalProposalRecord_index]
  exact completedSigningRecord_acceptance_cap (signingBoundaryTrace key.parameter) key message cache spent hbound index
noncomputable def originalProposalActive {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool) :
    (OracleWorld + SigningSpec).Domain → QueryCache HashSpec × μ → Bool
  | .inl _, _ => false
  | .inr message, state => enabled message state && decide (ProposalCacheBound key state.1 (spent state))
noncomputable def originalRejectedProposal {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) :
    (OracleWorld + SigningSpec).Domain → QueryCache HashSpec × μ → PMF Index
  | .inl _, _ => PMF.uniformOfFintype Index
  | .inr message, state =>
      if hbound : ProposalCacheBound key state.1 (spent state) then
        proposalResidualLaw (PMF.uniformOfFintype Index)
          ((originalProposalRecord key (.inr message) state.1).map (fun result => result.index))
          targetProposalAcceptance targetProposalAcceptance_lt_one
          (originalProposalRecord_cap key message state.1 (spent state) hbound)
      else PMF.uniformOfFintype Index
def originalProposalAdvance {μ : Type}
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (input : (OracleWorld + SigningSpec).Domain) (state : QueryCache HashSpec × μ)
    (length : Nat) (record : ProposalExecutionRecord input) : QueryCache HashSpec × μ :=
  (record.cache, update input state length record)
noncomputable def originalProposalImpl {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × (QueryCache HashSpec × μ)) PMF) :=
  proposalRecordImpl (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (fun _ record => record.index)
    (originalRejectedProposal key spent) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
noncomputable def originalLengthImpl {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec × μ) PMF) :=
  lengthRecordImpl (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
theorem simulateQ_originalProposalImpl_length {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    Prod.map id Prod.snd <$> (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (simulateQ (originalLengthImpl key spent enabled update) computation).run state.2 :=
  simulateQ_proposalRecordImpl_project _ _ _ _ _ _ _ _ _ computation state
theorem simulateQ_originalLengthImpl_forget {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : QueryCache HashSpec × μ) :
    Prod.map id Prod.fst <$> (simulateQ (originalLengthImpl key spent enabled update) computation).run state =
      (simulateQ (originalAdversaryPMFImpl key) computation).run state.1 := by
  apply simulateQ_lengthRecordImpl_project
    (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
    (originalAdversaryPMFImpl key) Prod.fst (fun _ _ record => record.cache)
  · intros
    rfl
  · intro input state
    exact originalProposalRecord_project key input state.1
theorem simulateQ_originalProposalImpl_forget {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (simulateQ (originalAdversaryPMFImpl key) computation).run state.2.1 := by
  calc
    _ = Prod.map id Prod.fst <$>
        (Prod.map id Prod.snd <$>
          (simulateQ (originalProposalImpl key spent enabled update) computation).run state) := by
      simp only [Functor.map_map]
      rfl
    _ = _ := by rw [simulateQ_originalProposalImpl_length, simulateQ_originalLengthImpl_forget]
theorem simulateQ_originalProposalImpl_original {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run state.2.1) : PMF _) := by
  rw [simulateQ_originalProposalImpl_forget, simulateQ_originalAdversaryPMFImpl]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_BankedProposalStep ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def certificateBankCount (bank : HashInput → Bool) : ENNReal :=
  ∑' input, if bank input then 1 else 0
theorem certificateBankCount_empty : certificateBankCount (fun _ => false) = 0 := by
  simp [certificateBankCount]
theorem one_le_certificateBankCount (bank : HashInput → Bool) (input : HashInput) (hbank : bank input = true) :
    1 ≤ certificateBankCount bank := by
  have h := ENNReal.le_tsum (f := fun input => if bank input then (1 : ENNReal) else 0) input
  simpa only [certificateBankCount, hbank, if_true] using h
noncomputable def bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' input, if bank input then 1 else if stopped then 0 else
    cacheMessageEntryWeight parameter weight cache input
theorem bankedCacheWeight_mono (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hle : ∀ input target, first input target ≤ second input target) :
    bankedCacheWeight parameter first bank stopped cache ≤ bankedCacheWeight parameter second bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · unfold cacheMessageEntryWeight
    cases cache input
    · exact le_rfl
    · simp only
      split_ifs
      · exact hle input _
      · exact le_rfl
theorem bankedCacheWeight_discard_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank stopped cache ≤ bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases bank input <;> cases stopped <;> simp
theorem certificateBankCount_le_bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    certificateBankCount bank ≤ bankedCacheWeight parameter weight bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs <;> first | exact le_rfl | exact zero_le
theorem bankedCacheWeight_stopped (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank true cache = certificateBankCount bank := by
  simp only [bankedCacheWeight, certificateBankCount, if_true]
theorem bankedCacheWeight_live (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank false cache = certificateBankCount bank +
      cacheMessageWeight parameter (fun input target => if bank input then 0 else weight input target) cache := by
  rw [bankedCacheWeight, certificateBankCount, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hbank : bank input <;> cases hcache : cache input <;>
    simp [cacheMessageEntryWeight, hbank, hcache]
theorem bankedCacheWeight_bank_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank completed : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hcompleted : ∀ input, completed input = true →
      1 ≤ cacheMessageEntryWeight parameter weight cache input) :
    bankedCacheWeight parameter weight (fun input => bank input || completed input) stopped cache ≤
      bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases hbank : bank input <;> cases hcomplete : completed input <;>
    simp only [hbank, hcomplete, Bool.false_or, Bool.true_or, Bool.false_eq_true, if_true, if_false, le_refl]
  · cases stopped <;> simp
  · exact hcompleted input hcomplete
theorem expected_bankedCacheWeight_step_le_of_split {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hsplit : ∀ result ∈ support computation, ∀ value : HashInput → FewTimeView → ENNReal,
      cacheMessageWeight parameter value (after result) = cacheMessageWeight parameter value before +
        cacheMessageWeight parameter (fun input target => if before input = none then value input target else 0) (after result))
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge := by
  let pending := fun result input target => if bank input then 0 else weight result input target
  have hstep (result : α) (hr : result ∈ support computation) :
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result) ≤
      certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
        cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
          (after result) := by
    apply (bankedCacheWeight_bank_le parameter (weight result) bank (completed result) (stopped result)
      (after result) (hcompleted result hr)).trans
    rw [bankedCacheWeight_live, hsplit result hr (pending result), ← add_assoc]
    apply add_le_add le_rfl
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    split_ifs <;> first | exact le_rfl | exact zero_le
  have hold' : (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) ≤
      cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before := by
    rw [expected_cacheMessageWeight]
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    cases hb : bank input
    · simpa only [hb, Bool.false_eq_true, if_false] using hold input target
    · simp only [if_true, mul_zero, tsum_zero, le_refl]
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (hstep result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | computation]) * certificateBankCount bank +
        (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) +
        (∑' result, Pr[= result | computation] *
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ certificateBankCount bank +
        cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before + charge :=
      add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hold') hnew
    _ = _ := by rw [bankedCacheWeight_live]
theorem expected_bankedCacheWeight_step_le {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hcache : ∀ result ∈ support computation, before ≤ after result)
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge :=
  expected_bankedCacheWeight_step_le_of_split parameter computation before after weight initial bank completed stopped charge
    (fun result hr value => cacheMessageWeight_of_le parameter value before (after result) (hcache result hr))
    hcompleted hold hnew
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem newTargetEnvelopeCharge_cacheQuery (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    newTargetEnvelopeCharge key before (before.cacheQuery input output) log reuse queries signings groups remaining =
      if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        targetShapeEnvelope (signerRate (hashOutputFewTimeView output)) reuse (arrivalRate (hashOutputFewTimeView output))
          queries signings
          (targetShapeMoments key (before.cacheQuery input output) log (payloadOf input) (hashOutputFewTimeView output)) groups remaining else 0 := by
  unfold newTargetEnvelopeCharge
  rw [cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh,
    cacheMessageWeight_fresh_restriction, zero_add]
  simp only [hfresh, if_true]
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_signWithView_newTargetEnvelopeCharge_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) reuse queries signings groups remaining) ≤
        freshDigestSelectionProbability key message before *
          (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
            targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
              (targetIndexMoments key before log) groups.card remaining.card)) := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log hsigned reuse queries signings groups remaining hvalid
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def freshWorldTargetHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => if MessageHashInput parameter input ∧ cache input = none then 1 else 0
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
noncomputable abbrev reuseNewTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (before : QueryCache HashSpec) (after : CoverLogState) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  newTargetEnvelopeCharge key before after.1 after.2 reuse budget signatures groups remaining
theorem expected_randomOracle_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 (.inr input) : ENNReal) *
        ((Fintype.card Index : ENNReal)⁻¹ *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (state.1.cacheQuery input output, state.2) groups remaining) ≤ _
    simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge_cacheQuery key state.1 state.2 _ _ _ groups remaining input _ hfresh]
    by_cases hmessage : MessageHashInput key.parameter input
    · obtain ⟨payload, rfl⟩ := hmessage
      simp only [show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
        true_and, payloadOf_tweakableHashInput, freshWorldTargetHashCost, hfresh, and_self, if_true, Nat.cast_one, one_mul]
      refine (expected_cacheQuery_freshTargetEnvelope_le key state.1 state.2 payload hfresh hsigned _ _ _ groups remaining hvalid).trans_eq ?_
      unfold reuseRawEnvelope observedRawIndexShapeVector
      rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
    · simp only [hmessage, false_and, if_false, mul_zero, tsum_zero, zero_le]
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    rw [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction]
    exact zero_le
theorem expected_logTraced_world_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
        ((Fintype.card Index : ENNReal)⁻¹ *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseNewTarget_le key reuse budget signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction, mul_zero, tsum_zero, zero_le]
theorem expected_logTraced_sign_reuseNewTarget_le_mass_mul (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      freshDigestSelectionProbability key message state.1 *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state groups remaining)) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  have heq := congrArg (fun computation : ProbComp (Option Signature × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) hrun
  rw [tsum_probOutput_map_mul] at heq
  have h := expected_signWithView_newTargetEnvelopeCharge_le_mass_mul key message state.1 state.2 hsigned
    reuse budget signatures groups remaining hvalid
  refine heq.le.trans (h.trans_eq ?_)
  unfold reuseRawEnvelope observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def signingExecutionHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => digestAttemptLimit
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def reuseTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (signerRate target) reuse (arrivalRate target) budget signatures
    (observedTargetShapeVector key payload target state)
theorem reuseTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    reuseTargetEnvelope key reuse smaller payload target signatures state groups remaining ≤
      reuseTargetEnvelope key reuse larger payload target signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ signatures _ hbudget groups remaining hvalid
theorem expected_randomOracle_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + 1) payload target signatures state groups remaining := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    unfold reuseTargetEnvelope
    rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
    exact targetShapeEnvelope_mono _ _ _ budget signatures
      (fun G R hv => expected_fresh_targetShape_le key payload target state.1 state.2 input hfresh hsigned G R hv)
      groups remaining hvalid
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact reuseTargetEnvelope_budget_mono key reuse payload target signatures state (Nat.le_succ _) groups remaining hvalid
theorem expected_logTraced_world_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) payload target signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseTarget_le key reuse budget payload target signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem expected_logTraced_sign_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse budget payload target (signatures + 1) state groups remaining := by
  unfold reuseTargetEnvelope
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ budget signatures
    (fun G R hv => expected_logTraced_sign_targetShape_le_of_exactReuse key reuse payload target state hsigned message hreuse G R hv)
      groups remaining hvalid).trans
    (targetShapeEnvelope_signing_le _ _ _ budget signatures _ groups remaining hvalid)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
def TargetCoveredOn (key : SecretKey) (required : Finset IndexGroup) (state : CoverLogState)
    (payload : HashInput) (target : FewTimeView) : Prop :=
  ∀ tree ∈ required, 0 < targetTreeMatchCount
    (eligibleSigningViews (messageAnswers key.parameter state.1) key.root payload state.2) target tree
def TargetCertificateAt (key : SecretKey) (required : Finset IndexGroup) (state : CoverLogState)
    (input : HashInput) : Prop :=
  ∃ output, state.1 input = some output ∧ MessageHashInput key.parameter input ∧
    Admissible (truncateMessageDigest output) ∧
      TargetCoveredOn key required state (payloadOf input) (hashOutputFewTimeView output)
noncomputable def completedTargetBank (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) : HashInput → Bool :=
  fun input => bank input || decide (TargetCertificateAt key required state input)
noncomputable def targetCertificateScale (required : Finset IndexGroup) : ENNReal :=
  coverScale ^ required.card
noncomputable def targetCertificateForecast (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput) (target : FewTimeView) : ENNReal :=
  reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required *
    targetCertificateScale required
noncomputable def bankedTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) : ENNReal :=
  bankedCacheWeight key.parameter (targetCertificateForecast key reuse budget signatures required state) bank stopped state.1
noncomputable def targetCreationMultiplier (key : SecretKey) (cache : QueryCache HashSpec) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl input => freshWorldTargetHashCost key.parameter cache input
  | .inr message => admissibleProbability⁻¹ * freshDigestSelectionProbability key message cache
theorem targetCreationMultiplier_sign_le (key : SecretKey) (cache : QueryCache HashSpec) (message : Message) :
    targetCreationMultiplier key cache (.inr message) ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
  calc
    _ ≤ (2142 : ENNReal) * 1 :=
      mul_le_mul' admissibleProbability_inv_le (freshDigestSelectionProbability_le_one key message cache)
    _ ≤ _ := by
      rw [mul_one]
      exact_mod_cast (show 2142 ≤ 2 ^ ftsTreeHeight by decide)
noncomputable def targetCreationPrice (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) : ENNReal :=
  (Fintype.card Index : ENNReal)⁻¹ *
    reuseRawEnvelope key reuse budget signatures state ∅ required * targetCertificateScale required
theorem bankedTargetEnvelope_initial (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState)
    (hnone : ∀ input, MessageHashInput key.parameter input → state.1 input = none) :
    bankedTargetEnvelope key reuse budget signatures required state (fun _ => false) false = 0 := by
  rw [bankedTargetEnvelope, bankedCacheWeight_live, certificateBankCount_empty, zero_add]
  exact cacheMessageWeight_of_no_message key.parameter _ state.1 hnone
theorem bankedTargetEnvelope_stopped (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) :
    bankedTargetEnvelope key reuse budget signatures required state bank true = certificateBankCount bank :=
  bankedCacheWeight_stopped _ _ _ _
theorem targetCreationMultiplier_sign_mul_price (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (message : Message) :
    targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state =
      freshDigestSelectionProbability key message state.1 *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required)) *
          targetCertificateScale required := by
  unfold targetCreationMultiplier targetCreationPrice
  ring
theorem completedTargetBank_of_certificate (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) (input : HashInput)
    (hcovered : TargetCertificateAt key required state input) :
    completedTargetBank key required state bank input = true := by
  simp only [completedTargetBank, hcovered, decide_true, Bool.or_true]
theorem normalizedTargetLogProduct_ge_of_coveredOn (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (payload : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state payload target) :
    coverNormalization ^ required.card ≤
      normalizedTargetLogProduct key state.1 state.2 payload target required := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro tree htree
  apply le_mul_of_one_le_right'
  exact_mod_cast Nat.succ_le_iff.mpr (hcovered tree htree)
theorem one_le_targetCertificateForecast_of_covered (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state (payloadOf input) target) :
    1 ≤ targetCertificateForecast key reuse budget signatures required state input target := by
  have hmoment := normalizedTargetLogProduct_ge_of_coveredOn key required state (payloadOf input) target hcovered
  have hforecast : coverNormalization ^ required.card ≤
      reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required := by
    apply hmoment.trans
    simpa only [reuseTargetEnvelope, observedTargetShapeVector, targetShapeMoments, Finset.prod_empty, one_mul] using
      (le_targetShapeEnvelope (signerRate target) reuse (arrivalRate target)
        budget signatures (observedTargetShapeVector key (payloadOf input) target state) ∅ required)
  unfold targetCertificateForecast targetCertificateScale
  calc
    (1 : ENNReal) = coverNormalization ^ required.card * coverScale ^ required.card := by
      rw [← mul_pow, coverNormalization_mul_coverScale, one_pow]
    _ ≤ _ := mul_le_mul' hforecast le_rfl
theorem one_le_targetCertificateEntry_of_certificate (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput)
    (hcertificate : TargetCertificateAt key required state input) :
    1 ≤ cacheMessageEntryWeight key.parameter
      (targetCertificateForecast key reuse budget signatures required state) state.1 input := by
  obtain ⟨output, houtput, hmessage, hadmissible, hcovered⟩ := hcertificate
  simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
  exact one_le_targetCertificateForecast_of_covered key reuse budget signatures required state input _ hcovered
private theorem empty_targetShapeValid (required : Finset IndexGroup) : TargetShapeValid ∅ required := by
  constructor <;> simp
theorem targetCreationPrice_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    targetCreationPrice key reuse smaller signatures required state ≤
      targetCreationPrice key reuse larger signatures required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact targetShapeEnvelope_queries_mono _ _ _ _ _ hbudget ∅ required (empty_targetShapeValid required)
theorem targetCreationPrice_signatures_mono (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) {smaller larger : Nat} (hsignatures : smaller ≤ larger) :
    targetCreationPrice key reuse budget smaller required state ≤
      targetCreationPrice key reuse budget larger required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact Function.monotone_iterate_of_id_le
    (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning (constRate (Fintype.card Index : ENNReal)⁻¹) reuse f from
      fun _ _ _ => (le_self_add).trans le_self_add)
    hsignatures _ ∅ required
theorem bankedTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool)
    {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    bankedTargetEnvelope key reuse smaller signatures required state bank stopped ≤
      bankedTargetEnvelope key reuse larger signatures required state bank stopped := by
  apply bankedCacheWeight_mono
  intro input target
  exact mul_le_mul' (reuseTargetEnvelope_budget_mono key reuse (payloadOf input) target signatures state
    hbudget ∅ required (empty_targetShapeValid required)) le_rfl
theorem newTargetCertificateForecast_eq (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (before : QueryCache HashSpec) (after : CoverLogState) :
    cacheMessageWeight key.parameter (fun input target => if before input = none then
      targetCertificateForecast key reuse budget signatures required after input target else 0) after.1 =
      reuseNewTargetEnvelope key reuse budget signatures before after ∅ required * targetCertificateScale required := by
  unfold reuseNewTargetEnvelope newTargetEnvelopeCharge
  rw [← cacheMessageWeight_mul_right]
  apply congrArg (fun weight => cacheMessageWeight key.parameter weight after.1)
  funext input target
  by_cases hfresh : before input = none
  · simp only [hfresh, if_true, targetCertificateForecast]
    rfl
  · simp only [hfresh, if_false, zero_mul]
theorem expected_logTraced_world_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : (OracleWorld + SigningSpec).Range (.inl input) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) signatures required state bank false +
        (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
          ((Fintype.card Index : ENNReal)⁻¹ *
            reuseRawEnvelope key reuse budget signatures state ∅ required) * targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inl input) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_world_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state input hsigned ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_world_reuseNewTarget_le key reuse budget signatures state input hsigned
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))
theorem expected_logTraced_sign_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : (OracleWorld + SigningSpec).Range (.inr message) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        freshDigestSelectionProbability key message state.1 *
          (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required)) *
            targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_sign_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state hsigned message hreuse ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_sign_reuseNewTarget_le_mass_mul key reuse budget signatures state hsigned message
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
def proposalRecordLogState (input : (OracleWorld + SigningSpec).Domain) (log : QueryLog SigningSpec)
    (record : ProposalExecutionRecord input) : CoverLogState :=
  (record.cache, log ++ signingLogFragment input record.output)
private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl
private theorem expected_pmf_mono_of_support {α : Type} (law : PMF α) (first second : α → ENNReal)
    (hle : ∀ result ∈ law.support, first result ≤ second result) :
    (∑' result, Pr[= result | law] * first result) ≤ ∑' result, Pr[= result | law] * second result := by
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (hle result hr)
  · have hp : Pr[= result | law] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]
theorem originalAdversaryPMFImpl_run (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    (originalAdversaryPMFImpl key input).run cache =
      (liftM ((unloggedMappedAdversaryImpl key input).run cache) : PMF _) := by
  rw [originalAdversaryPMFImpl, pmfSumImpl_eq_lift_add, originalAdversaryImpl_split]
  rfl
theorem expected_originalProposalRecord_logged (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CoverLogState) (weight : CoverLogState → ENNReal) :
    (∑' record, Pr[= record | originalProposalRecord key input state.1] *
      weight (proposalRecordLogState input state.2 record)) =
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * weight result.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have h := congrArg (fun computation : PMF ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] * weight (result.2, state.2 ++ signingLogFragment input result.1))
      (originalProposalRecord_project key input state.1)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, originalAdversaryPMFImpl_run, expected_pmfLift] at h
  exact h
theorem originalProposalRecord_world_hashCalls (key : SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inl input))
    (hr : record ∈ (originalProposalRecord key (.inl input) cache).support) :
    record.trace.hashCalls = signingExecutionHashCost (.inl input) := by
  rw [originalProposalRecord, PMF.mem_support_map_iff] at hr
  obtain ⟨result, _, rfl⟩ := hr
  cases input with
  | inl sample => rfl
  | inr input => rfl
noncomputable def bankedProposalRecordValue (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool)
    (input : (OracleWorld + SigningSpec).Domain) (record : ProposalExecutionRecord input) (stopped : Bool) : ENNReal :=
  let after := proposalRecordLogState input state.2 record
  bankedTargetEnvelope key reuse (budget - record.trace.hashCalls) signatures required after
    (completedTargetBank key required after bank) stopped
theorem expected_originalProposalRecord_world_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : ProposalExecutionRecord (.inl input) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcost : signingExecutionHashCost (.inl input) ≤ budget) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse budget signatures required state := by
  let afterBudget := budget - signingExecutionHashCost (.inl input)
  let weight := fun current => bankedTargetEnvelope key reuse afterBudget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_world_bankedTarget_le key reuse afterBudget signatures required state bank input
    (fun _ => false) hsigned
  have hrestore : afterBudget + signingExecutionHashCost (.inl input) = budget := Nat.sub_add_cancel hcost
  rw [hrestore] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
        weight (proposalRecordLogState (.inl input) state.2 record) := by
      apply expected_pmf_mono_of_support
      intro record hr
      have hc := originalProposalRecord_world_hashCalls key input state.1 record hr
      dsimp only [bankedProposalRecordValue, weight, afterBudget]
      rw [hc]
      exact bankedCacheWeight_discard_le _ _ _ _ _
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inl input) state weight
    _ ≤ bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse afterBudget signatures required state := by
      simpa only [targetCreationMultiplier, targetCreationPrice, mul_assoc] using hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_budget_mono key reuse signatures required state (Nat.sub_le _ _)))
theorem expected_originalProposalRecord_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state := by
  let weight := fun current => bankedTargetEnvelope key reuse budget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_sign_bankedTarget_le key reuse budget signatures required state bank message
    (fun _ => false) hsigned hreuse
  rw [← targetCreationMultiplier_sign_mul_price] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
        weight (proposalRecordLogState (.inr message) state.2 record) := by
      apply ENNReal.tsum_le_tsum
      intro record
      apply mul_le_mul' le_rfl
      exact (bankedCacheWeight_discard_le _ _ _ _ _).trans
        (bankedTargetEnvelope_budget_mono key reuse signatures required _ _ false (Nat.sub_le _ _))
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inr message) state weight
    _ ≤ bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state := hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_signatures_mono key reuse budget required state (Nat.le_succ _)))
theorem expected_coupled_bankedProposalRecord_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) (input : (OracleWorld + SigningSpec).Domain)
    (law : PMF α) (record : α → ProposalExecutionRecord input) (stopped : α → Bool) (bound : ENNReal)
    (hrecord : law.map record = originalProposalRecord key input state.1)
    (hbound : (∑' result, Pr[= result | originalProposalRecord key input state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank input result false) ≤ bound) :
    (∑' result, Pr[= result | law] *
      bankedProposalRecordValue key reuse budget signatures required state bank input (record result) (stopped result)) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        bankedProposalRecordValue key reuse budget signatures required state bank input (record result) false := by
      apply ENNReal.tsum_le_tsum
      intro result
      exact mul_le_mul' le_rfl (bankedCacheWeight_discard_le _ _ _ _ _)
    _ = ∑' result, Pr[= result | originalProposalRecord key input state.1] *
        bankedProposalRecordValue key reuse budget signatures required state bank input result false := by
      rw [← hrecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    _ ≤ bound := hbound
theorem expected_lengthBridge_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : Nat × ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | recordLengthBridge (originalProposalRecord key (.inr message) state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) result.2 (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state :=
  expected_coupled_bankedProposalRecord_le key reuse budget signatures required state bank (.inr message)
    _ Prod.snd stopped _ (recordLengthBridge_record _ _ _ _)
    (expected_originalProposalRecord_sign_banked_le key reuse budget signatures required state bank message
      (fun _ => false) hsigned hreuse)
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_CertificateMonitor ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def ValidSigningStep (log : QueryLog SigningSpec) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl _ => log.length ≤ signatureLimit
  | .inr _ => log.length < signatureLimit
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
def signingMacroHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2 ^ ftsTreeHeight
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
structure CertificateMonitor where
  log : QueryLog SigningSpec
  spent : Nat
  messageCalls : Nat
  proposals : Nat
  creationMass : ENNReal
  creationCost : ENNReal
  bank : HashInput → Bool
  stopped : Bool
abbrev CertificateMonitorState := QueryCache HashSpec × CertificateMonitor
def certificateMonitorCoverState (state : CertificateMonitorState) : CoverLogState :=
  (state.1, state.2.log)
def CertificateMonitorReady (key : SecretKey) (budget : Nat) (state : CertificateMonitorState) : Prop :=
  SigningDigestsCached key.parameter state.1 key.root state.2.log ∧
    ProposalCacheBound key state.1 state.2.spent ∧ state.2.spent ≤ budget
def CertificateMonitorActive (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : Prop :=
  state.2.stopped = false ∧ CertificateMonitorReady key budget state ∧
    ValidSigningStep state.2.log input ∧ signingMacroHashCost input ≤ budget - state.2.spent
abbrev CertificateStopRule := (input : (OracleWorld + SigningSpec).Domain) →
  CertificateMonitorState → Nat → ProposalExecutionRecord input → Bool
noncomputable def certificateMonitorEnabled (key : SecretKey) (budget : Nat)
    (message : Message) (state : CertificateMonitorState) : Bool :=
  decide (CertificateMonitorActive key budget (.inr message) state)
noncomputable def certificateMonitorUpdate (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) : CertificateMonitor :=
  if CertificateMonitorActive key budget input state then
    let after := proposalRecordLogState input state.2.log record
    let next : CertificateMonitor :=
      { log := after.2
        spent := state.2.spent + record.trace.hashCalls
        messageCalls := state.2.messageCalls + record.trace.messageCalls.length
        proposals := state.2.proposals + length
        creationMass := state.2.creationMass + targetCreationMultiplier key state.1 input
        creationCost := state.2.creationCost + targetCreationMultiplier key state.1 input *
          targetCreationPrice key nearUniformDigestReuseWeight (budget - state.2.spent)
            (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state)
        bank := completedTargetBank key required after state.2.bank
        stopped := false }
    { next with stopped := (stopAfter input state length record || decide (¬ CertificateMonitorReady key budget (record.cache, next))) }
  else { state.2 with stopped := true }
noncomputable def certificateLengthImpl (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CertificateMonitorState PMF) :=
  originalLengthImpl key (fun state => state.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter)
noncomputable def certificateProposalImpl (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × CertificateMonitorState) PMF) :=
  originalProposalImpl key (fun state => state.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter)
noncomputable def certificateMonitorPotential (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (state : CertificateMonitorState) : ENNReal :=
  bankedTargetEnvelope key nearUniformDigestReuseWeight (budget - state.2.spent)
    (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state) state.2.bank state.2.stopped
noncomputable def certificateMonitorCharge (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    targetCreationMultiplier key state.1 input * targetCreationPrice key nearUniformDigestReuseWeight
      (budget - state.2.spent) (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state)
  else 0
noncomputable def certificateMonitorMass (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then targetCreationMultiplier key state.1 input else 0
def initialCertificateMonitor (spent : Nat) (stopped : Bool := false) : CertificateMonitor :=
  { log := []
    spent := spent
    messageCalls := 0
    proposals := 0
    creationMass := 0
    creationCost := 0
    bank := fun _ => false
    stopped := stopped }
theorem certificateMonitorUpdate_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).creationCost =
      state.2.creationCost + certificateMonitorCharge key budget required input state := by
  by_cases hactive : CertificateMonitorActive key budget input state <;>
    simp only [certificateMonitorUpdate, certificateMonitorCharge, hactive, if_true, if_false, add_zero]
theorem certificateMonitorUpdate_creationMass (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass =
      state.2.creationMass + certificateMonitorMass key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state <;>
    simp only [certificateMonitorUpdate, certificateMonitorMass, hactive, if_true, if_false, add_zero]
theorem certificateMonitorPotential_initial (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateMonitorPotential key budget required (cache, initialCertificateMonitor spent stopped) = 0 := by
  cases stopped with
  | false => exact bankedTargetEnvelope_initial key _ _ _ required _ hnone
  | true => simp only [certificateMonitorPotential, initialCertificateMonitor, bankedTargetEnvelope_stopped, certificateBankCount_empty]
theorem certificateMonitorUpdate_inactive (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    certificateMonitorUpdate key budget required stopAfter input state length record = { state.2 with stopped := true } := by
  rw [certificateMonitorUpdate, if_neg hactive]
theorem certificateMonitorUpdate_spent (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent =
      state.2.spent + record.trace.hashCalls := by
  simp only [certificateMonitorUpdate, if_pos hactive]
theorem certificateMonitorUpdate_messageCalls (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).messageCalls =
      state.2.messageCalls + record.trace.messageCalls.length := by
  simp only [certificateMonitorUpdate, if_pos hactive]
theorem certificateMonitorPotential_advance_active (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) =
      bankedProposalRecordValue key nearUniformDigestReuseWeight (budget - state.2.spent)
        (signatureLimit - (state.2.log ++ signingLogFragment input record.output).length)
        required (certificateMonitorCoverState state) state.2.bank input record
        (certificateMonitorUpdate key budget required stopAfter input state length record).stopped := by
  simp only [certificateMonitorPotential, originalProposalAdvance, certificateMonitorUpdate, if_pos hactive,
    bankedProposalRecordValue, proposalRecordLogState, certificateMonitorCoverState, Nat.sub_sub]
theorem certificateMonitorPotential_advance_inactive (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) =
      certificateBankCount state.2.bank := by
  simp only [certificateMonitorPotential, originalProposalAdvance, certificateMonitorUpdate_inactive key budget
    required stopAfter input state length record hactive, bankedTargetEnvelope_stopped]
theorem certificateMonitor_sign_proposals_active (key : SecretKey) (budget : Nat)
    (message : Message) (state : CertificateMonitorState) :
    originalProposalActive key (fun state : CertificateMonitorState => state.2.spent)
      (certificateMonitorEnabled key budget) (.inr message) state =
        decide (CertificateMonitorActive key budget (.inr message) state) := by
  by_cases hactive : CertificateMonitorActive key budget (.inr message) state
  · simp only [originalProposalActive, certificateMonitorEnabled, hactive, decide_true,
      hactive.2.1.2.1, Bool.true_and]
  · simp only [originalProposalActive, certificateMonitorEnabled, hactive, decide_false, Bool.false_and]
theorem certificateLengthImpl_world_run (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (state : CertificateMonitorState) :
    (certificateLengthImpl key budget required stopAfter (.inl input)).run state =
      (originalProposalRecord key (.inl input) state.1).map (fun record =>
        (record.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inl input) state 0 record)) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, originalProposalActive,
    StateT.run_mk, Bool.false_eq_true, if_false]
theorem certificateLengthImpl_sign_run (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (message : Message)
    (state : CertificateMonitorState) :
    (certificateLengthImpl key budget required stopAfter (.inr message)).run state =
      if CertificateMonitorActive key budget (.inr message) state then
        (recordLengthBridge (originalProposalRecord key (.inr message) state.1)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le).map
            (fun result => (result.2.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
              (.inr message) state result.1 result.2))
      else (originalProposalRecord key (.inr message) state.1).map (fun record =>
        (record.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inr message) state 0 record)) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk,
    certificateMonitor_sign_proposals_active, decide_eq_true_eq]
theorem certificateLengthImpl_inactive_run (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    (certificateLengthImpl key budget required stopAfter input).run state =
      (originalProposalRecord key input state.1).map (fun record =>
        (record.output, (record.cache, { state.2 with stopped := true }))) := by
  cases input with
  | inl world =>
      simp only [certificateLengthImpl_world_run, originalProposalAdvance,
        certificateMonitorUpdate_inactive key budget required stopAfter (.inl world) state 0 _ hactive]
  | inr message =>
      simp only [certificateLengthImpl_sign_run, if_neg hactive, originalProposalAdvance,
        certificateMonitorUpdate_inactive key budget required stopAfter (.inr message) state 0 _ hactive]
theorem simulateQ_certificateProposalImpl_length {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    Prod.map id Prod.snd <$> (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state =
      (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state.2 :=
  simulateQ_originalProposalImpl_length _ _ _ _ _ _
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Reference_BoundaryMessageCost ====
section

namespace SphincsSecurity.Concrete.FtsProbeSimulation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def messageHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 1 else 0
end SphincsSecurity.Concrete.FtsProbeSimulation
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
noncomputable def boundaryRun {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp ((α × SigningBoundaryTrace) × QueryCache HashSpec) :=
  ((simulateQ (romImpl.withTrace (signingBoundaryTrace parameter)) computation).run).run cache
theorem boundaryRun_forget {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$> boundaryRun parameter computation cache =
      (simulateQ romImpl computation).run cache := by
  have h := congrArg (fun comp : StateT (QueryCache HashSpec) ProbComp α => comp.run cache)
    (QueryImpl.fst_map_run_withTrace romImpl (signingBoundaryTrace parameter) computation)
  simpa only [StateT.run_map, boundaryRun] using h
theorem boundaryRun_bind {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    boundaryRun parameter (computation >>= next) cache =
      boundaryRun parameter computation cache >>= fun first =>
        (fun second => ((second.1.1, first.1.2 * second.1.2), second.2)) <$>
          boundaryRun parameter (next first.1.1) first.2 := by
  simp only [boundaryRun, simulateQ_bind, WriterT.run_bind, StateT.run_bind, StateT.run_map]
theorem boundaryRun_query (parameter : PublicParameter)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    boundaryRun parameter (OracleSpec.query input) cache =
      (fun result => ((result.1, signingBoundaryTrace parameter input result.1), result.2)) <$>
        (romImpl input).run cache := by
  simp [boundaryRun, QueryImpl.withTrace_apply]
theorem SigningBoundaryTrace.messageCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).messageCalls = first.messageCalls ++ second.messageCalls := by
  simp only [SigningBoundaryTrace.messageCalls, FreeMonoid.toList_mul, List.filterMap_append]
noncomputable def expectedBoundaryMessageCalls {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' result, Pr[= result | boundaryRun parameter computation cache] * result.1.2.messageCalls.length
@[simp] theorem expectedBoundaryMessageCalls_pure {α : Type} (parameter : PublicParameter)
    (value : α) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (pure value) cache = 0 := by
  haveI : DecidableEq (QueryCache HashSpec) := Classical.decEq _
  simp [expectedBoundaryMessageCalls, boundaryRun, SigningBoundaryTrace.messageCalls]
theorem expectedBoundaryMessageCalls_bind {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (computation >>= next) cache =
      expectedBoundaryMessageCalls parameter computation cache +
        ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
          expectedBoundaryMessageCalls parameter (next result.1) result.2 := by
  rw [expectedBoundaryMessageCalls, boundaryRun_bind, tsum_probOutput_bind_mul]
  simp_rw [tsum_probOutput_map_mul, SigningBoundaryTrace.messageCalls_mul, List.length_append,
    Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  simp only [tsum_probOutput_of_liftM_PMF, one_mul]
  rw [← boundaryRun_forget parameter computation cache, tsum_probOutput_map_mul]
  simp only [expectedBoundaryMessageCalls, mul_add, ENNReal.tsum_add]
theorem signingBoundaryTrace_messageCalls (parameter : PublicParameter)
    (input : OracleWorld.Domain) (output : OracleWorld.Range input) (cache : QueryCache HashSpec) :
    ((signingBoundaryTrace parameter input output).messageCalls.length : ENNReal) =
      hashQueryCharge (messageHashCharge parameter) cache input := by
  cases input with
  | inl input => simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, hashQueryCharge]
  | inr input =>
      by_cases hinput : FtsProbeSimulation.MessageHashInput parameter input <;>
        simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, messageHashCharge,
          hashQueryCharge, hinput]
theorem expectedBoundaryMessageCalls_query (parameter : PublicParameter)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter (OracleSpec.query input) cache =
      hashQueryCharge (messageHashCharge parameter) cache input := by
  rw [expectedBoundaryMessageCalls, boundaryRun_query, tsum_probOutput_map_mul]
  simp only [signingBoundaryTrace_messageCalls parameter input _ cache,
    ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]
theorem expectedBoundaryMessageCalls_eq_queryCharge {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls parameter computation cache =
      expectedQueryCharge (messageHashCharge parameter) computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [expectedBoundaryMessageCalls_pure, expectedQueryCharge_pure]
  | query_bind input next ih =>
      rw [expectedBoundaryMessageCalls_bind, expectedQueryCharge_query_bind,
        expectedBoundaryMessageCalls_query, simulateQ_spec_query]
      simp only [ih]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Reference_BoundaryHashEvaluation ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem SigningBoundaryTrace.hashCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).hashCalls = first.hashCalls + second.hashCalls := by
  simp only [SigningBoundaryTrace.hashCalls, FreeMonoid.toList_mul, List.length_append]
theorem signingBoundaryTrace_hashCalls_eq (parameter : PublicParameter)
    (input : OracleWorld.Domain) (output : OracleWorld.Range input) :
    (signingBoundaryTrace parameter input output).hashCalls = if input matches .inr _ then 1 else 0 := by
  cases input <;> rfl
def BoundaryHashAtLeast {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cost : Nat) : Prop :=
  ∀ cache result, result ∈ support (boundaryRun parameter computation cache) → cost ≤ result.1.2.hashCalls
theorem boundaryHashAtLeast_zero {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) : BoundaryHashAtLeast parameter computation 0 := by
  intro _ _ _
  exact Nat.zero_le _
theorem BoundaryHashAtLeast.mono {α : Type} {parameter : PublicParameter}
    {computation : OracleComp OracleWorld α} {a b : Nat}
    (h : BoundaryHashAtLeast parameter computation a) (hba : b ≤ a) :
    BoundaryHashAtLeast parameter computation b := by
  intro cache result hr
  exact hba.trans (h cache result hr)
theorem boundaryHashAtLeast_bind {α β : Type} (parameter : PublicParameter)
    (first : OracleComp OracleWorld α) (second : α → OracleComp OracleWorld β) (a b : Nat)
    (hfirst : BoundaryHashAtLeast parameter first a)
    (hsecond : ∀ value, BoundaryHashAtLeast parameter (second value) b) :
    BoundaryHashAtLeast parameter (first >>= second) (a + b) := by
  intro cache result hr
  rw [boundaryRun_bind, mem_support_bind_iff] at hr
  obtain ⟨middle, hmiddle, hr⟩ := hr
  rw [support_map] at hr
  obtain ⟨last, hlast, rfl⟩ := hr
  exact (Nat.add_le_add (hfirst cache middle hmiddle) (hsecond middle.1.1 middle.2 last hlast)).trans_eq
    (SigningBoundaryTrace.hashCalls_mul _ _).symm
theorem boundaryHashAtLeast_hash (parameter : PublicParameter) (input : HashInput) :
    BoundaryHashAtLeast parameter (oracleHash input) 1 := by
  intro cache result hr
  change result ∈ support (boundaryRun parameter
    (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) cache) at hr
  rw [boundaryRun_query, support_map] at hr
  obtain ⟨source, _, rfl⟩ := hr
  exact le_refl _
theorem boundaryHashAtLeast_tweakableHash (traceParameter parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    BoundaryHashAtLeast traceParameter
      (liftM (tweakableHash parameter domain payload : OracleComp HashSpec Digest)) 1 := by
  change BoundaryHashAtLeast traceParameter
    (oracleHash (tweakableHashInput parameter domain payload) >>= fun output => pure (truncateHash output)) 1
  exact boundaryHashAtLeast_bind traceParameter _ _ 1 0 (boundaryHashAtLeast_hash _ _)
    (fun _ => boundaryHashAtLeast_zero _ _)
theorem boundaryRun_count {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => ((result.1.1, result.1.2.hashCalls), result.2)) <$> boundaryRun parameter computation cache =
      (simulateQ romImpl (countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        map_pure, countHashQueries_pure]
      rfl
  | query_bind input next ih =>
      rw [boundaryRun_bind, boundaryRun_query, map_bind, bind_map_left,
        countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      intro reply
      simp only [Functor.map_map, bind_pure_comp, simulateQ_map, StateT.run_map]
      rw [← ih]
      simp only [Functor.map_map, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq]
      cases input <;> rfl
theorem hashQueryBound_iff_boundaryRun {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound computation cache q ↔
      ∀ result ∈ support (boundaryRun parameter computation cache), result.1.2.hashCalls ≤ q := by
  rw [hashQueryBound_iff_run, ← boundaryRun_count parameter computation cache]
  simp only [support_map, Set.forall_mem_image]
theorem boundaryRun_bind_query_bound {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (q : Nat) (cache : QueryCache HashSpec) (hbound : HashQueryBound (computation >>= next) cache q)
    (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    result.1.2.hashCalls ≤ q ∧ HashQueryBound (next result.1.1) result.2 (q - result.1.2.hashCalls) := by
  apply hashQueryBound_bind computation next cache q hbound ((result.1.1, result.1.2.hashCalls), result.2)
  rw [← boundaryRun_count parameter computation cache, support_map]
  exact ⟨result, hr, rfl⟩
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
def authenticationHashCost (lay : Layer) : Nat :=
  ∑ level : Fin maxLayerHeight, if level.val < layerHeight lay then treeNodeHashCost level.val else 0
def layerMessageHashCost (lay : Layer) : Nat :=
  if hbelow : lay.val + 1 < numLayers then
    treeNodeHashCost (layerHeight ⟨lay.val + 1, hbelow⟩)
  else ftsKeyHashCost
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete.FtsProbeSimulation
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem tweakableHashInput_tag_eq (parameter : PublicParameter) (first second : HashDomain)
    (firstPayload secondPayload : HashInput)
    (heq : tweakableHashInput parameter first firstPayload = tweakableHashInput parameter second secondPayload) :
    (hashDomainFields first).tag = (hashDomainFields second).tag := by
  simp only [tweakableHashInput] at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact congrArg TweakFields.tag (tweakBytes_eq_iff.mp htweak)
end SphincsSecurity.Concrete.FtsProbeSimulation
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem SigningBoundaryTrace.hashCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.hashCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = cost := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.hashCalls_mul, ih]
      rfl
theorem SigningBoundaryTrace.messageCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.messageCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = [] := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.messageCalls_mul, ih]
      rfl
noncomputable def boundaryEval {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : α × SigningBoundaryTrace :=
  (simulateQ (f.withTrace (fun input output => signingBoundaryTrace parameter (.inr input) output))
    computation).run
@[simp] theorem boundaryEval_pure {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : α) : boundaryEval parameter f (pure value) = (value, 1) := rfl
theorem boundaryEval_fst {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    (boundaryEval parameter f computation).1 = evalWithAnswerFn f computation := by
  exact QueryImpl.fst_map_run_withTrace f
    (fun input output => signingBoundaryTrace parameter (.inr input) output) computation
theorem boundaryEval_bind {α β : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (first : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    boundaryEval parameter f (first >>= next) =
      ((boundaryEval parameter f (next (evalWithAnswerFn f first))).1,
        (boundaryEval parameter f first).2 *
          (boundaryEval parameter f (next (evalWithAnswerFn f first))).2) := by
  simp only [boundaryEval, simulateQ_bind, WriterT.run_bind]
  rw [← boundaryEval_fst parameter f first]
  rfl
theorem boundaryEval_tweakableHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (domain : HashDomain) (payload : HashInput) (hmessage : (hashDomainFields domain).tag ≠ 12#8) :
    boundaryEval parameter f (tweakableHash parameter domain payload) =
      (truncateHash (f (tweakableHashInput parameter domain payload)), FreeMonoid.of none) := by
  have hn : ¬ FtsProbeSimulation.MessageHashInput parameter (tweakableHashInput parameter domain payload) := by
    rintro ⟨otherPayload, heq⟩
    exact hmessage (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain .message
      payload otherPayload heq.symm)
  simp [boundaryEval, tweakableHash, oracleHash, QueryImpl.withTrace_apply,
    signingBoundaryTrace_nonmessage _ _ _ hn]
  rfl
theorem boundaryEval_eq_of_snd {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) (trace : SigningBoundaryTrace)
    (htrace : (boundaryEval parameter f computation).2 = trace) :
    boundaryEval parameter f computation = (evalWithAnswerFn f computation, trace) := by
  exact Prod.ext (boundaryEval_fst _ _ _) htrace
theorem boundaryEval_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, (boundaryEval parameter f (computation i)).2 = (FreeMonoid.of none) ^ cost i) :
    boundaryEval parameter f (sequenceFin computation) =
      (fun i => evalWithAnswerFn f (computation i), (FreeMonoid.of none) ^ (∑ i, cost i)) := by
  rw [← evalWithAnswerFn_sequenceFin]
  apply boundaryEval_eq_of_snd
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, boundaryEval_bind]
      have ht := ih (fun i => computation i.succ) (fun i => cost i.succ) (fun i => hcost i.succ)
      simp only [boundaryEval_bind, boundaryEval_pure, mul_one, hcost, ht,
        Fin.sum_univ_succ, pow_add]
def layersHashCostFrom {α : Type} (layers : Layer → Option α × Nat) : Nat → Nat
  | 0 => 0
  | remaining + 1 =>
      if hlayer : remaining < numLayers then
        (layers ⟨remaining, hlayer⟩).2 +
          if (layers ⟨remaining, hlayer⟩).1.isSome then layersHashCostFrom layers remaining else 0
      else 0
def sequenceLayersHashCost {α : Type} (layers : Layer → Option α × Nat) : Nat :=
  layersHashCostFrom layers numLayers
theorem boundaryEval_chainWalk (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    boundaryEval parameter f (chainWalk parameter lay tree leaf chainIdx start steps value) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value),
        (FreeMonoid.of none) ^ steps) := by
  apply boundaryEval_eq_of_snd
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      have hstep : start + steps < chainLength - 1 := by omega
      rw [chainWalk, boundaryEval_bind, dif_pos hstep,
        boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields]), ih (by omega), pow_succ]
theorem boundaryEval_oneTimePublicKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) :
    boundaryEval parameter f (oneTimePublicKey parameter lay tree leaf secret) =
      (evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret), (FreeMonoid.of none) ^ oneTimeKeyHashCost) := by
  rw [oneTimePublicKey]
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx))
    (fun _ => chainLength - 1)
    (fun chainIdx => congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega)))
  simpa only [evalWithAnswerFn_sequenceFin, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← oneTimeKeyHashCost_def] using h
theorem boundaryEval_treeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (treeNode parameter lay tree secret level nodeIdx) =
      (evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx),
        (FreeMonoid.of none) ^ treeNodeHashCost level) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq, boundaryEval_bind, boundaryEval_oneTimePublicKey]
      simp only [leafHash, boundaryEval_tweakableHash parameter f (.leaf lay tree (leafOfNat nodeIdx)) _
        (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, treeNodeHashCost_zero]
  | succ level ih =>
      rw [treeNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih, boundaryEval_tweakableHash parameter f (.node lay tree (level + 1) nodeIdx) _
        (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, ← pow_add, treeNodeHashCost_succ]
theorem boundaryEval_treePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    boundaryEval parameter f (treePath parameter lay tree secret leaf) =
      (evalWithAnswerFn f (treePath parameter lay tree secret leaf),
        (FreeMonoid.of none) ^ authenticationHashCost lay) := by
  unfold treePath authenticationHashCost
  rw [evalWithAnswerFn_sequenceFin]
  apply boundaryEval_sequenceFin
  intro level
  split_ifs
  · exact congrArg Prod.snd (boundaryEval_treeNode _ _ _ _ _ _ _)
  · simp
theorem boundaryEval_ftsNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (ftsNode parameter index tree secret level nodeIdx) =
      (evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx),
        (FreeMonoid.of none) ^ (2 ^ (level + 1) - 1)) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq, ftsLeafHash, boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
      simp
  | succ level ih =>
      rw [ftsNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih,
        boundaryEval_tweakableHash parameter f (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx)) _
          (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, ← pow_add]
      congr 1
      have hp : 0 < 2 ^ (level + 1) := by positivity
      rw [pow_succ]
      omega
theorem boundaryEval_ftsKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    boundaryEval parameter f (ftsKey parameter index secret) =
      (evalWithAnswerFn f (ftsKey parameter index secret), (FreeMonoid.of none) ^ ftsKeyHashCost) := by
  rw [ftsKey, boundaryEval_ftsNode, ftsKeyHashCost_def]
theorem boundaryEval_layerMessage (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    boundaryEval key.parameter f (layerMessage key index lay) =
      (evalWithAnswerFn f (layerMessage key index lay), (FreeMonoid.of none) ^ layerMessageHashCost lay) := by
  rw [layerMessage, layerMessageHashCost]
  split_ifs
  · rw [treeRoot]
    exact boundaryEval_treeNode _ _ _ _ _ _ _
  · exact boundaryEval_ftsKey _ _ _ _
theorem boundaryEval_hash_query (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (input : HashInput) :
    boundaryEval parameter f (liftM (HashSpec.query input)) =
      (f input, signingBoundaryTrace parameter (.inr input) (f input)) := rfl
theorem boundaryEval_node_hash (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest) :
    (boundaryEval parameter f (tweakableHash parameter (.node lay tree level nodeIdx)
      (nodePayload left right))).2 = FreeMonoid.of none := by
  rw [boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
theorem boundaryEval_ftsNode_hash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (heapIdx : Nat) (left right : Digest) :
    (boundaryEval parameter f (tweakableHash parameter (.ftsNode index tree heapIdx)
      (nodePayload left right))).2 = FreeMonoid.of none := by
  rw [boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
theorem boundaryEval_buildLevel (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ nodeIdx left right, (boundaryEval parameter f (hashNode nodeIdx left right)).2 = FreeMonoid.of none)
    (width : Nat) (below : Nat → Digest) :
    (boundaryEval parameter f (buildLevel hashNode width below)).2 = (FreeMonoid.of none) ^ width := by
  unfold buildLevel
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => 1)
    (fun nodeIdx => by rw [hhash, pow_one])]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one]
def levelsHashCost (height : Nat) : Nat → Nat
  | 0 => 0
  | levels + 1 => levelsHashCost height levels + 2 ^ (height - (levels + 1))
theorem levelsHashCost_eq (height levels : Nat) (hlevels : levels ≤ height) :
    levelsHashCost height levels = 2 ^ height - 2 ^ (height - levels) := by
  induction levels with
  | zero => simp [levelsHashCost]
  | succ levels ih =>
      rw [levelsHashCost, ih (by omega)]
      have hpow : 2 ^ (height - levels) = 2 * 2 ^ (height - (levels + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have hle : 2 ^ (height - levels) ≤ 2 ^ height := Nat.pow_le_pow_right (by omega) (by omega)
      omega
theorem levelsHashCost_self (height : Nat) : levelsHashCost height height = 2 ^ height - 1 := by
  rw [levelsHashCost_eq height height le_rfl, Nat.sub_self, pow_zero]
theorem boundaryEval_buildLevels (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      (boundaryEval parameter f (hashNode level nodeIdx left right)).2 = FreeMonoid.of none)
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    (boundaryEval parameter f (buildLevels hashNode height leaves levels)).2 =
      (FreeMonoid.of none) ^ levelsHashCost height levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [buildLevels, boundaryEval_bind, ih, boundaryEval_bind,
        boundaryEval_buildLevel _ _ _ (hhash (levels + 1))]
      simp only [boundaryEval_pure, mul_one, levelsHashCost, pow_add]
theorem boundaryEval_buildChain_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)
    (digit : Nat) (hdigit : digit ≤ chainLength - 1) :
    (boundaryEval parameter f (buildChain parameter lay tree leaf chainIdx (pure secret) digit)).2 =
      (FreeMonoid.of none) ^ (chainLength - 1) := by
  unfold buildChain
  rw [pure_bind, boundaryEval_bind, boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega),
    boundaryEval_bind, boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega)]
  simp only [boundaryEval_pure, mul_one, ← pow_add]
  congr 1
  omega
theorem boundaryEval_buildLeaf_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLeaf parameter lay tree leaf (fun chainIdx => pure (secret chainIdx))
      digits)).2 = (FreeMonoid.of none) ^ (oneTimeKeyHashCost + 1) := by
  unfold buildLeaf
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => chainLength - 1)
    (fun chainIdx => boundaryEval_buildChain_pure _ _ _ _ _ _ _ _ (by
      have := (digits chainIdx).isLt
      simp only [chainLength, winternitzBits] at this ⊢
      omega))]
  rw [boundaryEval_bind, leafHash, boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, pow_succ, oneTimeKeyHashCost_def]
theorem boundaryEval_buildLayerTree_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLayerTree parameter lay tree
      (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits)).2 =
      (FreeMonoid.of none) ^ treeNodeHashCost (layerHeight lay) := by
  unfold buildLayerTree
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => oneTimeKeyHashCost + 1)
    (fun leafNat => boundaryEval_buildLeaf_pure _ _ _ _ _ _ _)]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _ (fun _ _ _ _ => boundaryEval_node_hash _ _ _ _ _ _ _ _),
    levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1
  rw [treeNodeHashCost_def]
  have hpos : 0 < 2 ^ layerHeight lay := Nat.two_pow_pos _
  have : (oneTimeKeyHashCost + 2) * 2 ^ layerHeight lay =
      2 ^ layerHeight lay * (oneTimeKeyHashCost + 1) + 2 ^ layerHeight lay := by ring
  omega
theorem boundaryEval_buildLayerTable_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLayerTable parameter lay tree
      (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits)).2 =
      (FreeMonoid.of none) ^ treeNodeHashCost (layerHeight lay) := by
  unfold buildLayerTable
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => oneTimeKeyHashCost + 1)
    (fun leafNat => boundaryEval_buildLeaf_pure _ _ _ _ _ _ _)]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _ (fun _ _ _ _ => boundaryEval_node_hash _ _ _ _ _ _ _ _),
    levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1
  rw [treeNodeHashCost_def]
  have hpos : 0 < 2 ^ layerHeight lay := Nat.two_pow_pos _
  have : (oneTimeKeyHashCost + 2) * 2 ^ layerHeight lay =
      2 ^ layerHeight lay * (oneTimeKeyHashCost + 1) + 2 ^ layerHeight lay := by ring
  omega
theorem boundaryEval_keygenTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenTable parameter secret) =
      (evalWithAnswerFn f (keygenTable parameter secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  apply boundaryEval_eq_of_snd
  unfold keygenTable
  rw [boundaryEval_bind, boundaryEval_buildLayerTable_pure, keygenHashCost_def]
  split
  simp only [boundaryEval_pure, mul_one]
theorem boundaryEval_keygenRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenRoot parameter secret) =
      (evalWithAnswerFn f (keygenRoot parameter secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  apply boundaryEval_eq_of_snd
  unfold keygenRoot
  rw [boundaryEval_bind, boundaryEval_buildLayerTree_pure, keygenHashCost_def]
  split
  simp only [boundaryEval_pure, mul_one]
theorem boundaryEval_buildFtsTree_pure_snd (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsLeaf → Digest) :
    (boundaryEval parameter f (buildFtsTree parameter index (fun leaf => pure (secret leaf)))).2 =
      (FreeMonoid.of none) ^ (2 ^ (ftsTreeHeight + 1) - 1) := by
  unfold buildFtsTree
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => 1)
    (fun leafIdx => by
      rw [pure_bind, boundaryEval_bind, ftsLeafHash,
        boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
      simp only [boundaryEval_pure, mul_one, pow_one])]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _
    (fun _ _ _ _ => boundaryEval_ftsNode_hash _ _ _ _ _ _ _), levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1
theorem boundaryEval_buildFtsTree_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsLeaf → Digest) :
    boundaryEval parameter f (buildFtsTree parameter index (fun leaf => pure (secret leaf))) =
      (evalWithAnswerFn f (buildFtsTree parameter index (fun leaf => pure (secret leaf))),
        (FreeMonoid.of none) ^ ftsOpenHashCost) := by
  apply boundaryEval_eq_of_snd
  rw [boundaryEval_buildFtsTree_pure_snd, ftsOpenHashCost_def]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierSigningEvaluation ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk
def referenceEncodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    Nat → Nat → Option (Counter × Encoding) × Nat
  | 0, _ => (none, 0)
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | some word => (some (BitVec.ofNat counterBits counter, word), 1)
      | none =>
          let rest := referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)
          (rest.1, 1 + rest.2)
theorem boundaryEval_encode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    boundaryEval parameter f (encodeAttempt parameter lay tree leaf message counter) =
      (evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter), FreeMonoid.of none) := by
  apply boundaryEval_eq_of_snd
  rw [encodeAttempt, boundaryEval_bind,
    boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields]), boundaryEval_pure, mul_one]
theorem boundaryEval_otsValues (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (word : Encoding) :
    boundaryEval parameter f (sequenceFin fun chainIdx =>
      chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) =
      (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)),
        (FreeMonoid.of none) ^ OtsCode.signingSteps word) := by
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))
    (fun chainIdx => (word chainIdx).val) (fun chainIdx => by
      apply congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ ?_)
      have hdigit := (word chainIdx).isLt
      omega)
  simpa only [OtsCode.signingSteps] using h
theorem boundaryEval_otsSignFrom_frontier (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret frontier : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat)
    (hfrontier : ∀ c word,
      (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 = some (c, word) →
      ∀ chainIdx, evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx) :
    boundaryEval parameter f (otsSignFrom parameter lay tree leaf secret message attempts counter) =
      ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.map
          (fun result => (result.1, frontier)),
        (FreeMonoid.of none) ^ ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).2 +
          (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.elim 0
            (fun result => OtsCode.signingSteps result.2))) := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom, referenceEncodingSearch]
  | succ attempts ih =>
      rw [otsSignFrom, boundaryEval_bind, boundaryEval_encode]
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | none =>
          have ht : ∀ c word,
              (referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)).1 = some (c, word) →
              ∀ chainIdx, evalWithAnswerFn f
                (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx := by
            intro c word hw
            apply hfrontier c word
            simpa only [referenceEncodingSearch, hencode] using hw
          rw [ih (counter + 1) ht]
          simp only [referenceEncodingSearch, hencode, Nat.add_assoc, pow_add, pow_one]
      | some word =>
          have hv : (fun chainIdx => evalWithAnswerFn f
              (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))) = frontier := by
            funext chainIdx
            exact hfrontier (BitVec.ofNat counterBits counter) word
              (by simp only [referenceEncodingSearch, hencode]) chainIdx
          rw [boundaryEval_bind, boundaryEval_otsValues]
          simp only [boundaryEval_pure, evalWithAnswerFn_sequenceFin, hv, mul_one,
            referenceEncodingSearch, hencode, Option.map_some, Option.elim_some, pow_add, pow_one]
theorem boundaryEval_encodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    boundaryEval parameter f (encodingSearch parameter lay tree leaf message attempts counter) =
      ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).1,
        (FreeMonoid.of none) ^ (referenceEncodingSearch parameter f lay tree leaf message attempts counter).2) := by
  induction attempts generalizing counter with
  | zero => simp only [encodingSearch, referenceEncodingSearch, boundaryEval_pure, pow_zero]
  | succ attempts ih =>
      rw [encodingSearch, encode_eq, boundaryEval_bind, boundaryEval_encode]
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | none =>
          rw [ih (counter + 1)]
          simp only [referenceEncodingSearch, hencode, pow_add, pow_one]
      | some word =>
          simp only [boundaryEval_pure, referenceEncodingSearch, hencode, mul_one, pow_one]
theorem eval_encodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts counter) =
      (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 := by
  rw [← boundaryEval_fst parameter f, boundaryEval_encodingSearch]
noncomputable def specLayerCost (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index)
    (lay : Layer) : Option (Counter × Encoding) × Nat :=
  let search := referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0
  (search.1, search.2 + search.1.elim 0 (fun result =>
    if lay = topLayer then OtsCode.signingSteps result.2 else treeNodeHashCost (layerHeight lay)))
theorem boundaryEval_signTopLayer (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index)
    (message : Digest) :
    (boundaryEval key.parameter f (signTopLayer key.parameter index
      (fun leaf chainIdx => pure (key.otsSecret topLayer (treeIndexAt index topLayer) leaf chainIdx))
      (fun level nodeIdx => pure (key.top level nodeIdx)) message)).2 =
      (FreeMonoid.of none) ^
        ((referenceEncodingSearch key.parameter f topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) message encodingAttemptLimit 0).2 +
        (referenceEncodingSearch key.parameter f topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) message encodingAttemptLimit 0).1.elim 0
            (fun result => OtsCode.signingSteps result.2)) := by
  unfold signTopLayer
  rw [boundaryEval_bind, boundaryEval_encodingSearch, eval_encodingSearch]
  cases (referenceEncodingSearch key.parameter f topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) message encodingAttemptLimit 0).1 with
  | none => simp only [boundaryEval_pure, mul_one, Option.elim_none, Nat.add_zero]
  | some result =>
      obtain ⟨counter, word⟩ := result
      simp only [pure_bind, Option.elim_some]
      rw [boundaryEval_bind, boundaryEval_otsValues key.parameter f topLayer (treeIndexAt index topLayer)
        (leafIndexAt index topLayer) (key.otsSecret topLayer (treeIndexAt index topLayer) (leafIndexAt index topLayer)) word,
        boundaryEval_bind, boundaryEval_sequenceFin key.parameter f _ (fun _ => 0) (fun _ => by
          rw [boundaryEval_pure, pow_zero])]
      simp only [boundaryEval_pure, mul_one, Finset.sum_const_zero, pow_zero, pow_add]
theorem boundaryEval_signLayers (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index)
    (remaining : Nat) (hremaining : remaining ≤ numLayers) (message : Digest)
    (hmessage : ∀ h : 0 < remaining,
      message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩)) :
    (boundaryEval key.parameter f (signLayers key.parameter index
      (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
      (fun level nodeIdx => pure (key.top level nodeIdx)) remaining message)).2 =
      (FreeMonoid.of none) ^ layersHashCostFrom (specLayerCost key f index) remaining := by
  induction remaining generalizing message with
  | zero => simp only [signLayers, boundaryEval_pure, layersHashCostFrom, pow_zero]
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      let lay : Layer := ⟨remaining, hlayer⟩
      have hmsg : message = evalWithAnswerFn f (layerMessage key index lay) := hmessage (by omega)
      by_cases hzero : remaining = 0
      · subst hzero
        have hlay : lay = topLayer := rfl
        rw [signLayers, dif_pos hlayer, if_pos rfl, layersHashCostFrom, dif_pos hlayer, boundaryEval_bind,
          boundaryEval_signTopLayer]
        change _ = (FreeMonoid.of none) ^ ((specLayerCost key f index topLayer).2 +
          if (specLayerCost key f index topLayer).1.isSome then layersHashCostFrom (specLayerCost key f index) 0
            else 0)
        have hcost : (specLayerCost key f index topLayer).2 =
            (referenceEncodingSearch key.parameter f topLayer (treeIndexAt index topLayer)
              (leafIndexAt index topLayer) message encodingAttemptLimit 0).2 +
            (referenceEncodingSearch key.parameter f topLayer (treeIndexAt index topLayer)
              (leafIndexAt index topLayer) message encodingAttemptLimit 0).1.elim 0
                (fun result => OtsCode.signingSteps result.2) := by
          simp only [specLayerCost, ← hlay, ← hmsg, if_pos hlay, if_true]
        rw [hcost, layersHashCostFrom, ite_self, Nat.add_zero]
        split <;> simp only [boundaryEval_pure, mul_one]
      rw [signLayers, dif_pos hlayer, if_neg hzero, layersHashCostFrom, dif_pos hlayer, boundaryEval_bind,
        boundaryEval_encodingSearch, eval_encodingSearch]
      simp only [show (⟨remaining, hlayer⟩ : Layer) = lay from rfl]
      change _ = (FreeMonoid.of none) ^ ((specLayerCost key f index lay).2 +
        if (specLayerCost key f index lay).1.isSome then layersHashCostFrom (specLayerCost key f index) remaining else 0)
      have hnottop : lay ≠ topLayer := fun h => hzero (congrArg Fin.val h)
      simp only [specLayerCost, ← hmsg, if_neg hnottop]
      cases hsearch : (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay)
          (leafIndexAt index lay) message encodingAttemptLimit 0).1 with
      | none =>
          simp only [boundaryEval_pure, mul_one, Option.elim_none, Nat.add_zero,
            Option.isSome_none, Bool.false_eq_true, if_false]
      | some result =>
          obtain ⟨counter, word⟩ := result
          simp only [Option.elim_some, Option.isSome_some, if_true]
          have hroot := eval_buildLayerTree_root f key.parameter lay (treeIndexAt index lay)
            (fun leaf chainIdx => pure (key.otsSecret lay (treeIndexAt index lay) leaf chainIdx))
            (leafIndexAt index lay) (leafIndexAt_lt index lay) word
          rw [boundaryEval_bind, boundaryEval_buildLayerTree_pure]
          revert hroot
          generalize evalWithAnswerFn f (buildLayerTree key.parameter lay (treeIndexAt index lay)
            (fun leaf chainIdx => pure (key.otsSecret lay (treeIndexAt index lay) leaf chainIdx))
            (leafIndexAt index lay) word) = built
          rcases built with ⟨values, path, root⟩
          intro hroot
          simp only [evalWithAnswerFn_pure] at hroot
          have hnext : ∀ h : 0 < remaining,
              root = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩) := by
            intro h
            have hbelow : remaining - 1 + 1 < numLayers := by omega
            rw [layerMessage, dif_pos hbelow]
            have hl : (⟨remaining - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl, hroot]
          rw [boundaryEval_bind, ih (by omega) root hnext]
          cases evalWithAnswerFn f (signLayers key.parameter index
              (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
              (fun level nodeIdx => pure (key.top level nodeIdx)) remaining root) <;>
            simp only [boundaryEval_pure, mul_one, pow_add, mul_assoc]
theorem boundaryEval_signAfterDigest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    (boundaryEval key.parameter f (signAfterDigest key randomness index leaves)).2 =
      (FreeMonoid.of none) ^ (ftsOpenHashCost + sequenceLayersHashCost (specLayerCost key f index)) := by
  have hforest := eval_buildFtsTree_open f key.parameter index
    (fun leaf => pure (key.ftsSecret index porsTree leaf)) leaves
  rw [signAfterDigest_eq_signFrom, signFrom, boundaryEval_bind, boundaryEval_buildFtsTree_pure]
  revert hforest
  generalize evalWithAnswerFn f (buildFtsTree key.parameter index
    (fun leaf => pure (key.ftsSecret index porsTree leaf))) = built
  rcases built with ⟨secrets, table⟩
  rintro ⟨_, hkey⟩
  have htable : (fun (_ : FtsTree) leaf => evalWithAnswerFn f
      (pure (key.ftsSecret index porsTree leaf) : OracleComp HashSpec Digest)) = key.ftsSecret index := by
    funext tree leaf
    rw [Subsingleton.elim tree porsTree]
    rfl
  simp only [htable] at hkey
  rw [boundaryEval_bind, boundaryEval_signLayers key f index numLayers le_rfl (table ftsTreeHeight 0) (by
    intro _
    rw [hkey]
    change _ = evalWithAnswerFn f (layerMessage key index bottomLayer)
    rw [layerMessage_bottomLayer_eq])]
  cases evalWithAnswerFn f (signLayers key.parameter index
      (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
      (fun level nodeIdx => pure (key.top level nodeIdx)) numLayers (table ftsTreeHeight 0)) <;>
    simp only [boundaryEval_pure, mul_one, pow_add, sequenceLayersHashCost]
theorem boundaryEval_signAfterDigest_eq (key : SecretKey) (f : QueryImpl HashSpec Id)
    (htop : KeyTopHonest f key)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      (signatureValue f key randomness index leaves,
        (FreeMonoid.of none) ^ (ftsOpenHashCost + sequenceLayersHashCost (specLayerCost key f index))) := by
  rw [← eval_signAfterDigest f key htop randomness index leaves]
  exact boundaryEval_eq_of_snd _ _ _ _ (boundaryEval_signAfterDigest key f randomness index leaves)
theorem boundaryEval_keygen (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenTable parameter secret) =
      (evalWithAnswerFn f (keygenTable parameter secret), (FreeMonoid.of none) ^ keygenHashCost) :=
  boundaryEval_keygenTable parameter f secret
theorem boundaryEval_keygenRoot_eq (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenRoot parameter secret) =
      (evalWithAnswerFn f (treeRoot parameter topLayer rootTree secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  rw [boundaryEval_keygenRoot, eval_keygenRoot]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_FrontierSignerErasure ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def frontierOneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (digits : Encoding) (frontier : ChainIndex → Digest) :
    OracleComp HashSpec (ChainIndex → Digest) :=
  sequenceFin fun chainIdx => recoverChain parameter lay tree leaf chainIdx (digits chainIdx) (frontier chainIdx)
def frontierTreeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) :
    Nat → Nat → OracleComp HashSpec Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← frontierTreeNode parameter lay tree digits frontier level (2 * nodeIdx)
      let right ← frontierTreeNode parameter lay tree digits frontier level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)
def frontierTreePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    OracleComp HashSpec (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      frontierTreeNode parameter lay tree digits frontier level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else pure 0
def IsOtsFrontier (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) : Prop :=
  ∀ leaf chainIdx, evalWithAnswerFn f
    (chainWalk parameter lay tree leaf chainIdx 0 (digits leaf chainIdx).val (secret leaf chainIdx)) =
      frontier leaf chainIdx
theorem eval_frontierOneTimePublicKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret frontier : ChainIndex → Digest)
    (digits : Encoding)
    (hfrontier : ∀ chainIdx, evalWithAnswerFn f
      (chainWalk parameter lay tree leaf chainIdx 0 (digits chainIdx).val (secret chainIdx)) = frontier chainIdx) :
    evalWithAnswerFn f (frontierOneTimePublicKey parameter lay tree leaf digits frontier) =
      evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret) := by
  simp only [frontierOneTimePublicKey, evalWithAnswerFn_sequenceFin, eval_oneTimePublicKey]
  funext chainIdx
  rw [← hfrontier chainIdx, eval_recoverChain]
theorem eval_frontierTreeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest)
    (hfrontier : IsOtsFrontier parameter f lay tree secret digits frontier) (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree digits frontier level nodeIdx) =
      evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [frontierTreeNode, treeNode_zero_eq, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
        eval_frontierOneTimePublicKey _ _ _ _ _ _ _ _ (hfrontier _)]
  | succ level ih =>
      simp only [frontierTreeNode, treeNode_succ_eq, evalWithAnswerFn_bind, ih]
theorem eval_frontierTreePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest)
    (hfrontier : IsOtsFrontier parameter f lay tree secret digits frontier) (leaf : LeafIndex) :
    evalWithAnswerFn f (frontierTreePath parameter lay tree digits frontier leaf) =
      evalWithAnswerFn f (treePath parameter lay tree secret leaf) := by
  simp only [frontierTreePath, treePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact eval_frontierTreeNode _ _ _ _ _ _ _ hfrontier _ _
  · rfl
theorem eval_chainWalk_congr_tail (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1)
    (hhash : ∀ (step : Fin (chainLength - 1)), start ≤ step.val → ∀ input : Digest,
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))) =
        truncateHash (g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input)))) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) =
      evalWithAnswerFn g (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hstep : start + steps < chainLength - 1 := by omega
      simp only [chainWalk, evalWithAnswerFn_bind, dif_pos hstep, eval_tweakableHash]
      rw [ih (by omega)]
      exact hhash ⟨start + steps, hstep⟩ (Nat.le_add_right start steps) _
theorem eval_frontierTreeNode_congr (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (digits : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : Fin (chainLength - 1)),
      (digits leaf chainIdx).val ≤ step.val → ∀ input : Digest,
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))) =
        truncateHash (g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))))
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload)) =
        truncateHash (g (tweakableHashInput parameter (.leaf lay tree leaf) payload)))
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      truncateHash (f (tweakableHashInput parameter (.node lay tree level nodeIdx) payload)) =
        truncateHash (g (tweakableHashInput parameter (.node lay tree level nodeIdx) payload)))
    (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree digits frontier level nodeIdx) =
      evalWithAnswerFn g (frontierTreeNode parameter lay tree digits frontier level nodeIdx) := by
  have hkey : ∀ leaf, evalWithAnswerFn f
      (frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)) =
        evalWithAnswerFn g (frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)) := by
    intro leaf
    simp only [frontierOneTimePublicKey, evalWithAnswerFn_sequenceFin]
    funext chainIdx
    apply eval_chainWalk_congr_tail _ _ _ _ _ _ _ _ _ _ _ (hchain leaf chainIdx)
    have hdigit := (digits leaf chainIdx).isLt
    omega
  induction level generalizing nodeIdx with
  | zero =>
      simp only [frontierTreeNode, evalWithAnswerFn_bind, leafHash, eval_tweakableHash]
      rw [hkey]
      exact hleaf _ _
  | succ level ih =>
      simp only [frontierTreeNode, evalWithAnswerFn_bind, eval_tweakableHash, ih]
      exact hnode _ _ _
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk referenceEncodingSearch
abbrev OtsReferenceWords := Layer → TreeIndex → LeafIndex → Encoding
abbrev OtsFrontierValues := Layer → TreeIndex → LeafIndex → ChainIndex → Digest
def IsSigningFrontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) : Prop :=
  ∀ lay tree, IsOtsFrontier key.parameter f lay tree (key.otsSecret lay tree) (words lay tree) (frontier lay tree)
def frontierLayerMessage (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    OracleComp HashSpec Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    frontierTreeNode parameter below (treeIndexAt index below)
      (words below (treeIndexAt index below)) (frontier below (treeIndexAt index below)) (layerHeight below) 0
  else ftsKey parameter index (ftsSecret index)
def frontierLayerSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret words frontier index lay)) encodingAttemptLimit 0
def FrontierReferenceWord (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Prop :=
  ∀ counter word, (frontierLayerSearch parameter f ftsSecret words frontier index lay).1 = some (counter, word) →
    word = words lay (treeIndexAt index lay) (leafIndexAt index lay)
def frontierSignLayer (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option LayerPart × Nat :=
  let search := frontierLayerSearch parameter f ftsSecret words frontier index lay
  match search.1 with
  | none => (none, search.2)
  | some (counter, word) =>
      (some (counter, frontier lay (treeIndexAt index lay) (leafIndexAt index lay),
        evalWithAnswerFn f (frontierTreePath parameter lay (treeIndexAt index lay)
          (words lay (treeIndexAt index lay)) (frontier lay (treeIndexAt index lay)) (leafIndexAt index lay))),
        search.2 + if lay = topLayer then OtsCode.signingSteps word else treeNodeHashCost (layerHeight lay))
theorem eval_frontierLayerMessage (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (frontierLayerMessage key.parameter key.ftsSecret words frontier index lay) =
      evalWithAnswerFn f (layerMessage key index lay) := by
  unfold frontierLayerMessage layerMessage
  split_ifs
  · rw [treeRoot]
    exact eval_frontierTreeNode _ _ _ _ _ _ _ (hfrontier _ _) _ _
  · rfl
theorem eval_signLayer_search (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (signLayer key index lay) =
      (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1.map fun result =>
          (result.1, fun chainIdx => evalWithAnswerFn f
            (chainWalk key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx 0
              (result.2 chainIdx).val (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)),
            evalWithAnswerFn f (treePath key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))) := by
  simp only [signLayer, evalWithAnswerFn_bind, otsSign, eval_otsSignFrom, eval_encodingSearch]
  cases (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1 with
  | none => rfl
  | some result => simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem specLayerCost_isSome (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    (specLayerCost key f index lay).1.isSome = (evalWithAnswerFn f (signLayer key index lay)).isSome := by
  rw [eval_signLayer_search, specLayerCost, Option.isSome_map]
theorem layersHashCostFrom_congr {α β : Type} (A : Layer → Option α × Nat) (B : Layer → Option β × Nat)
    (hcost : ∀ lay, (A lay).2 = (B lay).2) (hsome : ∀ lay, (A lay).1.isSome = (B lay).1.isSome)
    (remaining : Nat) : layersHashCostFrom A remaining = layersHashCostFrom B remaining := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      simp only [layersHashCostFrom, ih, hcost, hsome]
theorem frontierSignLayer_eq_spec (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer)
    (hword : FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    frontierSignLayer key.parameter f key.ftsSecret words frontier index lay =
      (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2) := by
  have hsearch : frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay =
      referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0 := by
    rw [frontierLayerSearch, eval_frontierLayerMessage key f words frontier hfrontier]
  have hpath := (eval_frontierTreePath key.parameter f lay (treeIndexAt index lay)
    (key.otsSecret lay (treeIndexAt index lay)) (words lay (treeIndexAt index lay))
    (frontier lay (treeIndexAt index lay)) (hfrontier _ _) (leafIndexAt index lay))
  have hspec := eval_signLayer_search key f index lay
  rw [hspec, specLayerCost]
  simp only [frontierSignLayer]
  rw [hsearch]
  cases hs : (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1 with
  | none => simp only [Option.map_none, Option.elim_none, Nat.add_zero]
  | some result =>
      obtain ⟨counter, word⟩ := result
      have hw : word = words lay (treeIndexAt index lay) (leafIndexAt index lay) :=
        hword counter word (by rw [hsearch]; exact hs)
      simp only [Option.map_some, Option.elim_some, hpath, Prod.mk.injEq, Option.some.injEq, and_true,
        true_and]
      funext chainIdx
      rw [hw]
      exact (hfrontier _ _ _ _).symm
def frontierSignAfterDigest (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Option Signature × Nat :=
  let layers := fun lay => frontierSignLayer parameter f ftsSecret words frontier index lay
  let paths := evalWithAnswerFn f (ftsOpen parameter index leaves (ftsSecret index))
  ((sequenceFin (m := Option) (fun lay => (layers lay).1)).map (fun parts =>
      { randomness := randomness
        fts := paths
        layers := fun lay => LayerSignature.ofPadded lay (parts lay) }),
    ftsOpenHashCost + sequenceLayersHashCost layers)
theorem boundaryEval_signAfterDigest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hwords : ∀ lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      ((frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).1,
        (FreeMonoid.of none) ^
          (frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).2) := by
  have hlayers : (fun lay => frontierSignLayer key.parameter f key.ftsSecret words frontier index lay) =
      fun lay => (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2) :=
    funext fun lay => frontierSignLayer_eq_spec key f words frontier hfrontier index lay (hwords lay)
  have hcost : sequenceLayersHashCost (fun lay => frontierSignLayer key.parameter f key.ftsSecret words frontier index lay) =
      sequenceLayersHashCost (specLayerCost key f index) := by
    rw [hlayers]
    exact layersHashCostFrom_congr
      (fun lay => (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2))
      (specLayerCost key f index) (fun _ => rfl) (fun lay => (specLayerCost_isSome key f index lay).symm) _
  rw [boundaryEval_signAfterDigest_eq key f htop]
  simp only [frontierSignAfterDigest, hcost, signatureValue]
  congr 2
  simp only [hlayers]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_CanonicalSigningFrontier ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] referenceEncodingSearch chainWalk boundaryEval
set_option backward.isDefEq.respectTransparency false
noncomputable def referenceIndex (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Index :=
  if h : ∃ index, treeIndexAt index lay = tree ∧ leafIndexAt index lay = leaf then Classical.choose h else 0
theorem referenceIndex_position (index : Index) (lay : Layer) :
    treeIndexAt (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay = treeIndexAt index lay ∧
      leafIndexAt (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay = leafIndexAt index lay := by
  have h : ∃ source, treeIndexAt source lay = treeIndexAt index lay ∧
      leafIndexAt source lay = leafIndexAt index lay := ⟨index, rfl, rfl⟩
  rw [referenceIndex, dif_pos h]
  exact Classical.choose_spec h
theorem layerMessage_referenceIndex (key : SecretKey) (index : Index) (lay : Layer) :
    layerMessage (m := OracleComp HashSpec) key
        (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay =
      layerMessage key index lay :=
  layerMessage_eq_of_position_eq key _ index lay (referenceIndex_position index lay).1
    (referenceIndex_position index lay).2
noncomputable def canonicalEncodingSearch (key : SecretKey) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch key.parameter f lay tree leaf
    (evalWithAnswerFn f (layerMessage key (referenceIndex lay tree leaf) lay)) encodingAttemptLimit 0
theorem canonicalEncodingSearch_at (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    canonicalEncodingSearch key f lay (treeIndexAt index lay) (leafIndexAt index lay) =
      referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0 := by
  rw [canonicalEncodingSearch, layerMessage_referenceIndex]
noncomputable def canonicalReferenceWords (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf => ((canonicalEncodingSearch key f lay tree leaf).1.map Prod.snd).getD (dummy lay tree leaf)
noncomputable def canonicalFrontierValues (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chainIdx => evalWithAnswerFn f
    (chainWalk key.parameter lay tree leaf chainIdx 0 (words lay tree leaf chainIdx).val
      (key.otsSecret lay tree leaf chainIdx))
theorem isSigningFrontier_canonical (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) :
    IsSigningFrontier key f words (canonicalFrontierValues key f words) := fun _ _ _ _ => rfl
theorem frontierReferenceWord_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (index : Index) (lay : Layer) :
    FrontierReferenceWord key.parameter f key.ftsSecret (canonicalReferenceWords key f dummy)
      (canonicalFrontierValues key f (canonicalReferenceWords key f dummy)) index lay := by
  intro counter word hword
  rw [frontierLayerSearch, eval_frontierLayerMessage key f _ _ (isSigningFrontier_canonical key f _) index lay,
    ← canonicalEncodingSearch_at] at hword
  simp only [canonicalReferenceWords, hword, Option.map_some, Option.getD_some]
theorem referenceEncodingSearch_valid (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (attempts start : Nat) (counter : Counter) (word : Encoding)
    (hword : (referenceEncodingSearch parameter f lay tree leaf message attempts start).1 = some (counter, word)) :
    OtsCode.Valid word := by
  induction attempts generalizing start with
  | zero => simp [referenceEncodingSearch] at hword
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits start)) with
      | none =>
          apply ih (start + 1)
          simpa only [referenceEncodingSearch, hencode] using hword
      | some selected =>
          simp only [referenceEncodingSearch, hencode, Option.some.injEq, Prod.mk.injEq] at hword
          apply OtsCode.decode_valid
          simpa only [encodeAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hword.2] using hencode
theorem canonicalReferenceWords_valid (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) :
    ∀ lay tree leaf, OtsCode.Valid (canonicalReferenceWords key f dummy lay tree leaf) := by
  intro lay tree leaf
  cases hsearch : (canonicalEncodingSearch key f lay tree leaf).1 with
  | none => simpa only [canonicalReferenceWords, hsearch, Option.map_none, Option.getD_none] using hdummy lay tree leaf
  | some selected =>
      obtain ⟨counter, word⟩ := selected
      simp only [canonicalReferenceWords, hsearch, Option.map_some, Option.getD_some]
      exact referenceEncodingSearch_valid _ _ _ _ _ _ _ _ _ _ hsearch
theorem boundaryEval_signAfterDigest_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (htop : KeyTopHonest f key) (dummy : OtsReferenceWords) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    let words := canonicalReferenceWords key f dummy
    let frontier := canonicalFrontierValues key f words
    let projected := frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      (projected.1, (FreeMonoid.of none) ^ projected.2) :=
  boundaryEval_signAfterDigest_frontier key f _ _ (isSigningFrontier_canonical key f _) htop randomness index leaves
    (frontierReferenceWord_canonical key f dummy index)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Reference_FixedHashBoundary ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk referenceEncodingSearch signDigestLoop
noncomputable def fixedHashWorld (f : QueryImpl HashSpec Id) : QueryImpl OracleWorld ProbComp
  | .inl input => liftM (unifSpec.query input)
  | .inr input => pure (f input)
noncomputable def fixedBoundaryRun {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) : ProbComp (α × SigningBoundaryTrace) :=
  (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter)) computation).run
theorem fixedBoundaryRun_pure {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (value : α) :
    fixedBoundaryRun parameter f (pure value) = pure (value, 1) := rfl
theorem fixedBoundaryRun_bind {α β : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    fixedBoundaryRun parameter f (first >>= next) =
      fixedBoundaryRun parameter f first >>= fun result =>
        (fun final => (final.1, result.2 * final.2)) <$> fixedBoundaryRun parameter f (next result.1) := by
  simp only [fixedBoundaryRun, simulateQ_bind, WriterT.run_bind]
theorem fixedBoundaryRun_map {α β : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (g : α → β) :
    fixedBoundaryRun parameter f (g <$> computation) =
      (Prod.map g id) <$> fixedBoundaryRun parameter f computation := by
  simp only [fixedBoundaryRun, simulateQ_map, WriterT.run_map]
  rfl
theorem fixedBoundaryRun_forget {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    Prod.fst <$> fixedBoundaryRun parameter f computation = simulateQ (fixedHashWorld f) computation :=
  QueryImpl.fst_map_run_withTrace (fixedHashWorld f) (signingBoundaryTrace parameter) computation
theorem fixedBoundaryRun_lift_hash {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    fixedBoundaryRun parameter f (liftM computation) = pure (boundaryEval parameter f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [liftM_pure, fixedBoundaryRun_pure, boundaryEval_pure]
  | query_bind input next ih =>
      rw [liftM_bind, fixedBoundaryRun_bind, boundaryEval_bind, boundaryEval_hash_query]
      have hquery : fixedBoundaryRun parameter f
          (liftM (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)) =
          pure (f input, signingBoundaryTrace parameter (.inr input) (f input)) := by
        change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
          (liftM (OracleWorld.query (.inr input)))).run = _
        rw [simulateQ_spec_query]
        rfl
      rw [hquery, pure_bind, ih, map_pure]
      rfl
def publicSignAttempt (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest parameter root message randomness
  if Admissible digest then pure (some (digestIndex digest, digestLeaves digest)) else pure none
noncomputable def publicDigestLoop (parameter : PublicParameter) (root : Digest) (message : Message) :
    Nat → OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0 => pure none
  | attempts + 1 => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM (publicSignAttempt parameter root message randomness)
      match attempt with
      | none => publicDigestLoop parameter root message attempts
      | some (index, leaves) => pure (some (randomness, index, leaves))
theorem publicDigestLoop_eq (key : SecretKey) (message : Message) (attempts : Nat) :
    publicDigestLoop key.parameter key.root message attempts = signDigestLoop attempts key message := by
  induction attempts with
  | zero => rw [publicDigestLoop, signDigestLoop]
  | succ attempts ih =>
      rw [publicDigestLoop, signDigestLoop]
      apply bind_congr
      intro randomness
      have hattempt : publicSignAttempt key.parameter key.root message randomness =
          (signAttempt key message randomness : OracleComp HashSpec _) := rfl
      rw [hattempt]
      apply bind_congr
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected => rfl
noncomputable def frontierSigningRecord (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (message : Message) :
    ProbComp ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let selected ← fixedBoundaryRun parameter f (publicDigestLoop parameter root message digestAttemptLimit)
  match selected.1 with
  | none => pure ((none, none), selected.2)
  | some (randomness, index, leaves) =>
      let result := frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves
      pure ((result.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ result.2)
theorem fixedBoundaryRun_signWithView_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (message : Message) :
    fixedBoundaryRun key.parameter f (signWithView key message) =
      frontierSigningRecord key.parameter key.root f key.ftsSecret words frontier message := by
  rw [signWithView, fixedBoundaryRun_bind, frontierSigningRecord, publicDigestLoop_eq]
  apply bind_congr
  rintro ⟨selected, trace⟩
  cases selected with
  | none => simp only [fixedBoundaryRun_pure, map_pure, mul_one]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      rw [fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash,
        boundaryEval_signAfterDigest_frontier key f words frontier hfrontier htop randomness index leaves (hwords index)]
      simp only [pure_bind, fixedBoundaryRun_pure, map_pure, mul_one]
theorem fixedBoundaryRun_signWithView_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (htop : KeyTopHonest f key) (dummy : OtsReferenceWords) (message : Message) :
    fixedBoundaryRun key.parameter f (signWithView key message) =
      frontierSigningRecord key.parameter key.root f key.ftsSecret (canonicalReferenceWords key f dummy)
        (canonicalFrontierValues key f (canonicalReferenceWords key f dummy)) message :=
  fixedBoundaryRun_signWithView_frontier key f _ _ (isSigningFrontier_canonical key f _) htop
    (frontierReferenceWord_canonical key f dummy) message
noncomputable def frontierSigningRun (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (message : Message) : ProbComp (Option Signature × SigningBoundaryTrace) :=
  (Prod.map Prod.fst id) <$> frontierSigningRecord parameter root f ftsSecret words frontier message
theorem fixedBoundaryRun_sign_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (message : Message) :
    fixedBoundaryRun key.parameter f (sign key message) =
      frontierSigningRun key.parameter key.root f key.ftsSecret words frontier message := by
  rw [← signWithView_fst, fixedBoundaryRun_map, fixedBoundaryRun_signWithView_frontier key f words frontier hfrontier htop hwords]
  rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Reference_FiniteHashWorld ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)
noncomputable def sampleHashTable (inputs : Finset HashInput) : ProbComp (inputs → HashOutput) :=
  $ᵗ (inputs → HashOutput)
theorem evalDist_finiteHashTable_extract {α : Type} (inputs : Finset HashInput) (input : inputs)
    (next : (inputs → HashOutput) → HashOutput → ProbComp α) :
    𝒮[do let table ← ($ᵗ (inputs → HashOutput) : ProbComp _); next table (table input)] =
      𝒮[do
        let output ← ($ᵗ HashOutput : ProbComp _)
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        next (Function.update table input output) output] := by
  classical
  have h := congrArg (fun distribution : SPMF (inputs → HashOutput) =>
    distribution >>= fun table => 𝒮[next table (table input)])
    (evalSPMF_uniformSample_bind_update (R := HashOutput) input)
  simpa only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind, Function.update_self] using h.symm
noncomputable def hashInputs {α : Type} (computation : OracleComp OracleWorld α) : Finset HashInput := by
  classical
  induction computation using OracleComp.construct with
  | pure _ => exact ∅
  | query_bind input _ tail =>
      exact (match input with | .inl _ => ∅ | .inr input => {input}) ∪ Finset.univ.biUnion tail
@[simp] theorem hashInputs_pure {α : Type} (value : α) :
    hashInputs (pure value) = ∅ := rfl
theorem hashInputs_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    hashInputs (liftM (OracleWorld.query input) >>= next) =
      (match input with | .inl _ => ∅ | .inr input => {input}) ∪
        Finset.univ.biUnion (fun output => hashInputs (next output)) := by
  simp only [hashInputs, OracleComp.construct_query_bind]
  cases input <;> rfl
attribute [local irreducible] hashInputs
theorem hashInputs_next_subset {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (output : OracleWorld.Range input) :
    hashInputs (next output) ⊆ hashInputs (liftM (OracleWorld.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨output, Finset.mem_univ _, hrow⟩)
theorem mem_hashInputs_hash_bind {α : Type} (input : HashInput)
    (next : HashOutput → OracleComp OracleWorld α) :
    input ∈ hashInputs (liftM (OracleWorld.query (.inr input)) >>= next) := by
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inl (Finset.mem_singleton_self _)
noncomputable def finiteHashAnswer (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD (if h : input ∈ inputs then table ⟨input, h⟩ else 0)
theorem finiteHashAnswer_some (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (output : HashOutput) (h : cache input = some output) :
    finiteHashAnswer cache inputs table input = output := by
  simp only [finiteHashAnswer, h, Option.getD_some]
theorem finiteHashAnswer_none (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (hin : input ∈ inputs) (h : cache input = none) :
    finiteHashAnswer cache inputs table input = table ⟨input, hin⟩ := by
  simp only [finiteHashAnswer, h, Option.getD_none, dif_pos hin]
theorem finiteHashAnswer_cacheQuery (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (hin : input ∈ inputs)
    (h : cache input = none) (output : HashOutput) :
    finiteHashAnswer (cache.cacheQuery input output) inputs table =
      finiteHashAnswer cache inputs (Function.update table ⟨input, hin⟩ output) := by
  classical
  funext row
  by_cases heq : row = input
  · subst row
    simp [finiteHashAnswer, h, hin]
  · by_cases hrow : row ∈ inputs
    · have hne : (⟨row, hrow⟩ : inputs) ≠ ⟨input, hin⟩ := fun hsub => heq (congrArg Subtype.val hsub)
      simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow, hne]
    · simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow]
theorem romRun_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM (OracleWorld.query input) >>= next)).run' cache =
      (romImpl input).run cache >>= fun result => (simulateQ romImpl (next result.1)).run' result.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl
theorem evalDist_romRun_eq_finiteHash {α : Type} (computation : OracleComp OracleWorld α)
    (inputs : Finset HashInput) (hinputs : hashInputs computation ⊆ inputs) (cache : QueryCache HashSpec) :
    𝒮[(simulateQ romImpl computation).run' cache] =
      𝒮[do
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) computation] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (evalSPMF_bind_const_neverFails _ (by simp) (pure value)).symm
  | query_bind input next ih =>
      have hnext : ∀ output, hashInputs (next output) ⊆ inputs :=
        fun output => (hashInputs_next_subset input next output).trans hinputs
      rw [romRun_query_bind]
      cases input with
      | inl sample =>
          change 𝒮[(liftM (unifSpec.query sample) : ProbComp _) >>= fun output =>
            (simulateQ romImpl (next output)).run' cache] = _
          trans 𝒮[do
            let output ← (liftM (unifSpec.query sample) : ProbComp _)
            let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
            simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) (next output)]
          · exact evalSPMF_bind_congr_left _ _ _ (fun output => ih output (hnext output) cache)
          · rw [evalSPMF_bind_comm]
            apply evalSPMF_bind_congr_left
            intro table
            simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld]
            rfl
      | inr input =>
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [show romImpl (.inr input) = randomOracle (spec := HashSpec) input from rfl]
          cases hcache : cache input with
          | some output =>
              rw [QueryImpl.withCaching_run_some _ hcache, pure_bind, ih output (hnext output) cache]
              apply evalSPMF_bind_congr_left
              intro table
              simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld,
                finiteHashAnswer_some cache inputs table input output hcache, pure_bind]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hcache, map_eq_bind_pure_comp]
              simp only [Function.comp, bind_assoc, pure_bind]
              trans 𝒮[do
                let output ← ($ᵗ HashOutput : ProbComp _)
                let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
                simulateQ (fixedHashWorld (finiteHashAnswer (cache.cacheQuery input output) inputs table)) (next output)]
              · exact evalSPMF_bind_congr_left _ _ _ (fun output => ih output (hnext output) _)
              · simp_rw [finiteHashAnswer_cacheQuery cache inputs _ input hin hcache]
                rw [← evalDist_finiteHashTable_extract inputs (⟨input, hin⟩ : inputs)
                  (fun table output => simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) (next output))]
                apply evalSPMF_bind_congr_left
                intro table
                simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld,
                  finiteHashAnswer_none cache inputs table input hin hcache, pure_bind]
end SphincsSecurity.Concrete
end
