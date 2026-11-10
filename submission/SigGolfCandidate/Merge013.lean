import Mathlib.Tactic
import VCVio.OracleComp.Constructions.SampleableType
import SigGolfCandidate.Merge002
import SigGolfCandidate.Merge012

-- ==== merged from T3_Gate6_ProductFibres ====
section

section
namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
set_option maxHeartbeats 3000000
abbrev Address := Fin (2^31)
abbrev Bank := Fin 7
abbrev Bucket := Fin 16
abbrev MarkedLabel := Address × (Bank → Bucket)
theorem markedLabel_card : Fintype.card MarkedLabel = 2^59 := by
  norm_num [MarkedLabel,Address,Bank,Bucket,Fintype.card_prod,Fintype.card_fun]
abbrev Triple := Fin 3 → Fin 128
abbrev Slots := Bank → Triple
abbrev Padding := Fin 8
abbrev Unused := Fin (2^47)
abbrev Payload := Slots × (Padding × Unused)
abbrev RawRecord := MarkedLabel × Payload
def slotSet (v : Triple) : Finset Nat := (valList v).toFinset
def childAuth (v : Triple) : Nat := octH 7 (slotSet v).sort
def SlotsAccepted (slots : Slots) : Prop :=
  (∀ bank, Function.Injective (slots bank)) ∧ (∑ bank, childAuth (slots bank)) ≤ 87
def PayloadAccepted (payload : Payload) : Prop :=
  payload.2.1 = 0 ∧ SlotsAccepted payload.1
def Accepted (raw : RawRecord) : Prop := PayloadAccepted raw.2
noncomputable instance : DecidablePred SlotsAccepted := Classical.decPred _
noncomputable instance : DecidablePred PayloadAccepted := Classical.decPred _
noncomputable instance : DecidablePred Accepted := Classical.decPred _
theorem rawRecord_card : Fintype.card RawRecord = 2^256 := by
  norm_num [RawRecord,Payload,Slots,Triple,Padding,Unused,MarkedLabel,Address,Bank,Bucket,
    Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
theorem payload_card : Fintype.card Payload = 2^197 := by
  norm_num [Payload,Slots,Triple,Padding,Unused,Bank,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
def witnessTriple : Triple := fun i => ⟨i.val,by omega⟩
theorem witness_injective : Function.Injective witnessTriple := by
  intro a b h
  exact Fin.ext (show a.val=b.val from congrArg (fun x : Fin 128 => x.val) h)
theorem witness_auth : childAuth witnessTriple = 6 := by
  unfold childAuth slotSet
  rw [← sortLeaves_eq ((valList_nodup _).mpr witness_injective)]
  decide
theorem accepted_witness : Accepted ((0,fun _ => 0),((fun _ => witnessTriple),(0,0))) := by
  refine ⟨rfl,fun _ => witness_injective,?_⟩
  simp only [witness_auth,sum_const,Fintype.card_fin,Bank,smul_eq_mul]
  norm_num
instance : Nonempty {r : RawRecord // Accepted r} :=
  ⟨⟨_,accepted_witness⟩⟩
instance : Nonempty {p : Payload // PayloadAccepted p} :=
  ⟨⟨_,accepted_witness⟩⟩
end SigGolfResearch.Gate6
end
section
namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
noncomputable def acceptedEquiv : {r : RawRecord // Accepted r} ≃
    MarkedLabel × {p : Payload // PayloadAccepted p} where
  toFun r := (r.1.1,⟨r.1.2,r.2⟩)
  invFun x := ⟨(x.1,x.2.1),x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def markFibreEquiv (mark : MarkedLabel) :
    {r : RawRecord // Accepted r ∧ r.1=mark} ≃ {p : Payload // PayloadAccepted p} where
  toFun r := ⟨r.1.2,r.2.1⟩
  invFun p := ⟨(mark,p.1),p.2,rfl⟩
  left_inv r := by apply Subtype.ext; exact Prod.ext r.2.2.symm rfl
  right_inv _ := rfl
noncomputable def payloadEquiv : {p : Payload // PayloadAccepted p} ≃
    {s : Slots // SlotsAccepted s} × Unused where
  toFun p := (⟨p.1.1,p.2.2⟩,p.1.2.2)
  invFun x := ⟨(x.1.1,(0,x.2)),rfl,x.1.2⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext p.2.1.symm rfl)
  right_inv _ := rfl
theorem accepted_card : Fintype.card {r : RawRecord // Accepted r} =
    2^59 * Fintype.card {p : Payload // PayloadAccepted p} := by
  rw [Fintype.card_congr acceptedEquiv,Fintype.card_prod,markedLabel_card]
theorem fibre_card (mark : MarkedLabel) :
    Fintype.card {r : RawRecord // Accepted r ∧ r.1=mark} =
      Fintype.card {p : Payload // PayloadAccepted p} := Fintype.card_congr (markFibreEquiv mark)
theorem payload_accepted_card : Fintype.card {p : Payload // PayloadAccepted p} =
    Fintype.card {s : Slots // SlotsAccepted s} * 2^47 := by
  rw [Fintype.card_congr payloadEquiv,Fintype.card_prod]
  simp only [Unused,Fintype.card_fin]
theorem fresh_acceptance : Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] =
    (Fintype.card {p : Payload // PayloadAccepted p} : ENNReal) / 2^197 := by
  rw [probEvent_uniformSample,← Fintype.card_subtype,accepted_card,rawRecord_card,Nat.cast_mul]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256=2^59*2^197 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)
theorem fresh_mark_joint (mark : MarkedLabel) :
    Pr[fun r => Accepted r ∧ r.1=mark | ($ᵗ RawRecord : ProbComp RawRecord)] =
      Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] / 2^59 := by
  rw [probEvent_uniformSample,← Fintype.card_subtype,fibre_card,rawRecord_card,fresh_acceptance]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  rw [show (2 : ENNReal)^256=2^197*2^59 by rw [← pow_add],
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),mul_assoc]
theorem fresh_mark_conditional (mark : MarkedLabel) :
    Pr[fun r => Accepted r ∧ r.1=mark | ($ᵗ RawRecord : ProbComp RawRecord)] /
      Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] = (2^59 : ENNReal)⁻¹ := by
  rw [fresh_mark_joint]
  have hp : Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] ≠ 0 := by
    rw [fresh_acceptance]
    exact ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast Fintype.card_ne_zero,by finiteness⟩
  rw [div_eq_mul_inv,div_eq_mul_inv]
  calc
    _ = (Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] *
        (Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)])⁻¹) * (2^59 : ENNReal)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hp probEvent_ne_top,one_mul]
end SigGolfResearch.Gate6
end
end
-- ==== merged from T3_Gate6_ChildCounting ====
section

namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
attribute [local irreducible] Finset.univ
set_option backward.isDefEq.respectTransparency false
abbrev ChildSet := (powersetCard 3 (range 128))
abbrev SetFamily := Bank → ChildSet
def setCost (s : ChildSet) : Nat := octH 7 s.val.sort
def familyCost (s : SetFamily) : Nat := ∑ bank, setCost (s bank)
theorem childSet_card : Fintype.card ChildSet = 341376 := by
  rw [Fintype.card_coe,card_powersetCard,card_range]
  norm_num [Nat.choose]
theorem family_card : Fintype.card SetFamily = 341376^7 := by
  rw [Fintype.card_fun,childSet_card]
  simp only [Bank,Fintype.card_fin]
theorem child_weight_sum (y : Nat) : ∑ s : ChildSet, y^setCost s = (Q y 7).coeff 3 := by
  rw [coeff_Q y 7 3 (by decide),show (2 : Nat)^7=128 by decide]
  simp only [setCost,oc]
  convert (sum_coe_sort (powersetCard 3 (range 128)) (fun s : Finset Nat => y^octH 7 s.sort)) using 1
theorem family_weight_sum (y : Nat) : ∑ s : SetFamily, y^familyCost s = ((Q y 7).coeff 3)^7 := by
  simp only [familyCost,← prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : Bank) (s : ChildSet) => y^setCost s)]
  simp only [child_weight_sum,prod_const,card_univ,Bank,Fintype.card_fin]
theorem mod_pow_sum_generic {α : Type} {y n : Nat} (hn : 0<n)
    (s : Finset α) (g : α → Nat) (hc : s.card<y) :
    (∑ a ∈ s,y^g a)%y^n = ∑ a ∈ s.filter (fun a => g a<n),y^g a := by
  classical
  rw [← sum_filter_add_sum_filter_not s (fun a => g a<n)]
  obtain ⟨c,hdiv⟩ : y^n ∣ ∑ a ∈ s.filter (fun a => ¬g a<n),y^g a :=
    dvd_sum fun a ha => pow_dvd_pow y (not_lt.mp (mem_filter.mp ha).2)
  rw [hdiv,Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hy : 1≤y := by omega
  calc
    _ ≤ ∑ _a ∈ s.filter (fun a => g a<n),y^(n-1) :=
      sum_le_sum fun a ha => Nat.pow_le_pow_right hy (by have := (mem_filter.mp ha).2;omega)
    _ = (s.filter (fun a => g a<n)).card*y^(n-1) := by rw [sum_const,smul_eq_mul]
    _ ≤ s.card*y^(n-1) := Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ < y*y^(n-1) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = y^n := by rw [←pow_succ'];congr 1;omega
theorem sum_pow_mod_pred_generic {α : Type} {y : Nat} (hy : 3≤y)
    (s : Finset α) (g : α → Nat) :
    (∑ a ∈ s,y^g a)%(y-1)=s.card%(y-1) := by
  have hm : y%(y-1)=1 := by
    calc
      _ = (y-1+1)%(y-1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 1%(y-1) := Nat.add_mod_left _ _
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  rw [sum_nat_mod,sum_congr rfl fun a _ => by rw [Nat.pow_mod,hm,one_pow]]
  simp
theorem generic_capped_card {α : Type} [Fintype α] (g : α → Nat) (y cap : Nat)
    (hy : 3≤y) (hc : Fintype.card α<y-1) :
    (Finset.univ.filter (fun a => g a≤cap)).card =
      ((∑ a,y^g a)%y^(cap+1))%(y-1) := by
  classical
  rw [mod_pow_sum_generic (by omega) _ _ (by rw [card_univ];omega),
    sum_pow_mod_pred_generic hy,Nat.mod_eq_of_lt ((card_filter_le _ _).trans_lt (by rw [card_univ];exact hc))]
  exact congrArg card (filter_congr fun a _ => by omega)
def packedSetCount : Nat :=
  (((piter 3 (2^160) ((2^160)^(87+1)) 7 [0,1]).getD 3 0)^7 % (2^160)^(87+1)) % (2^160-1)
theorem packedSetCount_value : packedSetCount = 1792558607887680192091036610744811520 := by
  decide +kernel
end SigGolfResearch.Gate6
end
-- ==== merged from T3_Nonbinary_Counting ====
section

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
/-- Campaign T8D (NF17, legacy): accepted NF17 words at target 146 (no credit floor). -/
def nf17Count : Nat := 68265759603931770586437474120287175
/-- Campaign T51: the exact T51 top decoder count `#{v : decode 0 v ≠ none}` (data digit sums 147..152, PINNED P3;
`SigGolfResearch.T51Top.decoder_card`, `SigGolfCandidate.T3.Nonbinary.actual_decoder_count`). -/
def count : Nat := 59986302681901911802536001662038264
theorem exact_packed_count :
    (packed%radix^147)%(radix-1)-(packed%radix^146)%(radix-1)=nf17Count := by decide +kernel
theorem accepted_card : (Finset.univ.filter fun w : Word => weight w=146).card=nf17Count := by
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
theorem accepted_digest_card : acceptedDigests.card=nf17Count := by
  classical
  unfold acceptedDigests
  rw [Finset.card_image_of_injective _ digest_injective,accepted_card]
theorem probability_fraction : (nf17Count : ℚ)/2^128=
    68265759603931770586437474120287175/340282366920938463463374607431768211456 := by
  norm_num [nf17Count]
end SigGolfResearch.NonbinaryTop.Counting

/-! Campaign T51 (COUNT): exact counting model of the T51 top word.
A word is the 9 r6 ranks (`< 216`, groups `g0..g8`, chains `3g .. 3g+2`), the 7 r5 ranks (`< 125`, #938's groups
`q9..q15`, chains `3q .. 3q+2`) and the r7 pair rank (`< 49`, chains 48 = `rank % 7`, 49 = `rank / 7`). The checksum
chain 50 is derived (`152 - weight`).
Per group: digit sum, zero digits, credit (digits one below the maximum), safe copies, and the dispatch-penalty
complement on the penalised r5 groups `q10, q11, q12`. The generating polynomial in `B = 2^128` with exponent
`stat = 32712 * zeros + 141 * weight + score` (score `≤ 139`, weight `≤ 231`) is computed modulo `B^(32712*8)` (zero
counts `≤ 7`). -/
namespace SigGolfResearch.T51Top
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-- Digit `k` of a group rank in radix `b`. -/
def dg (b r k : Nat) : Nat := r / b ^ k % b
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def tsum (b r : Nat) : Nat := dg b r 0 + dg b r 1 + dg b r 2
def tzeros (b r : Nat) : Nat := ind (dg b r 0 = 0) + ind (dg b r 1 = 0) + ind (dg b r 2 = 0)
def tcredit (b r : Nat) : Nat := ind (dg b r 0 + 1 = b - 1) + ind (dg b r 1 + 1 = b - 1) + ind (dg b r 2 + 1 = b - 1)
def tcopies (b : Nat) (first : Bool) (r : Nat) : Nat :=
  ind (first = true ∧ dg b r 0 = b - 1) + ind (dg b r 1 = b - 1 ∧ dg b r 0 = b - 1) +
    ind (dg b r 2 = b - 1 ∧ dg b r 1 = b - 1)
/-- Score of a triple: credit, 4 per safe copy, and on a penalised group 1 when its digit sum is at least 3. -/
def tscore (b : Nat) (first pen : Bool) (r : Nat) : Nat :=
  tcredit b r + 4 * tcopies b first r + (if pen = true then ind (3 ≤ tsum b r) else 0)
def tstat (b : Nat) (first pen : Bool) (r : Nat) : Nat := 32712 * tzeros b r + 141 * tsum b r + tscore b first pen r

/-! The r7 pair (chain 48 = digit 0, chain 49 = digit 1, radix 7). Chain 48 is never safe (`48 % 3 = 0`), chain 49
is safe iff both digits are 6. -/
def psum (r : Nat) : Nat := dg 7 r 0 + dg 7 r 1
def pzeros (r : Nat) : Nat := ind (dg 7 r 0 = 0) + ind (dg 7 r 1 = 0)
def pcredit (r : Nat) : Nat := ind (dg 7 r 0 + 1 = 6) + ind (dg 7 r 1 + 1 = 6)
def pcopies (r : Nat) : Nat := ind (dg 7 r 1 = 6 ∧ dg 7 r 0 = 6)
def pscore (r : Nat) : Nat := pcredit r + 4 * pcopies r
def pstat (r : Nat) : Nat := 32712 * pzeros r + 141 * psum r + pscore r

/-- The penalised r5 groups: `q10, q11, q12` (index `j = q - 9`). -/
def pen (j : Fin 7) : Bool := decide (j.val = 1 ∨ j.val = 2 ∨ j.val = 3)

abbrev Word := (Fin 9 → Fin 216) × (Fin 7 → Fin 125) × Fin 49

def weight (w : Word) : Nat :=
  (∑ g : Fin 9, tsum 6 (w.1 g).val) + (∑ j : Fin 7, tsum 5 (w.2.1 j).val) + psum w.2.2.val
def zeros (w : Word) : Nat :=
  (∑ g : Fin 9, tzeros 6 (w.1 g).val) + (∑ j : Fin 7, tzeros 5 (w.2.1 j).val) + pzeros w.2.2.val
def score (w : Word) : Nat :=
  (∑ g : Fin 9, tscore 6 (decide (g.val = 0)) false (w.1 g).val) +
    (∑ j : Fin 7, tscore 5 false (pen j) (w.2.1 j).val) + pscore w.2.2.val
def stat (w : Word) : Nat :=
  (∑ g : Fin 9, tstat 6 (decide (g.val = 0)) false (w.1 g).val) +
    (∑ j : Fin 7, tstat 5 false (pen j) (w.2.1 j).val) + pstat w.2.2.val
/-- LOW is not forced (`TopChoice.blocked` fails): the rank of r6 group 8 (bits 120..127) is at least 64. -/
def isFree (w : Word) : Prop := 64 ≤ (w.1 8).val
instance (w : Word) : Decidable (isFree w) := inferInstanceAs (Decidable (64 ≤ (w.1 8).val))

theorem stat_eq (w : Word) : stat w = 32712 * zeros w + 141 * weight w + score w := by
  simp only [stat, tstat, pstat, zeros, weight, score, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem tscore6_le (first : Bool) (r : Fin 216) : tscore 6 first false r.val ≤ if first then 12 else 8 := by
  revert first r; decide +kernel
theorem tscore5_le (p : Bool) (r : Fin 125) : tscore 5 false p r.val ≤ if p = true then 9 else 8 := by
  revert p r; decide +kernel
theorem pscore_le (r : Fin 49) : pscore r.val ≤ 4 := by revert r; decide +kernel
theorem tsum6_le (r : Fin 216) : tsum 6 r.val ≤ 15 := by revert r; decide +kernel
theorem tsum5_le (r : Fin 125) : tsum 5 r.val ≤ 12 := by revert r; decide +kernel
theorem psum_le (r : Fin 49) : psum r.val ≤ 12 := by revert r; decide +kernel

theorem score_le (w : Word) : score w ≤ 139 := by
  have h6 : (∑ g : Fin 9, tscore 6 (decide (g.val = 0)) false (w.1 g).val) ≤
      ∑ g : Fin 9, (if g.val = 0 then 12 else 8) := by
    apply Finset.sum_le_sum; intro g _
    simpa using tscore6_le (decide (g.val = 0)) (w.1 g)
  have h5 : (∑ j : Fin 7, tscore 5 false (pen j) (w.2.1 j).val) ≤ ∑ j : Fin 7, (if pen j = true then 9 else 8) :=
    Finset.sum_le_sum fun j _ => tscore5_le (pen j) (w.2.1 j)
  have hp := pscore_le w.2.2
  have hb : (∑ g : Fin 9, (if g.val = 0 then 12 else 8)) = 76 := by decide +kernel
  have hb5 : (∑ j : Fin 7, (if pen j = true then 9 else 8)) = 59 := by decide +kernel
  simp only [hb, hb5] at h6 h5
  unfold score; omega

theorem weight_le (w : Word) : weight w ≤ 231 := by
  have h6 : (∑ g : Fin 9, tsum 6 (w.1 g).val) ≤ ∑ _g : Fin 9, 15 := Finset.sum_le_sum fun g _ => tsum6_le (w.1 g)
  have h5 : (∑ j : Fin 7, tsum 5 (w.2.1 j).val) ≤ ∑ _j : Fin 7, 12 :=
    Finset.sum_le_sum fun j _ => tsum5_le (w.2.1 j)
  have hp := psum_le w.2.2
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h6 h5
  unfold weight; omega

theorem word_card : Fintype.card Word = 216 ^ 9 * (125 ^ 7 * 49) := by
  simp [Word, Fintype.card_prod, Fintype.card_fun]

/-! ### Digits of a sum of powers -/
theorem sum_pow_lt {α : Type} (s : Finset α) (g : α → Nat) (y k : Nat) (hy : 1 ≤ y) (hc : s.card < y)
    (hg : ∀ a ∈ s, g a < k) : (∑ a ∈ s, y ^ g a) < y ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : s = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => by have := hg a ha; omega
    subst this; simp
  · calc (∑ a ∈ s, y ^ g a) ≤ ∑ _a ∈ s, y ^ (k - 1) :=
          Finset.sum_le_sum fun a ha => Nat.pow_le_pow_right hy (by have := hg a ha; omega)
      _ = s.card * y ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ < y * y ^ (k - 1) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = y ^ k := by rw [← pow_succ']; congr 1; omega

theorem digit_of_sum {α : Type} (s : Finset α) (g : α → Nat) (y k : Nat) (hy : 2 ≤ y) (hc : s.card < y) :
    (∑ a ∈ s, y ^ g a) / y ^ k % y = (s.filter fun a => g a = k).card := by
  classical
  have hk1 : (∑ a ∈ s, y ^ g a) % y ^ (k + 1) = ∑ a ∈ s.filter (fun a => g a < k + 1), y ^ g a :=
    SigGolfResearch.Gate6.mod_pow_sum_generic (by omega) s g hc
  have hsplit : (∑ a ∈ s.filter (fun a => g a < k + 1), y ^ g a) =
      (∑ a ∈ s.filter (fun a => g a < k), y ^ g a) + (s.filter fun a => g a = k).card * y ^ k := by
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun a => g a < k + 1)) (fun a => g a < k),
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · apply Finset.sum_congr (Finset.filter_congr fun a _ => by omega) (fun _ _ => rfl)
    · rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr (Finset.filter_congr fun a _ => by omega)
      intro a ha
      simp only [Finset.mem_filter] at ha
      rw [ha.2]
  have hlt : (∑ a ∈ s.filter (fun a => g a < k), y ^ g a) < y ^ k :=
    sum_pow_lt _ g y k (by omega) ((Finset.card_filter_le _ _).trans_lt hc) fun a ha => (Finset.mem_filter.mp ha).2
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, hk1, hsplit, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem digit_mod_pow (P b n k : Nat) (hk : k < n) : P % b ^ n / b ^ k % b = P / b ^ k % b := by
  have h : b ^ n = b ^ k * b ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self b (by omega : n - k ≠ 0))]

/-! ### Truncated products
Generic in the modulus `m`; instantiated at `m = B ^ e` (the kernel only ever evaluates `Nat.pow` with exponent
`e < 2^24`). -/
def B : Nat := 2 ^ 128
def tmulM (m a b : Nat) : Nat := a * b % m
def tprodM (m : Nat) : List Nat → Nat
  | [] => 1 % m
  | a :: t => tmulM m a (tprodM m t)

theorem tprodM_eq (m : Nat) (L : List Nat) : tprodM m L = L.prod % m := by
  induction L with
  | nil => rfl
  | cons a t ih => rw [tprodM, tmulM, ih, List.prod_cons, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem word_card_lt : Fintype.card Word < B := by rw [word_card, B]; norm_num

/-- A weighted sum over words factors over the 17 groups (generic statistic per group). -/
theorem weighted_generic (f6 : Fin 9 → Fin 216 → Nat) (f5 : Fin 7 → Fin 125 → Nat) (f7 : Fin 49 → Nat) :
    (∑ w : Word, (∏ g : Fin 9, f6 g (w.1 g)) * (∏ j : Fin 7, f5 j (w.2.1 j)) * f7 w.2.2) =
      (∏ g : Fin 9, ∑ r : Fin 216, f6 g r) * (∏ j : Fin 7, ∑ r : Fin 125, f5 j r) * ∑ r : Fin 49, f7 r := by
  rw [Fintype.prod_sum (fun g r => f6 g r), Fintype.prod_sum (fun j r => f5 j r), Fintype.sum_prod_type,
    Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]

/-! ### Generic group statistics
A statistic of a word is a sum of per-group statistics `s6 g r6`, `s5 j r5`, `s7 r7`. With `free`, words whose LOW
half is forced (`¬ isFree`) are dropped (group 8 restricted to ranks `≥ 64`). -/
structure GStat where
  s6 : Fin 9 → Nat → Nat
  s5 : Fin 7 → Nat → Nat
  s7 : Nat → Nat

def GStat.eval (S : GStat) (w : Word) : Nat :=
  (∑ g : Fin 9, S.s6 g (w.1 g).val) + (∑ j : Fin 7, S.s5 j (w.2.1 j).val) + S.s7 w.2.2.val

def F6 (y : Nat) (S : GStat) (free : Bool) (g : Fin 9) : Nat :=
  ∑ r : Fin 216, if free = true ∧ g.val = 8 ∧ r.val < 64 then 0 else y ^ S.s6 g r.val
def F5 (y : Nat) (S : GStat) (j : Fin 7) : Nat := ∑ r : Fin 125, y ^ S.s5 j r.val
def F7 (y : Nat) (S : GStat) : Nat := ∑ r : Fin 49, y ^ S.s7 r.val

def factors (y : Nat) (S : GStat) (free : Bool) : List Nat :=
  List.ofFn (F6 y S free) ++ List.ofFn (F5 y S) ++ [F7 y S]

theorem factors_prod (y : Nat) (S : GStat) (free : Bool) :
    (factors y S free).prod = ∑ w ∈ univ.filter (fun w : Word => free = true → isFree w), y ^ S.eval w := by
  have h := weighted_generic (fun g r => if free = true ∧ g.val = 8 ∧ r.val < 64 then 0 else y ^ S.s6 g r.val)
    (fun j r => y ^ S.s5 j r.val) (fun r => y ^ S.s7 r.val)
  have hl : (factors y S free).prod =
      (∏ g : Fin 9, F6 y S free g) * (∏ j : Fin 7, F5 y S j) * F7 y S := by
    rw [factors, List.prod_append, List.prod_append, List.prod_ofFn, List.prod_ofFn]
    simp
  rw [hl]
  unfold F6 F5 F7
  rw [← h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_pow_eq_pow_sum]
  by_cases hf : free = true ∧ (w.1 8).val < 64
  · rw [if_neg (by unfold isFree; intro h1; have := h1 hf.1; omega)]
    apply mul_eq_zero_of_left
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ 8)
    simp [hf.1, hf.2]
  · rw [if_pos (by unfold isFree; intro h1; have := not_and.mp hf h1; omega)]
    rw [Finset.prod_congr rfl (g := fun g => y ^ S.s6 g (w.1 g).val) (fun g _ => by
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      have hg : g = 8 := Fin.ext h2
      subst hg
      exact hf ⟨h1, h3⟩)]
    rw [Finset.prod_pow_eq_pow_sum, GStat.eval, pow_add, pow_add]

def packedG (n : Nat) (S : GStat) (free : Bool) : Nat := tprodM (B ^ n) (factors B S free)

theorem packedG_digit (n : Nat) (S : GStat) (free : Bool) (k : Nat) (hk : k < n) :
    packedG n S free / B ^ k % B =
      (univ.filter fun w : Word => (free = true → isFree w) ∧ S.eval w = k).card := by
  classical
  rw [packedG, tprodM_eq, digit_mod_pow _ _ _ _ hk, factors_prod,
    digit_of_sum _ _ _ _ (by norm_num [B]) ((Finset.card_filter_le _ _).trans_lt (by simpa using word_card_lt)),
    Finset.filter_filter]

/-! ### The weight polynomial (decoder count) -/
def weightS : GStat := ⟨fun _ r => tsum 6 r, fun _ r => tsum 5 r, psum⟩
theorem weightS_eval (w : Word) : weightS.eval w = weight w := rfl

/-- Weight cut: words of weight below 153 (all data sums of an accepted top word). -/
def wcut : Nat := 153
def packedW : Nat := packedG wcut weightS false
attribute [irreducible] packedW

theorem packedW_digit (k : Nat) (hk : k < wcut) :
    packedW / B ^ k % B = (univ.filter fun w : Word => weight w = k).card := by
  rw [packedW, packedG_digit _ _ _ _ hk]
  simp only [Bool.false_eq_true, false_implies, true_and, weightS_eval]

/-- The T51 top decoder window: data digit sums `147 .. 152` (checksum digit `152 - weight ∈ [0, 5]`). -/
theorem window_card_digits :
    (univ.filter fun w : Word => 147 ≤ weight w ∧ weight w ≤ 152).card =
      ((List.range 6).map fun i => packedW / B ^ (147 + i) % B).sum := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun w : Word => weight w)
    (s := univ.filter fun w : Word => 147 ≤ weight w ∧ weight w ≤ 152) (t := Finset.Icc 147 152) (by
      intro w hw
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hw
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact hw)
  rw [hfib]
  have hl : ((List.range 6).map fun i => packedW / B ^ (147 + i) % B).sum =
      ∑ i ∈ Finset.range 6, packedW / B ^ (147 + i) % B := by
    simp [Finset.sum_range_succ, List.range_succ]
    ring
  rw [hl, show Finset.Icc 147 152 = (Finset.range 6).map (addLeftEmbedding 147) by decide, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [addLeftEmbedding_apply, Finset.filter_filter]
  rw [packedW_digit _ (by have := Finset.mem_range.mp hi; unfold wcut; omega)]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  have := Finset.mem_range.mp hi
  omega

/-- The T51 top decoder count (data sums 147..152). -/
def decoderCount : Nat := 59986302681901911802536001662038264
theorem decoderCount_digits : ((List.range 6).map fun i => packedW / B ^ (147 + i) % B).sum = decoderCount := by
  decide +kernel
theorem decoderCount_eq : decoderCount = SigGolfResearch.NonbinaryTop.Counting.count := rfl

end SigGolfResearch.T51Top
end
