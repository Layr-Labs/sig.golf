import SigGolfCandidate.T3_Nonbinary_Counting
import SigGolfCandidate.SphincsSecurity_Completeness_Uniform
import SigGolfCandidate.T3_Nonbinary_SourceDigits

section
namespace SigGolfResearch.NonbinaryTop.Decoder
open scoped BigOperators
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
def parse : (n : Nat) → Nat → Option ((Fin n → Triple5) × Triple8)
  | 0,x => if h : x<512 then some ((fun i => Fin.elim0 i),digits8 ⟨x,h⟩) else none
  | n+1,x => if h : x%128<125 then
      match parse n (x/128) with
      | none => none
      | some (ds,q) => some (Fin.cons (digits5 ⟨x%128,h⟩) ds,q)
    else none
def encodeN {n : Nat} (d : (Fin n → Triple5) × Triple8) : Nat :=
  pack (List.ofFn fun i => (rank5 (d.1 i)).val) (rank8 d.2).val
theorem encodeN_zero (d : (Fin 0 → Triple5) × Triple8) : encodeN d=(rank8 d.2).val := rfl
theorem encodeN_succ {n : Nat} (d : (Fin (n+1) → Triple5) × Triple8) :
    encodeN d=(rank5 (d.1 0)).val+128*encodeN (Fin.tail d.1,d.2) := by
  simp [encodeN,List.ofFn_succ,pack,Fin.tail]
theorem parse_encodeN {n : Nat} (d : (Fin n → Triple5) × Triple8) :
    parse n (encodeN d)=some d := by
  induction n with
  | zero =>
    rw [encodeN_zero]
    simp only [parse,dif_pos (rank8 d.2).isLt]
    change some ((fun i => Fin.elim0 i),digits8 (rank8 d.2))=some d
    rw [digits8_rank8]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hd := (rank5 (d.1 0)).isLt
    have hd128 : (rank5 (d.1 0)).val<128 := lt_trans hd (by decide)
    rw [encodeN_succ]
    simp only [parse,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd128,
      dif_pos hd,Nat.add_mul_div_left _ _ (by decide : 0<128),
      Nat.div_eq_of_lt hd128,Nat.zero_add,ih]
    change some (Fin.cons (digits5 (rank5 (d.1 0))) (Fin.tail d.1),d.2)=some d
    rw [digits5_rank5,Fin.cons_self_tail]
theorem encodeN_parse {n x : Nat} {d : (Fin n → Triple5) × Triple8}
    (h : parse n x=some d) : encodeN d=x := by
  induction n generalizing x with
  | zero =>
    simp only [parse] at h
    split at h
    · cases h
      simp [encodeN,pack,rank8_digits8]
    · contradiction
  | succ n ih =>
    simp only [parse] at h
    split at h
    · split at h
      · contradiction
      · rename_i ds q he
        cases h
        rw [encodeN_succ]
        simp only [Fin.cons_zero,Fin.tail_cons,rank5_digits5]
        rw [ih he]
        exact Nat.mod_add_div x 128
    · contradiction
def decode (d : Fin (2^128)) : Option Word :=
  (parse 17 d.val).filter fun w => decide (weight w=146)
theorem encodeN_word (w : Word) : encodeN w=encode w := rfl
attribute [local irreducible] encodeN Codec.encode Codec.pack Codec.ranks
theorem decode_some_iff (d : Fin (2^128)) (w : Word) :
    decode d=some w ↔ digest w=d ∧ weight w=146 := by
  constructor
  · intro h
    obtain ⟨hparse,hw⟩ := Option.filter_eq_some_iff.mp h
    have hp := encodeN_parse hparse
    refine ⟨?_,of_decide_eq_true hw⟩
    apply Fin.ext
    exact (encodeN_word w).symm.trans hp
  · rintro ⟨hd,hw⟩
    subst d
    apply Option.filter_eq_some_iff.mpr
    constructor
    · change parse 17 (encode w)=some w
      rw [←encodeN_word]
      exact parse_encodeN w
    · exact decide_eq_true hw
theorem decode_isSome_iff (d : Fin (2^128)) : (decode d).isSome ↔ d∈acceptedDigests := by
  classical
  simp only [Option.isSome_iff_exists,acceptedDigests,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨he,hweight⟩ := (decode_some_iff d w).mp hw
    exact ⟨w,hweight,he⟩
  · rintro ⟨w,hweight,he⟩
    exact ⟨w,(decode_some_iff d w).mpr ⟨he,hweight⟩⟩
theorem decoder_count :
    Fintype.card {d : Fin (2^128) // (decode d).isSome}=nf17Count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => (decode d).isSome)=acceptedDigests := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,decode_isSome_iff]
  rw [he,accepted_digest_card]
open OracleComp OracleSpec ENNReal
theorem decoder_uniform_probability :
    Pr[fun d => (decode d).isSome | ($ᵗ Fin (2^128) : ProbComp (Fin (2^128)))]=
      (nf17Count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,←Fintype.card_subtype,decoder_count]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
def decodeBV (d : BitVec 128) : Option Word := decode d.toFin
def acceptedBVEquiv : {d : BitVec 128 // (decodeBV d).isSome} ≃
    {d : Fin (2^128) // (decode d).isSome} where
  toFun d := ⟨d.val.toFin,d.property⟩
  invFun d := ⟨BitVec.ofFin d.val,d.property⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl
theorem decoder_bv_count :
    Fintype.card {d : BitVec 128 // (decodeBV d).isSome}=nf17Count := by
  classical
  rw [Fintype.card_congr acceptedBVEquiv,decoder_count]
theorem decoder_bv_probability :
    Pr[fun d => (decodeBV d).isSome | ($ᵗ BitVec 128 : ProbComp (BitVec 128))]=
      (nf17Count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,←Fintype.card_subtype,decoder_bv_count]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
@[reducible] def encodingDecode (answer : BitVec 256) : Option Word :=
  decodeBV (answer.extractLsb' 0 128)
theorem encoding_uniform_probability :
    Pr[fun answer => (encodingDecode answer).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      (nf17Count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample]
  have hc := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128)
    (by decide) (fun d => (decodeBV d).isSome)
  change (Finset.univ.filter fun answer : BitVec 256 =>
    (decodeBV (answer.extractLsb' 0 128)).isSome).card = _ at hc
  simp only [encodingDecode]
  rw [hc]
  rw [←Fintype.card_subtype,decoder_bv_count]
  simp only [Fintype.card_bitVec,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256=2^128*2^128 by rw [←pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
end SigGolfResearch.NonbinaryTop.Decoder
#print axioms SigGolfResearch.NonbinaryTop.Decoder.parse_encodeN
#print axioms SigGolfResearch.NonbinaryTop.Decoder.encodeN_parse
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decode_some_iff
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_count
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_uniform_probability
#print axioms SigGolfResearch.NonbinaryTop.Decoder.decoder_bv_count
#print axioms SigGolfResearch.NonbinaryTop.Decoder.encoding_uniform_probability
end
section
namespace SigGolfResearch.NonbinaryTop.Decoder
open Codec Counting
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem parse_succ_isSome (n x : Nat) :
    (parse (n+1) x).isSome ↔ x%128<125 ∧ (parse n (x/128)).isSome := by
  by_cases h : x%128<125
  · cases hp : parse n (x/128) <;> simp [parse,h,hp]
  · simp [parse,h]
theorem parse_isSome_iff (n x : Nat) :
    (parse n x).isSome ↔ x<512*128^n ∧ ∀ j<n,x/128^j%128<125 := by
  induction n generalizing x with
  | zero =>
    by_cases h : x<512 <;> simp [parse,h]
  | succ n ih =>
    rw [parse_succ_isSome,ih]
    have hb : x/128<512*128^n ↔ x<512*128^(n+1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0<128),pow_succ,Nat.mul_assoc]
    constructor
    · rintro ⟨hzero,hbound,hrest⟩
      refine ⟨hb.mp hbound,?_⟩
      intro j hj
      cases j with
      | zero => simpa using hzero
      | succ j =>
        have hh := hrest j (by omega)
        simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh
    · rintro ⟨hbound,hrest⟩
      refine ⟨by simpa using hrest 0 (by omega),hb.mpr hbound,?_⟩
      intro j hj
      have hh := hrest (j+1) (by omega)
      simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hh
theorem parse_fields {n x : Nat} {d : (Fin n → Triple5) × Triple8}
    (h : parse n x=some d) :
    (∀ j : Fin n,(rank5 (d.1 j)).val=x/128^j.val%128) ∧
      (rank8 d.2).val=x/128^n := by
  induction n generalizing x with
  | zero =>
    simp only [parse] at h
    split at h
    · cases h
      constructor
      · intro j; exact Fin.elim0 j
      · simp [rank8_digits8]
    · contradiction
  | succ n ih =>
    simp only [parse] at h
    split at h
    · split at h
      · contradiction
      · rename_i ds q hp
        cases h
        obtain ⟨hr,hq⟩ := ih hp
        constructor
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [rank5_digits5]
          · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hr j
        · simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hq
    · contradiction
end SigGolfResearch.NonbinaryTop.Decoder
end
section
namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def wordDigits (w : Codec.Word) : List Nat :=
  (List.ofFn fun j => List.ofFn fun k => (w.1 j k).val).flatten ++
    List.ofFn fun k => (w.2 k).val
theorem wordDigits_sum (w : Codec.Word) : (wordDigits w).sum=Counting.weight w := by
  simp only [wordDigits,List.sum_append,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rfl
end SigGolfCandidate.T3.Nonbinary
end

section
/-! Campaign T51 (COUNT): the T51 top digests and the counting model `T51Top.Word`.
`encode` packs the 17 ranks into the T51 word (r6 fields `g0..g6` at `8g`, `g0` offset by 40, the r7 rank at 56
flipped, the r5 ranks `q9..q15` at `7q` flipped, `g7` at 112, `g8` at 120); it is a bijection onto the words with
`topRanksValid`. -/
namespace SigGolfResearch.T51Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-! ### Bit-field packing -/
def packF : List (Nat × Nat) → Nat
  | [] => 0
  | p :: t => p.2 + 2 ^ p.1 * packF t
def offF : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | p :: t, k + 1 => p.1 + offF t k
def widthF : List (Nat × Nat) → Nat
  | [] => 0
  | p :: t => p.1 + widthF t

theorem packF_lt : ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.2 < 2 ^ p.1) → packF L < 2 ^ widthF L
  | [], _ => by simp [packF, widthF]
  | p :: t, h => by
    have hp := h p (by simp)
    have ht := packF_lt t (fun q hq => h q (by simp [hq]))
    simp only [packF, widthF, pow_add]
    have : packF t + 1 ≤ 2 ^ widthF t := ht
    nlinarith [Nat.one_le_two_pow (n := p.1)]

theorem packF_field : ∀ (L : List (Nat × Nat)) (k : Nat), (∀ p ∈ L, p.2 < 2 ^ p.1) → (hk : k < L.length) →
    packF L / 2 ^ offF L k % 2 ^ (L[k]'hk).1 = (L[k]'hk).2
  | [], k, _, hk => by simp at hk
  | p :: t, 0, h, _ => by
    have hp := h p (by simp)
    simp only [packF, offF, pow_zero, Nat.div_one, List.getElem_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  | p :: t, k + 1, h, hk => by
    have hp := h p (by simp)
    have ih := packF_field t k (fun q hq => h q (by simp [hq])) (by simpa using hk)
    simp only [packF, offF, List.getElem_cons_succ, pow_add, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hp, Nat.zero_add]
    exact ih

/-- The T51 fields of a model word (before the flip of the 7-bit fields). -/
def fields (w : Word) : List (Nat × Nat) :=
  [(8, (w.1 0).val + 40), (8, (w.1 1).val), (8, (w.1 2).val), (8, (w.1 3).val), (8, (w.1 4).val),
    (8, (w.1 5).val), (8, (w.1 6).val), (7, w.2.2.val),
    (7, (w.2.1 0).val), (7, (w.2.1 1).val), (7, (w.2.1 2).val), (7, (w.2.1 3).val), (7, (w.2.1 4).val),
    (7, (w.2.1 5).val), (7, (w.2.1 6).val),
    (8, (w.1 7).val), (8, (w.1 8).val)]

theorem fields_bound (w : Word) : ∀ p ∈ fields w, p.2 < 2 ^ p.1 := by
  simp only [fields, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨by have := (w.1 0).isLt; norm_num; omega,
    by have := (w.1 1).isLt; norm_num; omega,
    by have := (w.1 2).isLt; norm_num; omega,
    by have := (w.1 3).isLt; norm_num; omega,
    by have := (w.1 4).isLt; norm_num; omega,
    by have := (w.1 5).isLt; norm_num; omega,
    by have := (w.1 6).isLt; norm_num; omega,
    by have := w.2.2.isLt; norm_num; omega,
    by have := (w.2.1 0).isLt; norm_num; omega,
    by have := (w.2.1 1).isLt; norm_num; omega,
    by have := (w.2.1 2).isLt; norm_num; omega,
    by have := (w.2.1 3).isLt; norm_num; omega,
    by have := (w.2.1 4).isLt; norm_num; omega,
    by have := (w.2.1 5).isLt; norm_num; omega,
    by have := (w.2.1 6).isLt; norm_num; omega,
    by have := (w.1 7).isLt; norm_num; omega,
    by have := (w.1 8).isLt; norm_num; omega⟩

def code (w : Word) : Nat := packF (fields w)
theorem code_lt (w : Word) : code w < 2 ^ 128 := by
  have h := packF_lt _ (fields_bound w)
  have hw : widthF (fields w) = 128 := rfl
  rw [hw] at h
  exact h

/-- The digest of a model word. -/
def encode (w : Word) : Digest := topFlip (BitVec.ofNat 128 (code w))

theorem topCode_encode (w : Word) : topCode (encode w) = code w := by
  rw [encode, topCode_topFlip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (code_lt w)]

theorem code_field (w : Word) (k : Nat) (hk : k < 17) :
    code w / 2 ^ offF (fields w) k % 2 ^ ((fields w)[k]'(by simpa [fields] using hk)).1 =
      ((fields w)[k]'(by simpa [fields] using hk)).2 :=
  packF_field _ k (fields_bound w) _

theorem r6Raw_encode (w : Word) (g : Fin 9) :
    r6Raw (encode w) g.val = if g.val = 0 then (w.1 g).val + 40 else (w.1 g).val := by
  unfold r6Raw r6Shift
  rw [topCode_encode]
  fin_cases g
  · exact code_field w 0 (by decide)
  · exact code_field w 1 (by decide)
  · exact code_field w 2 (by decide)
  · exact code_field w 3 (by decide)
  · exact code_field w 4 (by decide)
  · exact code_field w 5 (by decide)
  · exact code_field w 6 (by decide)
  · exact code_field w 15 (by decide)
  · exact code_field w 16 (by decide)

theorem r6Rank_encode (w : Word) (g : Fin 9) : r6Rank (encode w) g.val = (w.1 g).val := by
  by_cases h : g = 0
  · subst h
    have := r6Raw_encode w 0
    rw [Fin.val_zero, if_pos rfl] at this
    unfold r6Rank
    rw [Fin.val_zero, if_pos rfl, this, Nat.add_sub_cancel]
  · have hg : g.val ≠ 0 := fun e => h (Fin.ext e)
    have := r6Raw_encode w g
    rw [if_neg hg] at this
    unfold r6Rank
    rw [if_neg hg, this]

theorem r6Valid_encode (w : Word) (g : Fin 9) : r6Valid (encode w) g.val = true := by
  by_cases h : g = 0
  · subst h
    have := r6Raw_encode w 0
    rw [Fin.val_zero, if_pos rfl] at this
    unfold r6Valid
    rw [Fin.val_zero, if_pos rfl, this]
    simp
  · have hg : g.val ≠ 0 := fun e => h (Fin.ext e)
    have := r6Raw_encode w g
    rw [if_neg hg] at this
    unfold r6Valid
    rw [if_neg hg, this]
    simpa using (w.1 g).isLt

theorem r5Rank_encode (w : Word) (j : Fin 7) : r5Rank (encode w) (9 + j.val) = (w.2.1 j).val := by
  unfold r5Rank
  rw [topCode_encode]
  fin_cases j
  · exact code_field w 8 (by decide)
  · exact code_field w 9 (by decide)
  · exact code_field w 10 (by decide)
  · exact code_field w 11 (by decide)
  · exact code_field w 12 (by decide)
  · exact code_field w 13 (by decide)
  · exact code_field w 14 (by decide)

theorem r7Rank_encode (w : Word) : r7Rank (encode w) = w.2.2.val := by
  unfold r7Rank
  rw [topCode_encode]
  exact code_field w 7 (by decide)

theorem topRanksValid_encode (w : Word) : topRanksValid (encode w) = true := by
  unfold topRanksValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1]
  refine ⟨⟨fun g hg => r6Valid_encode w ⟨g, hg⟩, fun q hq => ?_⟩, ?_⟩
  · have h := r5Rank_encode w ⟨q - 9, by omega⟩
    simp only [show 9 + (q - 9) = q by omega] at h
    rw [h]; exact (w.2.1 _).isLt
  · rw [r7Rank_encode]; exact w.2.2.isLt

/-- The model word of a digest: its 17 ranks (reduced, so that `wordOf` is total). -/
def wordOf (v : Digest) : Word :=
  (fun g => ⟨r6Rank v g.val % 216, Nat.mod_lt _ (by decide)⟩,
    fun j => ⟨r5Rank v (9 + j.val) % 125, Nat.mod_lt _ (by decide)⟩, ⟨r7Rank v % 49, Nat.mod_lt _ (by decide)⟩)

theorem wordOf_encode (w : Word) : wordOf (encode w) = w := by
  refine Prod.ext (funext fun g => Fin.ext ?_) (Prod.ext (funext fun j => Fin.ext ?_) (Fin.ext ?_))
  · simp only [wordOf, r6Rank_encode]; exact Nat.mod_eq_of_lt (w.1 g).isLt
  · simp only [wordOf, r5Rank_encode]; exact Nat.mod_eq_of_lt (w.2.1 j).isLt
  · simp only [wordOf, r7Rank_encode]; exact Nat.mod_eq_of_lt w.2.2.isLt

theorem dataDigits_encode_wordOf (v : Digest) (hv : topRanksValid v = true) :
    dataDigits 0 (encode (wordOf v)) = dataDigits 0 v := by
  obtain ⟨h6, h5, h7⟩ := topRanksValid_parts hv
  unfold dataDigits
  apply List.map_congr_left
  intro i hi
  have hi : i < 50 := by simpa [dataCount] using hi
  unfold coreDigit
  simp only [if_true]
  split_ifs with h27 h48
  · have hg : i / 3 < 9 := by omega
    have := r6Rank_encode (wordOf v) ⟨i / 3, hg⟩
    simp only at this
    rw [this]
    show r6Rank v (i / 3) % 216 / 6 ^ (i % 3) % 6 = _
    rw [Nat.mod_eq_of_lt (r6Rank_lt (h6 _ hg))]
  · have hq : i / 3 - 9 < 7 := by omega
    have := r5Rank_encode (wordOf v) ⟨i / 3 - 9, hq⟩
    simp only [show 9 + (i / 3 - 9) = i / 3 by omega] at this
    rw [this]
    show r5Rank v (9 + (i / 3 - 9)) % 125 / 5 ^ (i % 3) % 5 = _
    rw [show 9 + (i / 3 - 9) = i / 3 by omega, Nat.mod_eq_of_lt (h5 _ (by omega) (by omega))]
  · rw [r7Rank_encode]
    show r7Rank v % 49 / 7 ^ (i - 48) % 7 = _
    rw [Nat.mod_eq_of_lt h7]

theorem encode_wordOf (v : Digest) (hv : topRanksValid v = true) : encode (wordOf v) = v :=
  top_digest_injective (dataDigits_encode_wordOf v hv) (topRanksValid_encode _) hv

theorem card_bij_generic {α β : Type} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P]
    (Q : β → Prop) [DecidablePred Q] (e : β → α) (d : α → β) (h1 : ∀ b, Q b → P (e b))
    (h2 : ∀ a, P a → Q (d a)) (h3 : ∀ b, Q b → d (e b) = b) (h4 : ∀ a, P a → e (d a) = a) :
    (univ.filter P).card = (univ.filter Q).card := by
  symm
  apply Finset.card_bij' (fun b _ => e b) (fun a _ => d a)
  · intro b hb; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 b (Finset.mem_filter.mp hb).2⟩
  · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 a (Finset.mem_filter.mp ha).2⟩
  · intro b hb; exact h3 b (Finset.mem_filter.mp hb).2
  · intro a ha; exact h4 a (Finset.mem_filter.mp ha).2

/-- Counting valid digests is counting model words. -/
theorem card_encode (P : Digest → Prop) [DecidablePred P] (hP : ∀ v, P v → topRanksValid v = true) :
    (univ.filter P).card = (univ.filter fun w : Word => P (encode w)).card :=
  card_bij_generic P (fun w => P (encode w)) encode wordOf (fun _ h => h)
    (fun v h => by show P (encode (wordOf v)); rw [encode_wordOf v (hP v h)]; exact h)
    (fun w _ => wordOf_encode w) (fun v h => encode_wordOf v (hP v h))

/-! ### Digit statistics of `encode w` -/
theorem core_encode6 (w : Word) (g : Fin 9) (k : Nat) (hk : k < 3) :
    coreDigit 0 (encode w) (3 * g.val + k) = dg 6 (w.1 g).val k := by
  rw [top_core_r6 _ _ _ g.isLt hk, r6Rank_encode]; rfl

theorem core_encode5 (w : Word) (j : Fin 7) (k : Nat) (hk : k < 3) :
    coreDigit 0 (encode w) (3 * (9 + j.val) + k) = dg 5 (w.2.1 j).val k := by
  rw [top_core_r5 _ _ _ (by omega) (by omega) hk, r5Rank_encode]; rfl

theorem core_encode7 (w : Word) (k : Nat) (hk : k < 2) :
    coreDigit 0 (encode w) (48 + k) = dg 7 w.2.2.val k := by
  rw [top_core_r7 _ _ hk, r7Rank_encode]; rfl

theorem list_sum_range_map (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_blocks (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ range (3 * n), f i = ∑ g ∈ range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

/-- A chain sum over the 50 data chains splits into the 9 r6 triples, the 7 r5 triples and the r7 pair. -/
theorem sum_50 (f : Nat → Nat) :
    ∑ i ∈ range 50, f i = (∑ g : Fin 9, (f (3 * g.val) + f (3 * g.val + 1) + f (3 * g.val + 2))) +
      (∑ j : Fin 7, (f (3 * (9 + j.val)) + f (3 * (9 + j.val) + 1) + f (3 * (9 + j.val) + 2))) +
        (f 48 + f 49) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, show 48 = 3 * 16 by rfl, sum_blocks,
    show 16 = 9 + 7 by rfl, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  ring

theorem sum_encode (w : Word) : (dataDigits 0 (encode w)).sum = weight w := by
  unfold dataDigits
  rw [show dataCount 0 = 50 from rfl, list_sum_range_map, sum_50]
  unfold weight psum
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl; intro g _
      rw [show 3 * g.val = 3 * g.val + 0 by rfl, core_encode6 w g 0 (by decide), core_encode6 w g 1 (by decide),
        core_encode6 w g 2 (by decide)]; rfl
    · apply Finset.sum_congr rfl; intro j _
      rw [show 3 * (9 + j.val) = 3 * (9 + j.val) + 0 by rfl, core_encode5 w j 0 (by decide),
        core_encode5 w j 1 (by decide), core_encode5 w j 2 (by decide)]; rfl
  · have e0 := core_encode7 w 0 (by decide)
    have e1 := core_encode7 w 1 (by decide)
    simp only [Nat.add_zero, Nat.reduceAdd] at e0 e1
    rw [e0, e1]

/-- Campaign T51: the top decoder through the model word. -/
theorem decode_top_encode (w : Word) :
    decode 0 (encode w) = if 147 ≤ weight w ∧ weight w ≤ 152 then
      some (dataDigits 0 (encode w) ++ [152 - weight w]) else none := by
  have hv := topRanksValid_encode w
  have hb : ¬ (BitVec.toNat (encode w) ≥ 2 ^ encodedBits 0) := not_le.mpr (encode w).isLt
  unfold decode
  rw [if_neg hb]
  simp only [if_true, sum_encode, hv, true_and, show target 0 = 152 from rfl]
  by_cases h : 147 ≤ weight w ∧ weight w ≤ 152
  · rw [if_pos ⟨h.2, by omega⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem decode_top_valid {v : Digest} (h : (decode 0 v).isSome = true) : topRanksValid v = true := by
  unfold decode at h
  split_ifs at h with h1 h2 <;> simp_all

/-- The exact T51 top decoder count (PINNED P3). -/
theorem decoder_card :
    (univ.filter fun v : Digest => (decode 0 v).isSome = true).card = decoderCount := by
  rw [card_encode _ (fun v h => decode_top_valid h), ← decoderCount_digits, ← window_card_digits]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [decode_top_encode]
  split_ifs with h <;> simp [h]

end SigGolfResearch.T51Top
end

section
namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-- Campaign T51: the exact top decoder count (the #938 NF17 bridge restated for the T51 word, PINNED P3). -/
theorem actual_decoder_count :
    Fintype.card {v : Digest // (T3.decode 0 v).isSome}=Counting.count := by
  rw [Fintype.card_subtype]
  exact SigGolfResearch.T51Top.decoder_card
open OracleComp OracleSpec ENNReal
theorem actual_decoder_probability :
    Pr[fun v => (T3.decode 0 v).isSome | ($ᵗ Digest : ProbComp Digest)]=
      (Counting.count : ENNReal)/(2 : ENNReal)^128 := by
  have hc := actual_decoder_count
  rw [Fintype.card_subtype] at hc
  rw [probEvent_uniformSample,hc]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
/-- The encoding answers whose low half decodes (term-mode composition: no defeq search through the decoder). -/
theorem actual_encoding_card :
    (Finset.univ.filter fun x : BitVec 256 => (T3.decode 0 (x.extractLsb' 0 128)).isSome = true).card =
      Counting.count * 2 ^ (256 - 128) :=
  (SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide)
    (fun d : Digest => (T3.decode 0 d).isSome = true)).trans
    (congrArg (fun n => n * 2 ^ (256 - 128)) SigGolfResearch.T51Top.decoder_card)
theorem actual_encoding_probability :
    Pr[fun answer : BitVec 256 => (T3.decode 0 (answer.extractLsb' 0 128)).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      (Counting.count : ENNReal)/(2 : ENNReal)^128 := by
  rw [probEvent_uniformSample, actual_encoding_card]
  simp only [Fintype.card_bitVec,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256=2^128*2^128 by rw [←pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfResearch.T51Top.decoder_card
#print axioms SigGolfCandidate.T3.Nonbinary.actual_decoder_count
#print axioms SigGolfCandidate.T3.Nonbinary.actual_encoding_probability
end
