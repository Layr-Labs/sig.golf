import SigGolfCandidate.T3.Nonbinary.Counting
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.T3.Nonbinary.SourceDigits

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
    Fintype.card {d : Fin (2^128) // (decode d).isSome}=count := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun d : Fin (2^128) => (decode d).isSome)=acceptedDigests := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,decode_isSome_iff]
  rw [he,accepted_digest_card]
open OracleComp OracleSpec ENNReal
theorem decoder_uniform_probability :
    Pr[fun d => (decode d).isSome | ($ᵗ Fin (2^128) : ProbComp (Fin (2^128)))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
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
    Fintype.card {d : BitVec 128 // (decodeBV d).isSome}=count := by
  classical
  rw [Fintype.card_congr acceptedBVEquiv,decoder_count]
theorem decoder_bv_probability :
    Pr[fun d => (decodeBV d).isSome | ($ᵗ BitVec 128 : ProbComp (BitVec 128))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_uniformSample,←Fintype.card_subtype,decoder_bv_count]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
@[reducible] def encodingDecode (answer : BitVec 256) : Option Word :=
  decodeBV (answer.extractLsb' 0 128)
theorem encoding_uniform_probability :
    Pr[fun answer => (encodingDecode answer).isSome |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=
      (count : ENNReal)/(2 : ENNReal)^128 := by
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
/-! ### Campaign R6: the top word (design D1c) as an R6 word (`SigGolfResearch.NonbinaryTop.R6.Word`)
`r6Word` reads the 8 r6 and 9 r5 ranks of a top word, `r6Encode` packs an R6 word (r6 group 0 offset by 40, r5 ranks
through `topFlip`, spare bit 0); on valid words they are inverse (`validEquiv`). `decode_top_r6` is the broad top
decoder through the R6 word, `r6_decoder_count` its exact count, `card_valid_transport` moves counts of predicates of
the R6 word to top digests, `blocked_iff_r6` reads `TopChoice.blocked`. The NF17 `Decoder` above (`Decoder.parse 17`)
does not describe the R6 top word. -/
open SigGolfResearch.NonbinaryTop.Codec
set_option linter.constructorNameAsVariable false
set_option linter.unnecessarySeqFocus false
def r6RawOf (w : R6.Word) (g : Fin 8) : Nat := (rank6 (w.1 g)).val + (if g.val = 0 then 40 else 0)
def r6Fields (w : R6.Word) : List (Nat × Nat) :=
  [(8, r6RawOf w 0), (8, r6RawOf w 1), (8, r6RawOf w 2), (8, r6RawOf w 3), (8, r6RawOf w 4), (8, r6RawOf w 5),
   (8, r6RawOf w 6), (7, (rank5 (w.2 0)).val), (7, (rank5 (w.2 1)).val), (7, (rank5 (w.2 2)).val),
   (7, (rank5 (w.2 3)).val), (7, (rank5 (w.2 4)).val), (7, (rank5 (w.2 5)).val), (7, (rank5 (w.2 6)).val),
   (7, (rank5 (w.2 7)).val), (7, (rank5 (w.2 8)).val), (8, r6RawOf w 7)]
def r6Code (w : R6.Word) : Nat := packF (r6Fields w)
def r6Encode (w : R6.Word) : Digest := topFlip (BitVec.ofNat 128 (r6Code w))
def r6Word (v : Digest) : R6.Word :=
  (fun g => digits6 ⟨r6Rank v g.val % 216, Nat.mod_lt _ (by decide)⟩,
   fun j => digits5 ⟨r5Rank v (j.val + 8) % 125, Nat.mod_lt _ (by decide)⟩)

theorem r6RawOf_lt (w : R6.Word) (g : Fin 8) : r6RawOf w g < 2 ^ 8 := by
  have := (rank6 (w.1 g)).isLt
  unfold r6RawOf; split_ifs <;> norm_num <;> omega
theorem r6Fields_bound (w : R6.Word) : ∀ p ∈ r6Fields w, p.2 < 2 ^ p.1 := by
  have h5 (j : Fin 9) : (rank5 (w.2 j)).val < 2 ^ 7 := lt_trans (rank5 (w.2 j)).isLt (by decide)
  intro p hp
  simp only [r6Fields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> first | exact r6RawOf_lt w _ | exact h5 _
theorem r6Code_lt (w : R6.Word) : r6Code w < 2 ^ 127 := by
  have h := packF_lt (r6Fields w) (r6Fields_bound w)
  unfold r6Code
  simpa [r6Fields, widthF] using h
theorem topCode_r6Encode (w : R6.Word) : topCode (r6Encode w) = r6Code w := by
  unfold r6Encode
  rw [topCode_topFlip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (r6Code_lt w) (by decide))]
theorem r6Code_field (w : R6.Word) (k : Nat) (hk : k < 17) :
    r6Code w / 2 ^ widthF ((r6Fields w).take k) % 2 ^ ((r6Fields w)[k]'(by simp [r6Fields]; omega)).1 =
      ((r6Fields w)[k]'(by simp [r6Fields]; omega)).2 :=
  packF_field _ (r6Fields_bound w) k (by simp [r6Fields]; omega)
theorem r6Raw_r6Encode (w : R6.Word) (g : Fin 8) : r6Raw (r6Encode w) g.val = r6RawOf w g := by
  unfold r6Raw
  rw [topCode_r6Encode]
  fin_cases g
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 0 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 1 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 2 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 3 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 4 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 5 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 6 (by decide)
  · simpa [r6Fields, widthF, r6Shift] using r6Code_field w 16 (by decide)
theorem r5Rank_r6Encode (w : R6.Word) (j : Fin 9) : r5Rank (r6Encode w) (j.val + 8) = (rank5 (w.2 j)).val := by
  unfold r5Rank
  rw [topCode_r6Encode]
  fin_cases j
  · simpa [r6Fields, widthF] using r6Code_field w 7 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 8 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 9 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 10 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 11 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 12 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 13 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 14 (by decide)
  · simpa [r6Fields, widthF] using r6Code_field w 15 (by decide)
theorem topSpare_r6Encode (w : R6.Word) : topSpare (r6Encode w) = 0 := by
  unfold topSpare
  rw [topCode_r6Encode, Nat.div_eq_of_lt (r6Code_lt w)]
theorem r6Rank_r6Encode (w : R6.Word) (g : Fin 8) : r6Rank (r6Encode w) g.val = (rank6 (w.1 g)).val := by
  have h := r6Raw_r6Encode w g
  unfold r6RawOf at h
  unfold r6Rank
  by_cases hg : g.val = 0
  · rw [if_pos hg]; rw [if_pos hg, hg] at h; omega
  · rw [if_neg hg]; rw [if_neg hg] at h; omega
theorem r6Valid_r6Encode (w : R6.Word) (g : Fin 8) : r6Valid (r6Encode w) g.val = true := by
  have h := r6Raw_r6Encode w g
  have hr := (rank6 (w.1 g)).isLt
  unfold r6RawOf at h
  unfold r6Valid
  by_cases hg : g.val = 0
  · rw [if_pos hg]; rw [if_pos hg, hg] at h; simp only [decide_eq_true_eq]; omega
  · rw [if_neg hg]; rw [if_neg hg] at h; simp only [decide_eq_true_eq]; omega
theorem topRanksValid_r6Encode (w : R6.Word) : topRanksValid (r6Encode w) = true := by
  unfold topRanksValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1]
  refine ⟨⟨topSpare_r6Encode w, fun g hg => r6Valid_r6Encode w ⟨g, hg⟩⟩, fun q hq => ?_⟩
  have h := r5Rank_r6Encode w ⟨q - 8, by omega⟩
  rw [show q - 8 + 8 = q by omega] at h
  rw [h]; exact (rank5 _).isLt
theorem r6Word_r6Encode (w : R6.Word) : r6Word (r6Encode w) = w := by
  unfold r6Word
  refine Prod.ext (funext fun g => ?_) (funext fun j => ?_)
  · have hx : (⟨r6Rank (r6Encode w) g.val % 216, Nat.mod_lt _ (by decide)⟩ : Fin 216) = rank6 (w.1 g) := by
      apply Fin.ext
      show r6Rank (r6Encode w) g.val % 216 = (rank6 (w.1 g)).val
      rw [r6Rank_r6Encode, Nat.mod_eq_of_lt (rank6 _).isLt]
    simp only
    rw [hx, digits6_rank6]
  · have hx : (⟨r5Rank (r6Encode w) (j.val + 8) % 125, Nat.mod_lt _ (by decide)⟩ : Fin 125) = rank5 (w.2 j) := by
      apply Fin.ext
      show r5Rank (r6Encode w) (j.val + 8) % 125 = (rank5 (w.2 j)).val
      rw [r5Rank_r6Encode, Nat.mod_eq_of_lt (rank5 _).isLt]
    simp only
    rw [hx, digits5_rank5]
/-- The 51 data digits of an R6 word, in chain order (r6 triples, then r5 triples). -/
def r6Digits (w : R6.Word) : List Nat :=
  (List.ofFn fun g : Fin 8 => List.ofFn fun k : Fin 3 => (w.1 g k).val).flatten ++
    (List.ofFn fun j : Fin 9 => List.ofFn fun k : Fin 3 => (w.2 j k).val).flatten
/-- Data digit `i` of an R6 word. -/
def r6Digit (w : R6.Word) (i : Nat) : Nat :=
  if h : i < 24 then (w.1 ⟨i / 3, by omega⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val
  else if h' : i < 51 then (w.2 ⟨i / 3 - 8, by omega⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val else 0
theorem r6Digits_length (w : R6.Word) : (r6Digits w).length = 51 := by
  simp [r6Digits]
theorem r6Digits_sum (w : R6.Word) : (r6Digits w).sum = R6.weight w := by
  simp only [r6Digits, List.sum_append, List.sum_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rfl
theorem r6Digits_getD (w : R6.Word) (i : Nat) (hi : i < 51) : (r6Digits w).getD i 0 = r6Digit w i := by
  interval_cases i <;> rfl
theorem coreDigit_r6 {v : Digest} (h : topRanksValid v = true) (i : Nat) (hi : i < 51) :
    coreDigit 0 v i = r6Digit (r6Word v) i := by
  obtain ⟨-, h6, h5⟩ := topRanksValid_parts h
  have hk : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  unfold coreDigit r6Digit r6Word
  by_cases h24 : i < 24
  · have hr := r6Rank_lt (h6 (i/3) (by omega))
    simp only [if_true, if_pos h24, dif_pos h24]
    rcases hk with hk|hk|hk <;> simp [digits6, hk, Nat.mod_eq_of_lt hr] <;> omega
  · have hr := h5 (i/3) (by omega) (by omega)
    have hq : i / 3 - 8 + 8 = i / 3 := by omega
    simp only [if_true, if_neg h24, dif_neg h24, if_pos hi, dif_pos hi, hq]
    rcases hk with hk|hk|hk <;> simp [digits5, hk, Nat.mod_eq_of_lt hr] <;> omega
theorem dataDigits_r6 {v : Digest} (h : topRanksValid v = true) : dataDigits 0 v = r6Digits (r6Word v) := by
  have hl : (dataDigits 0 v).length = 51 := by simp [dataDigits, dataCount]
  apply List.ext_getElem (by rw [hl, r6Digits_length])
  intro i h1 h2
  have hi : i < 51 := by rwa [hl] at h1
  rw [← List.getD_eq_getElem (d := 0), ← List.getD_eq_getElem (d := 0), r6Digits_getD _ _ hi]
  simp only [dataDigits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i < dataCount 0 from hi),
    Option.map_some, Option.getD_some]
  exact coreDigit_r6 h i hi
theorem r6Encode_r6Word {v : Digest} (h : topRanksValid v = true) : r6Encode (r6Word v) = v := by
  apply top_digest_injective _ (topRanksValid_r6Encode _) h
  rw [dataDigits_r6 (topRanksValid_r6Encode _), r6Word_r6Encode, dataDigits_r6 h]
/-- The decoded top digits of an R6 word: 51 data digits and the checksum digit `target 0 - weight`. -/
def r6Full (w : R6.Word) : List Nat := r6Digits w ++ [target 0 - R6.weight w]
/-- The checksum window: the checksum digit `target 0 - weight` lies in `[0, 7]`. -/
def r6Window (w : R6.Word) : Prop := R6.weight w ≤ target 0 ∧ target 0 - R6.weight w < 8
instance (w : R6.Word) : Decidable (r6Window w) := by unfold r6Window; infer_instance
theorem r6Full_length (w : R6.Word) : (r6Full w).length = 52 := by
  simp [r6Full, r6Digits_length]
/-- Digit `i` of the decoded top word of an R6 word: data digits, then the checksum `target 0 - weight` at 51. -/
theorem r6Full_getD (w : R6.Word) (i : Nat) :
    (r6Full w).getD i 0 = if i < 51 then r6Digit w i else if i = 51 then target 0 - R6.weight w else 0 := by
  unfold r6Full
  by_cases hi : i < 51
  · rw [if_pos hi, List.getD_append _ _ _ _ (by rw [r6Digits_length]; exact hi), r6Digits_getD _ _ hi]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by rw [r6Digits_length]; omega), r6Digits_length]
    by_cases h51 : i = 51
    · subst h51; simp
    · rw [if_neg h51, List.getD_eq_default _ _ (by simp; omega)]
theorem r6Full_sum {w : R6.Word} (h : r6Window w) : (r6Full w).sum = target 0 := by
  unfold r6Full r6Window at *
  rw [List.sum_append, r6Digits_sum]; simp; omega
/-- Data digit `3 g + k` (`g < 8`) is digit `k` of r6 triple `g`. -/
theorem r6Digit_r6 (w : R6.Word) (g : Fin 8) (k : Fin 3) : r6Digit w (3 * g.val + k.val) = (w.1 g k).val := by
  have h : 3 * g.val + k.val < 24 := by omega
  have e1 : (3 * g.val + k.val) / 3 = g.val := by omega
  have e2 : (3 * g.val + k.val) % 3 = k.val := by omega
  unfold r6Digit
  rw [dif_pos h]
  simp only [e1, e2]
/-- Data digit `24 + 3 q + k` (`q < 9`) is digit `k` of r5 triple `q` (group `q + 8`). -/
theorem r6Digit_r5 (w : R6.Word) (q : Fin 9) (k : Fin 3) :
    r6Digit w (24 + 3 * q.val + k.val) = (w.2 q k).val := by
  have h : ¬ (24 + 3 * q.val + k.val < 24) := by omega
  have h' : 24 + 3 * q.val + k.val < 51 := by omega
  have e1 : (24 + 3 * q.val + k.val) / 3 - 8 = q.val := by omega
  have e2 : (24 + 3 * q.val + k.val) % 3 = k.val := by omega
  unfold r6Digit
  rw [dif_neg h, dif_pos h']
  simp only [e1, e2]
/-- A list sum over `List.range n` as a `Finset.range` sum. -/
theorem list_sum_range_map (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
/-- Regrouping a range sum into triples (chain `3 g + k` is digit `k` of triple `g`). -/
theorem sum_range_triples (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ Finset.range (3 * n), f i = ∑ g ∈ Finset.range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
/-- Campaign R6: the top broad decoder through the R6 word. -/
theorem decode_top_r6 (v : Digest) :
    decode 0 v = if topRanksValid v = true ∧ r6Window (r6Word v) then some (r6Full (r6Word v)) else none := by
  by_cases h : topRanksValid v = true
  · have hd := dataDigits_r6 h
    have hb : ¬ (BitVec.toNat v ≥ 2 ^ encodedBits 0) := not_le.mpr v.isLt
    unfold decode
    simp only [if_true, hd, r6Digits_sum, h, true_and, r6Window, r6Full, hb, if_false]
  · unfold decode
    simp [h]
theorem decode_top_isSome_r6 (v : Digest) :
    (decode 0 v).isSome = true ↔ topRanksValid v = true ∧ r6Window (r6Word v) := by
  rw [decode_top_r6]
  split_ifs with h <;> simp [h]
/-- Valid top words and R6 words are in bijection (`r6Word` / `r6Encode`). -/
def validEquiv : {v : Digest // topRanksValid v = true} ≃ R6.Word where
  toFun v := r6Word v.1
  invFun w := ⟨r6Encode w, topRanksValid_r6Encode w⟩
  left_inv v := Subtype.ext (r6Encode_r6Word v.2)
  right_inv w := r6Word_r6Encode w
/-- Counting transport: a predicate of the R6 word, on valid top words. -/
theorem card_valid_transport (Q : R6.Word → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun v : Digest => topRanksValid v = true ∧ Q (r6Word v)).card =
      (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun v _ => r6Word v) (fun w _ => r6Encode w) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨topRanksValid_r6Encode w, by rw [r6Word_r6Encode]; exact hw⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact r6Encode_r6Word hv.1
  · intro w _
    exact r6Word_r6Encode w
theorem r6_decoder_count :
    Fintype.card {v : Digest // (decode 0 v).isSome} = R6.count := by
  classical
  rw [Fintype.card_subtype]
  simp_rw [decode_top_isSome_r6]
  rw [card_valid_transport (fun w => r6Window w)]
  exact R6.window_card
/-- On a valid top word, `TopChoice.blocked` (`v < 2^126`) is "rank of r6 group 7 below 128". -/
theorem blocked_iff_r6 {v : Digest} (h : topRanksValid v = true) :
    TopChoice.blocked v ↔ (rank6 ((r6Word v).1 7)).val < 128 := by
  obtain ⟨hs, h6, -⟩ := topRanksValid_parts h
  have hr := r6Rank_lt (h6 7 (by decide))
  have hc : topCode v < 2 ^ 128 := by rw [topCode]; exact (topFlip v).isLt
  have hd := topCode_div_high v 126 (by decide)
  unfold topSpare at hs
  have hrank : (rank6 ((r6Word v).1 7)).val = r6Rank v 7 := by
    show (rank6 (digits6 ⟨r6Rank v 7 % 216, _⟩)).val = _
    rw [rank6_digits6]; exact Nat.mod_eq_of_lt hr
  rw [hrank]
  unfold r6Rank r6Raw r6Shift at *
  simp only [show (7:Nat) ≠ 0 by decide, if_false, if_true] at hr ⊢
  unfold TopChoice.blocked
  constructor
  · intro hb
    have : v.toNat / 2 ^ 126 = 0 := Nat.div_eq_of_lt hb
    omega
  · intro hb
    have : topCode v / 2 ^ 126 = 0 := by omega
    rw [hd] at this
    exact (Nat.div_eq_zero_iff_lt (by positivity)).mp this
theorem actual_decoder_count :
    Fintype.card {v : Digest // (T3.decode 0 v).isSome}=R6.count :=
  r6_decoder_count
open OracleComp OracleSpec ENNReal
theorem actual_decoder_probability :
    Pr[fun v => (T3.decode 0 v).isSome | ($ᵗ Digest : ProbComp Digest)]=
      (R6.count : ENNReal)/(2 : ENNReal)^128 := by
  have hc := actual_decoder_count
  rw [Fintype.card_subtype] at hc
  rw [probEvent_uniformSample,hc]
  simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.decode_top_r6
#print axioms SigGolfCandidate.T3.Nonbinary.card_valid_transport
#print axioms SigGolfCandidate.T3.Nonbinary.blocked_iff_r6
#print axioms SigGolfCandidate.T3.Nonbinary.actual_decoder_count
end
