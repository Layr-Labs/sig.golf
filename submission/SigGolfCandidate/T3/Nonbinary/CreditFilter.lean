import SigGolfCandidate.T3.Nonbinary.CreditCounting

/-! Credit filter: the producers' search decoder (`T3.searchDecode`: `decode` minus the words below the layer's credit
floor) and its exact acceptance count at the top layer. -/
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

/-- The credit read off the digest's digits is the credit of its parsed word. -/
theorem topCredit_parse {v : Digest} {w : Codec.Word}
    (hp : Decoder.parse 17 v.toNat=some w) : topCredit v=CreditCounting.credit w := by
  unfold topCredit
  rw [range54_map_ofFn,List.ofFn_add (n:=51) (m:=3),List.sum_append]
  change (List.ofFn fun i : Fin (17*3) => if coreDigit 0 v i.val=(if i.val<51 then 3 else 2) then 1 else 0).sum+
      (List.ofFn fun k : Fin 3 =>
        if coreDigit 0 v (51+k.val)=(if 51+k.val<51 then 3 else 2) then 1 else 0).sum=CreditCounting.credit w
  rw [List.ofFn_mul]
  simp only [List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  unfold CreditCounting.credit CreditCounting.credit5 CreditCounting.credit4
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have he := coreDigit_parse5 hp j k
    rw [Nat.mul_comm 3 j.val] at he
    have hlt : j.val*3+k.val<51 := by have := j.isLt;have := k.isLt;omega
    show (if coreDigit 0 v (j.val*3+k.val)=(if j.val*3+k.val<51 then 3 else 2) then 1 else 0)=
      if (w.1 j k).val=3 then 1 else 0
    rw [if_pos hlt,he]
  · apply Finset.sum_congr rfl
    intro k hk
    have he := coreDigit_parse4 hp k
    show (if coreDigit 0 v (51+k.val)=(if 51+k.val<51 then 3 else 2) then 1 else 0)=
      if (w.2 k).val=2 then 1 else 0
    have hn : ¬(51+k.val<51) := by omega
    rw [if_neg hn,he]

theorem decodeBV_parse {v : Digest} {w : Codec.Word} (hw : Decoder.decodeBV v=some w) :
    Decoder.parse 17 v.toNat=some w := by
  change ((Decoder.parse 17 v.toNat).filter fun w => decide (Counting.weight w=126))=some w at hw
  exact (Option.filter_eq_some_iff.mp hw).1

theorem searchDecode_top_isSome (v : Digest) :
    (searchDecode 0 v).isSome=true ↔ ∃ w,Decoder.decodeBV v=some w ∧ creditFloor 0≤CreditCounting.credit w := by
  constructor
  · intro h
    obtain ⟨ds,hds⟩ := Option.isSome_iff_exists.mp h
    have hm := searchDecode_some hds
    rw [decode_top_eq_map] at hm
    cases hw : Decoder.decodeBV v with
    | none => simp [hw] at hm
    | some w =>
    refine ⟨w,rfl,?_⟩
    rw [←topCredit_parse (decodeBV_parse hw)]
    exact searchDecode_top_credit hds
  · rintro ⟨w,hw,hc⟩
    have hd : decode 0 v=some (wordDigits w) := by rw [decode_top_eq_map,hw]; rfl
    rw [searchDecode_top_of hd (by rw [topCredit_parse (decodeBV_parse hw)]; exact hc)]
    rfl

/-- Exact count of the digests the top-layer producer search accepts. -/
theorem searchDecode_top_count :
    Fintype.card {v : Digest // (searchDecode 0 v).isSome=true}=CreditCounting.count := by
  classical
  let e : Digest ≃ Fin (2^128) := ⟨BitVec.toFin,BitVec.ofFin,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr (e.subtypeEquiv (p := fun v => (searchDecode 0 v).isSome=true)
    (q := fun d => ∃ w,Decoder.decode d=some w ∧ CreditCounting.creditFloor≤CreditCounting.credit w)
    (fun v => searchDecode_top_isSome v))]
  convert CreditCounting.credited_decoder_count

end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.topCredit_parse
#print axioms SigGolfCandidate.T3.Nonbinary.searchDecode_top_count
