import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.TopLayer
import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.TopSource
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9 (topRejectLength topGroupBad topRejectChains)
theorem chainCount0 : chainCount 0=54 := rfl
theorem length_finRange0 : (List.finRange (chainCount 0)).length=54 := by simp [chainCount0]
theorem topGroupBad_iff (a : Digest) (i : Nat) :
    topGroupBad a i=true ↔ (i%3=0 ∧ i<51 ∧ 125 ≤ Search.topRank (topFlip a) (i/3)) := by
  unfold topGroupBad Search.topRank topCode
  simp only [decide_eq_true_eq]
theorem topRejectLength_high (a : Digest) (h : 2^125 ≤ a.toNat) : topRejectLength a=0 := by
  unfold topRejectLength
  rw [if_pos (by simpa [encodedBits] using h)]
theorem topRejectLength_bad (a : Digest) (hv : a.toNat<2^125) (j : Nat) (hj : j ≤ 16)
    (hgood : ∀ q, q<j → Search.topRank (topFlip a) q<125) (hbad : 125 ≤ Search.topRank (topFlip a) j) :
    topRejectLength a=3*j := by
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega)]
  rw [List.findIdx_eq (by rw [length_finRange0]; omega)]
  refine ⟨?_,fun k hk => ?_⟩
  · simp only [List.getElem_finRange,Fin.cast_mk]
    rw [topGroupBad_iff]
    exact ⟨by omega,by omega,by rw [show 3*j/3=j by omega]; exact hbad⟩
  · simp only [List.getElem_finRange,Fin.cast_mk]
    rw [Bool.eq_false_iff,ne_eq,topGroupBad_iff]
    rintro ⟨h1,-,h3⟩
    have := hgood (k/3) (by omega)
    omega
theorem topRejectLength_sum (a : Digest) (hv : a.toNat<2^125) (hgood : ∀ q, q<17 → Search.topRank (topFlip a) q<125) :
    topRejectLength a=54 := by
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega)]
  rw [← length_finRange0, List.findIdx_eq_length]
  intro x _
  rw [Bool.eq_false_iff,ne_eq,topGroupBad_iff]
  rintro ⟨-,h2,h3⟩
  have := hgood (x.val/3) (by omega)
  omega
theorem decode_none_high (a : Digest) (h : 2^125 ≤ a.toNat) : decode 0 a=none := by
  unfold decode; rw [if_pos (by simpa [encodedBits] using h)]
theorem decode_none_bad (a : Digest) (j : Nat) (hj : j<17) (hbad : 125 ≤ Search.topRank (topFlip a) j) :
    decode 0 a=none := by
  rw [Search.decode_top, if_neg]
  rintro ⟨-,hr,-⟩
  unfold topRanksValid at hr
  have := List.all_eq_true.mp hr j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq] at this
  unfold Search.topRank topCode at *
  omega
theorem decode_none_sum (a : Digest) (hs : (Search.topDigits a).sum ≠ 129) : decode 0 a=none := by
  rw [Search.decode_top, if_neg]
  rintro ⟨-,-,h⟩
  exact hs h
theorem take_mapM {β : Type} (g : Nat → M β) (m : Nat) (hm : m ≤ 54) :
    ((List.finRange (chainCount 0)).take m).mapM (fun i => g i.val)=(List.range' 0 m).mapM g := by
  have e : ((List.finRange (chainCount 0)).take m).map Fin.val=List.range' 0 m := by
    apply List.ext_getElem
    · simp [chainCount0]; omega
    · intro k h1 h2; simp
  rw [← e, List.mapM_map]; rfl
end SigGolfCandidate.T3M.TopSource
