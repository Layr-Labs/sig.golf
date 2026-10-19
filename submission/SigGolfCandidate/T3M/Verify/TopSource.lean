import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.TopLayer
import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.TopSource
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9 (topRejectLength topGroupBad topRejectChains topGroupValid topChecksumOk)
theorem chainCount0 : chainCount 0=52 := rfl

theorem length_finRange0 : (List.finRange (chainCount 0)).length=52 := by simp [chainCount0]
/-- Campaign R6: a group is checked at its first chain (r6 / r5 range), the checksum before chain 51. -/
theorem topGroupBad_iff (a : Digest) (i : Nat) :
    topGroupBad a i=true ↔
      ((i%3=0 ∧ i<51 ∧ topGroupValid a (i/3)=false) ∨ (i=51 ∧ topChecksumOk a=false)) := by
  unfold topGroupBad
  simp only [Bool.or_eq_true, decide_eq_true_eq]

/-- Campaign R6: with the spare bit clear, the verifier runs exactly the chains before the first bad position. -/
theorem topRejectLength_bad (a : Digest) (j : Nat) (hj : j<52) (hsp : topSpare a=0)
    (hgood : ∀ i, i<j → topGroupBad a i=false) (hbad : topGroupBad a j=true) :
    topRejectLength a=j := by
  have hv := a.isLt
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega), if_neg (by simpa using hsp)]
  rw [List.findIdx_eq (by rw [length_finRange0]; omega)]
  refine ⟨?_,fun k hk => ?_⟩
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hbad
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hgood k hk

/-- Campaign R6: a set spare bit rejects before any chain. -/
theorem topRejectLength_spare (a : Digest) (hsp : topSpare a≠0) : topRejectLength a=0 := by
  have hv := a.isLt
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega), if_pos hsp]

theorem take_mapM {β : Type} (g : Nat → M β) (m : Nat) (hm : m ≤ 52) :
    ((List.finRange (chainCount 0)).take m).mapM (fun i => g i.val)=(List.range' 0 m).mapM g := by
  have e : ((List.finRange (chainCount 0)).take m).map Fin.val=List.range' 0 m := by
    apply List.ext_getElem
    · simp [chainCount0]; omega
    · intro k h1 h2; simp
  rw [← e, List.mapM_map]; rfl

end SigGolfCandidate.T3M.TopSource
