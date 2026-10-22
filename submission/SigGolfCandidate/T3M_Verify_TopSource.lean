import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_TopLayer
import SigGolfCandidate.T3M_Search_TopTables

namespace SigGolfCandidate.T3M.TopSource
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9 (topRejectLength topGroupBad topRejectChains topGroupValid topChecksumOk)
theorem chainCount0 : chainCount 0=51 := rfl
theorem length_finRange0 : (List.finRange (chainCount 0)).length=51 := by simp [chainCount0]
/-- Campaign T51: a group is checked at its first chain (r6 groups g0..g8 at chains 0..24, r5 groups q9..q15 at
27..45, the r7 pair at 48), the checksum before chain 50. -/
theorem topGroupBad_iff (a : Digest) (i : Nat) :
    topGroupBad a i=true ↔
      ((i%3=0 ∧ i<50 ∧ topGroupValid a (i/3)=false) ∨ (i=50 ∧ topChecksumOk a=false)) := by
  unfold topGroupBad
  simp only [Bool.or_eq_true, decide_eq_true_eq]

/-- Campaign T51 (no spare bit): the verifier runs exactly the chains before the first bad position. -/
theorem topRejectLength_bad (a : Digest) (j : Nat) (hj : j<51)
    (hgood : ∀ i, i<j → topGroupBad a i=false) (hbad : topGroupBad a j=true) :
    topRejectLength a=j := by
  have hv := a.isLt
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega)]
  rw [List.findIdx_eq (by rw [length_finRange0]; omega)]
  refine ⟨?_,fun k hk => ?_⟩
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hbad
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hgood k hk

theorem take_mapM {β : Type} (g : Nat → M β) (m : Nat) (hm : m ≤ 51) :
    ((List.finRange (chainCount 0)).take m).mapM (fun i => g i.val)=(List.range' 0 m).mapM g := by
  have e : ((List.finRange (chainCount 0)).take m).map Fin.val=List.range' 0 m := by
    apply List.ext_getElem
    · simp [chainCount0]; omega
    · intro k h1 h2; simp
  rw [← e, List.mapM_map]; rfl

end SigGolfCandidate.T3M.TopSource
