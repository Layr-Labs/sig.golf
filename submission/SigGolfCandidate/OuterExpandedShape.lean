import SigGolfCandidate.OuterSecurityFrozen1
import SigGolfCandidate.OuterGoodOverlay
import SigGolfCandidate.OuterVerifierForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpandedShape
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 W9Machine
open ClaudeWCT.W9.T3M
open W9Drv.SharedCanonical

theorem forest (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (ho : OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.ForestOpenings answers
      (OuterExpand.witEncOuter output w ns) (digestIndex output)
      (rawChildFromOutput output) (fun coord=>embed (forestRank output coord.val))) :
    w.signature.forest=(evalWithAnswerFn answers (OuterForestMoment.forest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  apply Paired.forest_eq_of_coordinates
  · intro coord i
    rw [OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.buildForest_coordinateValues]
    have hc:=((ho.2 coord).2.1 i).1
    change V3.reveal (OuterExpand.witEncOuter output w ns) coord.val i.val
      (wordDigit (forestRank output coord.val) i)=_ at hc
    have hr:=OuterWitnessReadout.chain output w ns coord (forestRank output coord.val)
      (W9Drv.SharedCanonical.coordinateValues w.signature.forest coord)
      (W9Drv.SharedCanonical.chainReadout_witEncF16 output w coord _ _
        (W9Drv.SharedCanonical.chainReadout_witEncF output w coord _ _
          (W9Drv.SharedCanonical.chainReadout_witEncG output w coord _ _
            (W9Drv.SharedCanonical.chainReadout_witEnc output w coord _))))
    exact (hr.reveal i).symm.trans hc
  · intro coord level hl
    rw [OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.buildForest_coordinatePath answers output coord level hl]
    have hp:=SharedV3.physical_lt coord.val (rawChildFromOutput output coord).val (Fin.isLt _)
    have hc:=(ho.2 coord).2
    have hr:=OuterWitnessReadout.path output w ns coord
    by_cases hle : level≤SharedV3.lastLevel coord.val
    · have hl6 : level<6 := by unfold SharedV3.lastLevel at hle;split_ifs at hle <;>omega
      have hs:=OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.PathStepGood.sibling_eq answers
        (OuterExpand.witEncOuter output w ns) (digestIndex output) coord.val
        (SharedV3.physical coord.val (rawChildFromOutput output coord).val) level hp hl6 _ (hc.2.1 level hle)
      rw [hr.siblings level hle] at hs
      exact hs
    · have hm : level≤SharedV3.lastLevel coord.val+1 := by
        by_cases he : coord.val<8 ∧ coord.val%2=0
        · simp only [if_pos he] at hl
          simp [SharedV3.lastLevel,SharedV3.first,he];omega
        · simp only [if_neg he] at hl
          simp [SharedV3.lastLevel,SharedV3.first,he];omega
      have he : level=SharedV3.lastLevel coord.val+1 := by omega
      subst level
      change W9Drv.SharedCanonical.coordinatePath w.signature.forest coord (SharedV3.lastLevel coord.val+1)=_
      rw [←hr.topOther]
      exact hc.2.2
#print axioms forest
end OuterExpandedShape
