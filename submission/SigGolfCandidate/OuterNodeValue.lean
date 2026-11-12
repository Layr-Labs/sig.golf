import SigGolfCandidate.OuterExtractModel
import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeValue
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M.Extract.Paired

theorem value (answers : Answers) (coord index heap : Nat) (left right : Digest) :
    (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index heap left right)).2=
      evalWithAnswerFn answers (OuterGroundCore.hashN coord index heap
        (evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index heap left right)).1 left right) := by
  rw [OuterGroundCore.nodeAt,OuterGroundDeterministic.eval_search]
  exact OuterGroundDeterministic.scan_value coord (OuterGroundDeterministic.response answers coord index heap left right) _ _

theorem projection (coord index nd : Nat) (hc : coord<9) (hf : first coord=false) (hn : nd<2)
    (a : HashOutput) :
    OuterGroundCore.value coord (2+nd) a=proj (.wctNode index coord 5 nd) a := by
  have hp : ¬(coord<8 ∧ coord%2=0) := by
    simpa only [first,decide_eq_false_iff_not] using hf
  by_cases he : coord=8
  · subst coord
    interval_cases nd <;> rfl
  · have hl : coord<8:=by omega
    have ho : coord%2=1:=by omega
    simp [OuterGroundCore.value,OuterGroundCore.offset,proj,highNodeAt,highPosition,singletonHigh,he,hl,ho]
#print axioms value
#print axioms projection
end OuterNodeValue
