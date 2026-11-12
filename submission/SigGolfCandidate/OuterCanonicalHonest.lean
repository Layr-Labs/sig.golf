import SigGolfCandidate.OuterCanonicalShort
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalHonest
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
theorem inner_honest (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hvalues : ∀ i, values i = chainValue answers index coord (rawChild first selected.val) word i)
    (hpath : ∀ level, level < 5 → path level =
      authAt (OuterCanonicalModel.nodes answers first index coord pads) selected.val level) :
    (evalWithAnswerFn answers (recoverSharedInner first index coord selected word values path
      (pads (selected.val / 64)))).1 =
      (OuterCanonicalModel.nodes answers first index coord pads).getD ((128 + selected.val) / 32) 0 := by
  cases first
  · exact OuterCoordinateCorrectness.recover_inner answers index coord selected word pads values path hvalues hpath
  · exact recoverSharedInner_honest answers true index coord selected word pads values path hvalues hpath
#print axioms inner_honest
end OuterCanonicalHonest
