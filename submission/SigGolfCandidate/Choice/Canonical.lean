import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest

/-! Signature expansion supplies the premise used by the conditional
extraction invariant. -/
namespace SigGolfCandidate.Choice
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT ClaudeWCT.W9.T3M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem searchHint_original (answers : Correctness.Answers) (lay : Layer)
    (tree leaf : Nat) (msg : WCT9.LayerMsg) (start fuel : Nat)
    (counter : BitVec 32) (digits : List Nat) (hint : BitVec 64)
    (h : evalWithAnswerFn answers (WCT9.layerCounterSearchHint lay tree leaf msg start fuel) =
      some (counter, digits, hint)) :
    evalWithAnswerFn answers (WCT9.layerCounterSearch lay tree leaf msg start fuel) =
      some (counter, digits) := by
  have he := congrArg (evalWithAnswerFn answers)
    (WCT9.layerCounterSearchHint_forget lay tree leaf msg start fuel)
  simpa only [evalWithAnswerFn_map, h, Option.map_some] using he.symm

theorem canonicalFrame_of_searchHint (answers : Correctness.Answers) (N : HashOutput)
    (wit : WCT9.Witness) (lay : Layer) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) (digits : List Nat) (hint : BitVec 64)
    (hctr : wit.counters lay = counter)
    (hmsg : msg = Extract.honestMsg answers (WCT9.digestIndex N) lay)
    (hs : evalWithAnswerFn answers (WCT9.layerCounterSearchHint lay
      (route (WCT9.digestIndex N) lay).2 (route (WCT9.digestIndex N) lay).1 msg 0
      (WCT9.searchLimit lay)) = some (counter, digits, hint))
    (hhint : lay = 0 → wit.topHint = hint) :
    Extract.CanonicalFrame answers (witEnc N wit) (WCT9.digestIndex N) lay := by
  by_cases hl : lay = 0
  · have hlimit := WCT9.searchLimit_le lay
    obtain ⟨_, _, hh, _⟩ := WCT9.layerCounterSearchHint_some answers lay
      (route (WCT9.digestIndex N) lay).2 (route (WCT9.digestIndex N) lay).1 msg
      (WCT9.searchLimit lay) 0 counter digits hint (by unfold counterLimit at hlimit; omega) hs
    have hright : wbcRight (witEnc N wit) = 0 := wright3_witEnc N wit
    dsimp only [Extract.CanonicalFrame]
    rw [wbcCtr_witEnc, wbcPad_witEnc, wbcHigh_witEnc, hright,
      Witness.topHint_roundtrip, hctr, ← hmsg,
      verificationHash_layerEncodingInputP_zero, encodingHash_layerEncodingInputP_zero]
    simp only [WCT9.verificationHash, WCT9.encodingHash, evalWithAnswerFn_map]
    rw [hhint hl, hh, WCT9.verificationAnswer_honest]
  · exact Extract.canonicalFrame_lower answers _ _ lay hl

end SigGolfCandidate.Choice

#print axioms SigGolfCandidate.Choice.canonicalFrame_of_searchHint
