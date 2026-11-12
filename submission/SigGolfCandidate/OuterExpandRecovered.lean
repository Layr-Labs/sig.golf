import SigGolfCandidate.OuterExpandNonces
import SigGolfCandidate.OuterExpandSelections
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterExpandRecovered
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Paired
def recoveredWitness (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput) :
    M (Option RecoveredLayers) := do
  let forest ← OuterForestCorrectness.recoverForest (WCT9.digestIndex output) (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest
  recoverHintedLayers w.signature (WCT9.digestIndex output) ((w.signature.layers 0).path WCT9.topJ)
    4 (.pair forest.1.1 forest.1.2)

theorem recovered (answers : Correctness.Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns5)) :
    ∃ result,evalWithAnswerFn answers (recoveredWitness w output)=some result ∧
      OuterSigning.policyHintsValid (WCT9.digestIndex output) w.signature.policyHints result.digits result.lows=true ∧
      (∀lay,w.counters lay=result.counters.getD lay.val 0) ∧
      evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output ∧
      digestAccepted output=true ∧ w.topHigh = !(result.lows.getD 0 true) ∧
      (∀ lay, w.lowerNonces lay = result.lowerNonces.getD lay.val []) ∧
      w.ftsNonces = (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.1 ∧
      w.ftsNonces16 = (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.2.1 ∧
      ns5 = (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.2.2 := by
  obtain ⟨_,counter,result,c,hs,hr,hh,hw,hc,hcs,htop⟩ := OuterExpandSelections.selections answers message pk sig output w ns5 he
  obtain ⟨result0, -, hr0', -, -, hlow, hfts, hfts16,hfts5⟩ := OuterExpandNonces.nonces_raw answers message pk sig output w ns5 he
  have hres : result0 = result := Option.some.inj (hr0'.symm.trans hr)
  let index := WCT9.digestIndex output
  let forest := evalWithAnswerFn answers (OuterForestCorrectness.recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let other := ((fillTopSignature sig 0).layers 0).path WCT9.topJ
  let other' := ((fillTopSignature sig c).layers 0).path WCT9.topJ
  let result' : RecoveredLayers := {result with root:=evalWithAnswerFn answers (WCT9.topNode index result.foldedTop other')}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 (.pair forest.1.1 forest.1.2))=some result := by
    rw [recoverHintedLayers_fill _ _ _ _ _ (by decide)] at hr
    exact hr
  have hr1 := eval_recoverHintedLayers_other answers sig index other other' 4 (.pair forest.1.1 forest.1.2)
  rw [hr0] at hr1
  have hr2 : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig c) index other'
      4 (.pair forest.1.1 forest.1.2))=some result' := by
    rw [recoverHintedLayers_fill _ _ _ _ _ (by decide)]
    exact hr1
  have hs' := sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs
  refine ⟨result',?_,?_,?_,?_,hs'.2.2.1,htop,?_,?_,?_,?_⟩
  · rw [recoveredWitness,evalWithAnswerFn_bind,hw]
    exact hr2
  · rw [hw,hints_retained]
    exact hh
  · exact hcs
  · rw [hw,hc,nonce_retained]
    exact hs'.2.2.2
  · intro lay
    rw [hlow lay, hres]
  · rw [hfts, hw]
    try rfl
  · rw [hfts16, hw]
    try rfl
  · rw [hfts5, hw]
    try rfl

#print axioms recovered
end OuterExpandRecovered
