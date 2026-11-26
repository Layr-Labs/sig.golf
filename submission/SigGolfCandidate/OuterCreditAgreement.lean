import SigGolfCandidate.OuterCredit74
import SigGolfCandidate.OuterNotEncForest
import SigGolfCandidate.OuterVerifySource
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCreditAgreement
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput Layer route)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M.Final ClaudeWCT.W9.T3M.Final.Credit ClaudeWCT.W9.T3M.Final.Credit.Paired
theorem agree (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn (machineAnswers hash 0) (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output)
    (hr : evalWithAnswerFn (machineAnswers hash 0)
      (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn (machineAnswers hash 0) (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.1
          (evalWithAnswerFn (machineAnswers hash 0) (OuterForestCorrectness.recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1.2)) = some result)
    (hh : OuterSigning.policyHintsValid (WCT9.digestIndex output) w.signature.policyHints result.digits result.lows = true)
    (hc : ∀ lay, w.counters lay = result.counters.getD lay.val 0)
    (htop : w.topHigh = !(result.lows.getD 0 true))
    (hln : ∀ lay, w.lowerNonces lay = result.lowerNonces.getD lay.val [])
    (hfn : w.ftsNonces = (evalWithAnswerFn (machineAnswers hash 0) (OuterForestCorrectness.recoverForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.1)
    (hfn16 : w.ftsNonces16 = (evalWithAnswerFn (machineAnswers hash 0) (OuterForestCorrectness.recoverForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.2.1)
    (hfn5 : ns5 = (evalWithAnswerFn (machineAnswers hash 0) (OuterForestCorrectness.recoverForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2.2.2) :
    ∃ floors : Layer → Nat, OuterVerifyBudget.CreditFloors74 floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (OuterVerifySource.verify message pk w ns5)) := by
  let floors : Layer → Nat := fun lay =>
    min 74 (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []) +
      if lay=0 then CanonicalPolicy.topPathSave (route (digestIndex output) 0).1 else LocalRoute.ownSave (digestIndex output) lay.val)
  refine ⟨floors, OuterCredit74.recovered _ _ _ _ _ result hr hh, ?_⟩
  unfold OuterVerifySource.verify
  split
  · trivial
  · refine (agree_mrealize_bind _ _).mpr ⟨agree_mrealize (notEnc_digest _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
    rw [hd]
    split
    · trivial
    · refine (agree_mrealize_bind _ _).mpr
        ⟨agree_mrealize (OuterNotEncForest.forest _ _ _ _ _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
      rw [hfn, hfn16, hfn5, OuterFixedForestReplay.eval_forest]
      refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
      · exact agree_layers floors hash w.signature (digestIndex output) (digestIndex_lt output) 4 le_rfl _ result hr
          (fun lay _ => Nat.min_le_right _ _) w rfl (fun lay _ => hc lay) htop (fun lay _ => hln lay)
      · split <;> trivial
#print axioms agree
end OuterCreditAgreement
