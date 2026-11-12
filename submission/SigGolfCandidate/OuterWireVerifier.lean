import SigGolfCandidate.OuterVerifierForest
import SigGolfCandidate.OuterVerifierLayers
import SigGolfCandidate.OuterVerifySource
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterWireVerifier
open ClaudeWCT SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired W9Machine W9Drv.SharedCanonical
theorem source_of (answers : SigGolfCandidate.T3.Correctness.Answers)
    (message : Message) (pk : Digest) (wb : ClaudeWCT.W9.T3M.WBytes)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (hrho : wrho wb=w.signature.rho) (hdc : wdc wb=w.digestCounter)
    (hd : evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output)
    (hbound : w.digestCounter.toNat<WCT9.digestVerifyWindow)
    (hg : output.toNat/2^242%16384<929)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563)
    (hf : SharedV3.forest wb (WCT9.digestIndex output) (rawChildFromOutput output)
      (fun k=>WCT9.embed (forestRank output k.val)) =
      OuterFixedForest.forest (WCT9.digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) w.signature.forest w.ftsNonces w.ftsNonces16 ns5)
    (hl : ∀left right,layersCanonicalBC wb (WCT9.digestIndex output) 4 (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) 4 (.pair left right)) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk wb)=
      evalWithAnswerFn answers (OuterVerifySource.verify message pk w ns5) := by
  have hd' : evalWithAnswerFn answers (digestP message wb)=some output := by
    simp only [digestP,hdc,hrho,show ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow by omega,
      ↓reduceIte,evalWithAnswerFn_map,hd]
  have ha : verifyDigestAccepted output=true := by
    simp only [verifyDigestAccepted,hg,decide_true,Bool.true_and]
    exact (ranksAccepted_iff output).mpr hr
  rw [ClaudeWCT.W9.T3M.Paired.verifyP,evalWithAnswerFn_bind,hd']
  simp only [ftsP_accepted wb output hg hr,hf,evalWithAnswerFn_bind,evalWithAnswerFn_pure,
    eval_layersCanonicalBCW answers wb _ 4 le_rfl,hl]
  simp only [OuterVerifySource.verify,
    show ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow by omega,↓reduceIte,
    evalWithAnswerFn_bind,hd,ha,Bool.not_true,Bool.false_eq_true,hl]
  rfl

#print axioms source_of
end OuterWireVerifier
