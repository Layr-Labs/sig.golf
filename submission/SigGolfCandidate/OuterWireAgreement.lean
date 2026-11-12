import SigGolfCandidate.OuterCreditAgreement
import SigGolfCandidate.OuterWireVerifier
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterWireAgreement
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT ClaudeWCT.WCT9 W9Machine
open ClaudeWCT.W9.T3M.Final ClaudeWCT.W9.T3M.Final.Credit ClaudeWCT.W9.T3M.Final.Credit.Paired
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3M.Paired (ftsP_accepted)
theorem source_of (f g : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (hrho : wrho wb=w.signature.rho) (hdc : wdc wb=w.digestCounter)
    (hd : evalWithAnswerFn (machineAnswers f 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output)
    (hg : output.toNat/2^242%16384<929)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563)
    (hf : SharedV3.forest wb (WCT9.digestIndex output) (rawChildFromOutput output)
      (fun k=>WCT9.embed (forestRank output k.val)) =
      OuterFixedForest.forest (WCT9.digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) w.signature.forest w.ftsNonces w.ftsNonces16 ns5)
    (hl : ∀left right,layersCanonicalBC wb (WCT9.digestIndex output) 4 (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) 4 (.pair left right))
    (hagree : Agree f g (mrealize 0 (OuterVerifySource.verify message pk w ns5))) :
    Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyPOld message pk wb)) := by
  have hb : ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow := by
    exact Nat.not_le.mpr w.digestCounter.isLt
  have ha : verifyDigestAccepted output=true := by
    simp only [verifyDigestAccepted,hg,decide_true,Bool.true_and]
    exact (ranksAccepted_iff output).mpr hr
  simp only [OuterVerifySource.verify,hb,↓reduceIte] at hagree
  rw [agree_mrealize_bind] at hagree
  obtain ⟨hDigest,hNext⟩ := hagree
  rw [hd] at hNext
  simp only [ha,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hNext
  unfold ClaudeWCT.W9.T3M.Paired.verifyPOld digestP
  rw [hdc,hrho,if_neg hb,bind_map_left,agree_mrealize_bind]
  refine ⟨hDigest,?_⟩
  rw [hd]
  dsimp only
  rw [ftsP_accepted wb output hg hr,hf]
  simp only [bind_map_left,bind_assoc,pure_bind,hl]
  convert hNext using 1
  rfl
#print axioms source_of
end OuterWireAgreement
