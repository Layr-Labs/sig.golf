import SigGolfCandidate.OuterWireVerifier
import SigGolfCandidate.OuterExpandSelections
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterWireEval
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired W9Machine
open SigGolfCandidate.Research.SharedForest
theorem eval_eq (answers : SigGolfCandidate.T3.Correctness.Answers)
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns5)) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk (OuterExpand.witEncOuter output w ns5))=
      evalWithAnswerFn answers (OuterVerifySource.verify message pk w ns5) := by
  obtain ⟨_,counter,result,c,hs,_,_,hw,hc,_⟩ := OuterExpandSelections.selections answers message pk sig output w ns5 he
  have hsearch := sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs
  obtain ⟨hg,hr,_⟩ := accepted_conditions output hsearch.2.2.1
  have hd : evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output := by
    rw [hw,hc,nonce_retained]
    exact hsearch.2.2.2
  have hb : w.digestCounter.toNat<WCT9.digestVerifyWindow := by
    rw [hc]
    have hlt := hsearch.2.1
    unfold WCT9.digestAttemptLimit WCT9.digestVerifyWindow at *
    omega
  exact OuterWireVerifier.source_of answers message pk _ output w ns5
    (OuterVerifierLayers.rho output w ns5)
    (OuterVerifierLayers.dc output w ns5) hd hb hg hr
    (OuterVerifierForest.forest output w ns5 _ (WCT9.digestIndex_lt output))
    (fun left right=>OuterVerifierLayers.layers output w ns5 4 left right (by decide))
#print axioms eval_eq
end OuterWireEval
