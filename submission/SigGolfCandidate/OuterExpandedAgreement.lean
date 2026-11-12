import SigGolfCandidate.OuterWireAgreement
import SigGolfCandidate.OuterExpandRecovered
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpandedAgreement
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput Layer)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT ClaudeWCT.WCT9 W9Machine
open ClaudeWCT.W9.T3M.Final ClaudeWCT.W9.T3M.Final.Credit ClaudeWCT.W9.T3M.Final.Credit.Paired
theorem agree (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn (machineAnswers hash 0) (OuterExpand.expandN message pk sig)=some (output,w,ns5)) :
    ∃ floors : Layer → Nat,OuterVerifyBudget.CreditFloors74 floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk (OuterExpand.witEncOuter output w ns5))) := by
  obtain ⟨result,hr,hh,hc,hd,ha,htop,hln,hfn,hfn16,hfn5⟩ := OuterExpandRecovered.recovered _ message pk sig output w ns5 he
  simp only [OuterExpandRecovered.recoveredWitness,evalWithAnswerFn_bind] at hr
  obtain ⟨floors,hfloors,hagree⟩ := OuterCreditAgreement.agree hash message pk w ns5 output result hd hr hh hc htop hln hfn hfn16 hfn5
  obtain ⟨hg,hrank,_⟩ := accepted_conditions output ha
  refine ⟨floors,hfloors,agree_verifyP_of_old (fun _ hq => (okHashBy_eq_of_not_enc floors w.topHigh hash hq).symm)
    message pk _ (OuterWireAgreement.source_of hash (okHashBy floors w.topHigh hash) message pk _ output w ns5
    (OuterVerifierLayers.rho output w ns5)
    (OuterVerifierLayers.dc output w ns5) hd hg hrank
    (OuterVerifierForest.forest output w ns5 _ (WCT9.digestIndex_lt output))
    (fun left right=>OuterVerifierLayers.layers output w ns5 4 left right (by decide)) hagree)⟩

#print axioms agree
end OuterExpandedAgreement
