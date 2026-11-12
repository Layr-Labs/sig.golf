import SigGolfCandidate.OuterExpandRecovered
import SigGolfCandidate.OuterVerifierLayers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterExpandedCap
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput Layer)
open SigGolfCandidate.T3M (mrealize mrealize_publicHash)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M.Final ClaudeWCT.W9.T3M.Final.Credit ClaudeWCT.W9.T3M.Final.Credit.Paired
theorem cap (floors : Layer → Nat) (high : Bool) (hash : Hash)
    (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn (machineAnswers hash 0) (OuterExpand.expandN message pk sig)=some (output,w,ns5)) :
    ClaudeWCT.W9.T3M.Final.Paired.DigestCapOk (okHashBy floors high hash) message (OuterExpand.witEncOuter output w ns5) := by
  obtain ⟨_,_,_,_,hd,ha,_,_,_,_,_⟩ := OuterExpandRecovered.recovered _ message pk sig output w ns5 he
  have hagree := agree_mrealize (notEnc_digest w.signature.rho message w.digestCounter) (hfg_okBy floors high hash)
  have hd' : evalWithAnswerFn (machineAnswers (okHashBy floors high hash) 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output := by
    rw [←eval_mrealize,←agree_eval hagree,eval_mrealize,hd]
  rw [←eval_mrealize] at hd'
  unfold SigGolfCandidate.T3.digest at hd'
  rw [mrealize_publicHash,eval_liftQ] at hd'
  unfold ClaudeWCT.W9.T3M.Final.Paired.DigestCapOk
  rw [OuterVerifierLayers.rho,OuterVerifierLayers.dc,hd']
  exact (accepted_conditions output ha).2.2.trans (by norm_num)
#print axioms cap
end OuterExpandedCap
