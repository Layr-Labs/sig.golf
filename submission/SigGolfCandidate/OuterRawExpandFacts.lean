import SigGolfCandidate.OuterRawExpand
import SigGolfCandidate.OuterExpandSelections
import SigGolfCandidate.OuterVerifierLayers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterRawExpandFacts
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired

theorem expandB_some (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (wb : WBytes)
    (he : evalWithAnswerFn answers (OuterRawExpand.expandB message pk sig)=some wb) :
    ∃ output w ns,evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns) ∧
      wb=OuterExpand.witEncOuter output w ns := by
  unfold OuterRawExpand.expandB at he
  rw [evalWithAnswerFn_map] at he
  cases hn : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) with
  | none=>simp only [hn,Option.map_none,reduceCtorEq] at he
  | some found=>
    obtain ⟨output,w,ns⟩:=found
    simp only [hn,Option.map_some,Option.some.injEq] at he
    exact ⟨output,w,ns,rfl,he.symm⟩

theorem digest (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns)) :
    evalWithAnswerFn answers (SigGolfCandidate.T3.digest (wrho (OuterExpand.witEncOuter output w ns)) message
      (wdc (OuterExpand.witEncOuter output w ns)))=output := by
  obtain ⟨_,counter,_,c,hs,_,_,hw,hc,_⟩:=OuterExpandSelections.selections answers message pk sig output w ns he
  have hd := (sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0 counter output (by decide) hs).2.2.2
  rw [OuterVerifierLayers.rho,OuterVerifierLayers.dc,hw,hc,nonce_retained]
  exact hd

theorem nonce (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns)) :
    wrho (OuterExpand.witEncOuter output w ns)=sig.rho := by
  obtain ⟨_,_,_,c,_,_,_,hw,_,_⟩:=OuterExpandSelections.selections answers message pk sig output w ns he
  rw [OuterVerifierLayers.rho,hw,nonce_retained]
#print axioms expandB_some
#print axioms digest
#print axioms nonce
end OuterRawExpandFacts
