import SigGolfCandidate.OuterCompactReplay
import SigGolfCandidate.OuterSourceExpansion
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCompactCorrectness
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
attribute [local irreducible] OuterSigning.signFromOutput OuterExpand.expandN

theorem signPayload_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (message : Message) (pk : Digest)
    (hpk : pk=treeValue (builtTree answers 0 0) 12 0) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (hs : evalWithAnswerFn answers (OuterSigning.signPayload cache message)=some sig) :
    ∃ wit,evalWithAnswerFn answers (OuterExpand.expandCompact message pk (OuterSignatureCodec.compress (sigBC sig)))=some wit := by
  obtain ⟨counter,output,w,hd,hw,rfl⟩:=OuterSignatureComponents.signPayload_components answers cache message sig hs
  let rho:=evalWithAnswerFn answers (privateNonce message)
  have hrho : rho.toNat<R := by
    simp only [rho,privateNonce,evalWithAnswerFn_bind,evalWithAnswerFn_pure,rhoMod_toNat]
    exact rhoMod_lt _
  have hf:=OuterSourceRecovery.signFromOutput_recovery answers cache hcache rho counter output w hw
  obtain ⟨result,hr,hroot,hh,_⟩:=hf.2
  have hd' : evalWithAnswerFn answers (sharedDigestSearch w.signature.rho message 0 digestAttemptLimit)=some (counter,output) := by
    rw [hf.1]
    exact hd
  obtain ⟨wit,he⟩:=OuterSourceExpansion.expand_complete_of_recovered answers message pk w.signature counter output result hd' hr hh (hroot.trans hpk.symm)
  unfold OuterExpand.expandCompact
  rw [OuterCodecSource.signFromOutput_decode_fill answers cache hcache htree hlower hforest rho counter output w hrho hw,
    OuterCodecSource.expandN_fill,evalWithAnswerFn_map,he]
  exact ⟨_,rfl⟩

theorem sign_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (message : Message) (pk : Digest)
    (hpk : pk=treeValue (builtTree answers 0 0) 12 0) (sig : OuterSignatureCodec.NewSig)
    (hs : evalWithAnswerFn answers (OuterExpand.signCompact cache message)=some sig) :
    ∃ wit,evalWithAnswerFn answers (OuterExpand.expandCompact message pk sig)=some wit := by
  obtain ⟨raw,hr,rfl⟩:=OuterCompactReplay.compact_some answers cache message sig hs
  unfold OuterSigning.sign at hr
  simp only [evalWithAnswerFn_bind] at hr
  split_ifs at hr
  · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hr
  · exact signPayload_expands answers cache hcache htree hlower hforest message pk hpk raw hr

#print axioms signPayload_expands
#print axioms sign_expands
end OuterCompactCorrectness
