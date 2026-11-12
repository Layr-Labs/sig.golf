import SigGolfCandidate.OuterExpandedSelections
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionSecurity
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.CanonicalExtract
theorem expanded_eq_signer_signature (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w signed : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) (counter : BitVec 32)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some (output,w,ns))
    (hg : ∀ lay, Good answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers) (OuterExpand.witEncOuter output w ns)
      (WCT9.digestIndex output) lay)
    (ho : OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.ForestOpenings answers (OuterExpand.witEncOuter output w ns) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (OuterSigning.signFromOutput cache sig.rho counter output) = some signed) :
    w.signature = signed.signature := by
  have hforest := OuterExpandedShape.forest answers output w ns ho
  obtain ⟨_, _, _, c, _, _, _, hsig, _, _⟩ := OuterExpandSelections.selections answers message pk sig output w ns he
  have hforestSig : sig.forest = w.signature.forest := by rw [hsig];rfl
  have hf : (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1 =
      OuterCanonicalModel.commitment answers (WCT9.digestIndex output) := by
    rw [hforestSig,hforest]
    exact (OuterForestCorrectness.forest_honest answers _ _ _).trans (OuterCanonicalModel.forest_result answers _ _ _)
  obtain ⟨da,la,hva,hsa,hpa⟩ := OuterExpansionSecurity.expanded_canonical_selections answers message pk sig output w ns he (fun lay=>(OuterGoodOverlay.good answers _ output w ns _ lay).mp (hg lay)) hf
  obtain ⟨db,lb,hvb,hsb,hpb⟩ := OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.signFromOutput_canonical_selections answers cache hcache sig.rho counter output signed hs
  obtain ⟨_,_,hrho,_,hfs,_,_,_⟩ := OuterLifted.SigGolfCandidate.Research.SharedForest.signFromOutput_components answers cache sig.rho counter output signed hs
  apply OuterLifted.SigGolfCandidate.Research.SharedForest.signature_unique_of_selections answers (WCT9.digestIndex output)
    (fun lay => OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    w.signature signed.signature w.counters signed.counters da db la lb _ (hforest.trans hfs.symm)
    hva hvb hsa hsb hpa hpb
  rw [hsig,nonce_retained,hrho]

 theorem same_nonce_signed_wire (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig signedSig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig) = some (output,w,ns))
    (hg : ∀ lay, Good answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers) (OuterExpand.witEncOuter output w ns)
      (WCT9.digestIndex output) lay)
    (ho : OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.ForestOpenings answers (OuterExpand.witEncOuter output w ns) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (OuterSigning.signPayload cache message) = some signedSig)
    (hrho : sig.rho = signedSig.rho) :
    SharedCodec.sigBC sig = SharedCodec.sigBC signedSig := by
  obtain ⟨counter,N,signed,hd,hsigned,hsig⟩ := OuterLifted.SigGolfCandidate.Research.SharedForest.signPayload_components answers cache message signedSig hs
  obtain ⟨_,_,hnonce,_,_,_,_,_⟩ := OuterLifted.SigGolfCandidate.Research.SharedForest.signFromOutput_components answers cache
    (evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message)) counter N signed hsigned
  have hr : sig.rho = evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message) :=
    hrho.trans ((congrArg (fun s : SigGolfCandidate.Research.SharedForest.Signature => s.rho) hsig).symm.trans hnonce)
  obtain ⟨_,ec,_,c,hed,_,_,hw,_,_⟩ := OuterExpandSelections.selections answers message pk sig output w ns he
  rw [hr,hd] at hed
  have hout : N=output := congrArg Prod.snd (Option.some.inj hed)
  subst N
  have heq := expanded_eq_signer_signature answers cache hcache message pk sig output w signed ns counter he hg ho
    (by rw [hr];exact hsigned)
  calc
    SharedCodec.sigBC sig = SharedCodec.sigBC (fillTopSignature sig c) := (SharedCodec.sigBC_fillTopSignature sig c).symm
    _ = SharedCodec.sigBC w.signature := by rw [hw]
    _ = SharedCodec.sigBC signedSig := by rw [heq,hsig]
#print axioms same_nonce_signed_wire
end OuterExpansionSecurity
