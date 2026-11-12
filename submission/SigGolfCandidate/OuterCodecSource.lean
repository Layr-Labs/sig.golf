import SigGolfCandidate.OuterExpand
import SigGolfCandidate.Merge053
import SigGolfCandidate.OuterSignaturePaths
import SigGolfCandidate.OuterSignatureComponents
import SigGolfCandidate.OuterHonestInnerCarriers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCodecSource
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec

theorem signFromOutput_codec (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (hrho : rho.toNat<R)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some w) :
    sigDecC (OuterSignatureCodec.expand (OuterSignatureCodec.compress (sigBC w.signature)))=normTop w.signature := by
  rw [OuterHonestCarriers.signFromOutput_roundtrip answers cache rho counter output w hforest he]
  apply sigDecC_sigBC_normTop
  · exact groundClear_of_lowerPathOK _
      (OuterSignaturePaths.signFromOutput_lowerPathOK answers cache hcache hlower rho counter output w he)
      (ftsSlotsClear_of_ftsPathOK _ (OuterHonestInnerCarriers.signFromOutput_ftsPathOK answers cache hforest rho counter output w he))
  · exact OuterSignatureComponents.rhoHintOK_signFromOutput answers cache rho counter output w hrho he

theorem expandN_fill (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    OuterExpand.expandN message pk (fillTopSignature sig c)=OuterExpand.expandN message pk sig := by
  simp only [OuterExpand.expandN,hints_retained,fillTopSignature_fill]

theorem signFromOutput_decode_fill (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (hrho : rho.toNat<R)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some w) :
    sigDecC (OuterSignatureCodec.expand (OuterSignatureCodec.compress (sigBC w.signature)))=fillTopSignature w.signature 0 := by
  rw [signFromOutput_codec answers cache hcache hlower hforest rho counter output w hrho he]
  apply normTop_eq_fill
  · obtain ⟨layers,hs,_,hh,_⟩:=OuterSignatureComponents.signFromOutput_components answers cache rho counter output w he
    have hf:=OuterPreparedFacts.searchPreparedLayers_some answers cache _ _ _ layers hs
    rw [hh]
    have hb:=hf.hints_spec.1
    omega
  · exact OuterSignaturePaths.signFromOutput_topPathOK answers cache hcache htree rho counter output w he
  · exact OuterSignaturePaths.signFromOutput_lowerPathOK answers cache hcache hlower rho counter output w he

theorem signFromOutput_expand_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (hrho : rho.toNat<R)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some w)
    (message : Message) (pk : Digest) :
    SigGolfCandidate.T3.SearchCost.cost answers
      (OuterExpand.expandCompact message pk (OuterSignatureCodec.compress (sigBC w.signature)))=
      SigGolfCandidate.T3.SearchCost.cost answers (OuterExpand.expandN message pk w.signature) := by
  rw [OuterExpand.expandCompact,signFromOutput_decode_fill answers cache hcache htree hlower hforest rho counter output w hrho he,
    expandN_fill,ClaudeWCT.W9.T3.ExpansionBudget.cost_map']

#print axioms expandN_fill
#print axioms signFromOutput_decode_fill
#print axioms signFromOutput_expand_cost

#print axioms signFromOutput_codec
end OuterCodecSource
