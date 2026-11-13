import SigGolfCandidate.OuterCodecSource
import SigGolfCandidate.OuterLooseSource
import SigGolfCandidate.OuterCompactReplay
import SigGolfCandidate.OuterPayloadCost
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterLooseReplay
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SearchCost (cost)
open ClaudeWCT.W9.T3M.SharedCodec
attribute [local irreducible] cost OuterExpand.expandN OuterSigning.signFromOutput
  OuterLooseCodec.compress ClaudeWCT.W9.T3M.SharedCodec.sigBC

theorem sign_expand_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (hs : evalWithAnswerFn answers (OuterSigning.sign cache message)=some sig) :
    cost answers (OuterExpand.expandCompact message pk (OuterLooseCodec.compress (sigBC sig)))=
      cost answers (OuterExpand.expandN message pk sig) := by
  have hp : evalWithAnswerFn answers (OuterSigning.signPayload cache message)=some sig := by
    unfold OuterSigning.sign at hs
    simp only [evalWithAnswerFn_bind] at hs
    split_ifs at hs
    · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hs
    · exact hs
  obtain ⟨counter,output,w,hd,hw,rfl⟩:=OuterSignatureComponents.signPayload_components answers cache message sig hp
  rw [OuterLooseSource.signFromOutput_eq answers cache _ counter output w hforest hw]
  exact OuterCompactReplay.sign_expand_cost answers cache hcache htree hlower hforest message pk w.signature hs

theorem compact_some (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message) (b : OuterSignatureCodec.NewSig)
    (hs : evalWithAnswerFn answers (OuterLooseSource.signCompact cache message)=some b) :
    ∃ sig,evalWithAnswerFn answers (OuterSigning.sign cache message)=some sig ∧
      OuterLooseCodec.compress (sigBC sig)=b := by
  unfold OuterLooseSource.signCompact at hs
  rw [evalWithAnswerFn_map] at hs
  cases he : evalWithAnswerFn answers (OuterSigning.sign cache message) with
  | none=>simp only [he,Option.map_none,reduceCtorEq] at hs
  | some sig=>
    simp only [he,Option.map_some,Option.some.injEq] at hs
    exact ⟨sig,rfl,hs⟩

theorem sign_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    cost answers (OuterLooseSource.signCompact cache message)=cost answers (OuterSigning.sign cache message) := by
  rw [OuterLooseSource.signCompact,ClaudeWCT.W9.T3.ExpansionBudget.cost_map']

theorem good_excess (answers : Answers) (message : Message) (b : OuterSignatureCodec.NewSig)
    (htree : TopTreeOK answers) (hlower : LowerTreesOK answers) (hforest : OuterHybridGlobalCorrectness.ForestsOK answers)
    (hs : evalWithAnswerFn answers (OuterLooseSource.signCompact (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=some b) :
    cost answers (OuterExpand.expandCompact message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 b)≤
      cost answers (OuterLooseSource.signCompact (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)+145480+
        max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  obtain ⟨sig,hsg,hb⟩:=compact_some answers _ message b hs
  have hk:=SigGolfCandidate.T3.Correctness.keygen_correct answers
  rw [←hb,sign_expand_cost answers _ hk.2.1 htree hlower hforest message _ sig hsg,sign_cost]
  exact OuterPayloadCost.expand_cost_le_sign_field answers message sig hsg

#print axioms sign_expand_cost
#print axioms good_excess
end OuterLooseReplay
