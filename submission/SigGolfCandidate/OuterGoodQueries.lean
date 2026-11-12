import SigGolfCandidate.OuterForestDomains
import SigGolfCandidate.OuterLooseSource
import SigGolfCandidate.OuterExpansionWorst
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterGoodQueries
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3M (allQ_mono allQ_ite)

theorem fts_good (index : Nat) (q : Spec.Domain)
    (hq : ClaudeWCT.W9.T3.Freshness.Paired.FtsQuery index q) : GoodQuery q := by
  rcases hq with hq|⟨coord,heap,left,pad,right,hc,hl,hh,rfl⟩
  · rcases q with (tag|input)|coordinate
    · trivial
    · have hl:=ClaudeWCT.WCT9.FtsInput.length hq
      simp only [GoodQuery]
      rcases hl with h|h|h <;> rw [h] <;> decide
    · trivial
  · simp only [GoodQuery,pad64_length,wctTopInput_length]
    decide

theorem forest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Good (OuterForestMoment.forest index selected words) :=
  allQ_mono (OuterForestDomains.forest_queries index selected words) (fts_good index)

theorem layers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots) (forest : PairRoot) :
    Good (OuterSigning.searchPreparedLayers cache index prepared forest) := by
  unfold OuterSigning.searchPreparedLayers
  refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
  rcases found with _|⟨counter0,digits0⟩
  · exact good_pure _
  · dsimp only
    refine allQ_ite _ (good_pure _) ?_
    refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
    rcases found with _|⟨counter1,digits1⟩
    · exact good_pure _
    · dsimp only
      refine allQ_ite _ (good_pure _) ?_
      refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
      rcases found with _|⟨counter2,digits2⟩
      · exact good_pure _
      · dsimp only
        refine allQ_ite _ (good_pure _) ?_
        refine good_bind (good_layerCounterSearchAt ..) fun found=>?_
        rcases found with _|⟨counter3,digits3⟩
        · exact good_pure _
        · exact good_bind (good_signTop ..) fun _=>good_pure _

theorem output (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    Good (OuterSigning.signFromOutput cache rho counter output) := by
  unfold OuterSigning.signFromOutput
  refine good_bind (forest ..) fun _=>?_
  refine good_bind (allQueriesSatisfy_of_bound (bound_prepareRoots ..)) fun _=>?_
  refine good_bind (layers ..) fun found=>?_
  cases found <;> exact good_pure _

theorem payload (cache : SigGolfCandidate.T3.Cache) (message : Message) : Good (OuterSigning.signPayload cache message) := by
  unfold OuterSigning.signPayload privateNonce
  refine good_bind (good_bind (good_privateHash _) fun _=>good_pure _) fun _=>?_
  refine good_bind (good_sharedDigestSearch ..) fun found=>?_
  rcases found with _|⟨counter,output⟩
  · exact good_pure _
  · refine good_bind (OuterGoodQueries.output ..) fun found=>?_
    cases found <;> exact good_pure _

theorem sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : Good (OuterSigning.sign cache message) := by
  unfold OuterSigning.sign
  have hmac : Good (privateMac cache.region) := by
    unfold privateMac privateMacKey
    exact good_bind (good_bind (good_privateHash _) fun _=>good_bind (good_privateHash _) fun _=>good_pure _) fun _=>good_pure _
  refine good_bind hmac fun _=>?_
  exact allQ_ite _ (good_pure _) (payload ..)

theorem compactSign (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Good (OuterLooseSource.signCompact cache message) := by
  unfold OuterLooseSource.signCompact
  exact good_map _ (sign ..)

theorem expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    Good (OuterExpand.expandN message pk sig) := SigGolfCandidate.T3M.allQ_of_bound (OuterExpansionWorst.bound_expandN ..)

theorem compactExpand (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    Good (OuterExpand.expandCompact message pk sig) := SigGolfCandidate.T3M.allQ_of_bound (OuterExpansionWorst.bound_expandCompact ..)
#print axioms compactSign
#print axioms compactExpand
end OuterGoodQueries
