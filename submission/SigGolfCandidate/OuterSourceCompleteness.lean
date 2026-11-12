import SigGolfCandidate.OuterCompactCorrectness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSourceCompleteness
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.Research.SharedForest
theorem searchPreparedLayers_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (prepared : PreparedRoots) (forest : PairRoot) :
    ∃ result, evalWithAnswerFn answers (OuterSigning.searchPreparedLayers cache index prepared forest)=some result := by
  let f0 := Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)
  have hb := OuterSigning.requiredCredit_bounds index
  have hf0 : 18≤f0 ∧ f0≤20 := by
    dsimp only [f0]
    rw [Policy75Safe23.threshold_top]
    omega
  obtain ⟨⟨c0,d0,l0⟩,hs0⟩ := context_good_at_route answers hgood index hi 0 f0 (by simpa using hf0)
    (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2
  have hd0 := (canonical_search_some' answers 0 f0 (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
    (searchLimit 0) 0 c0 d0 l0 (by decide) hs0).2.2.2
  let r1 := routeResidual index (OuterSigning.requiredCredit index) 0 l0 d0
  have hr1 : r1<58 := by
    have hraw := Policy75Safe23.accepted_top_residual_pool (OuterSigning.requiredCredit index) hd0
    change CanonicalPolicy.nextResidual (OuterSigning.requiredCredit index) 0 l0 d0 - LocalRoute.ownSave index 1 < 58
    omega
  have hf1' : Policy75Safe23.threshold 1 r1<17 := Policy75Safe23.lower_one_floor_lt ⟨r1,hr1⟩
  have hf1 : Policy75Safe23.threshold 1 r1<19 := by omega
  obtain ⟨⟨c1,d1,l1⟩,hs1⟩ := context_good_at_route answers hgood index hi 1
    (Policy75Safe23.threshold 1 r1) (by simpa only [show (1:Layer)≠0 by decide, show (1:Layer)≠3 by decide, if_false] using hf1)
    (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2
  have hd1 := (canonical_search_some' answers 1 (Policy75Safe23.threshold 1 r1)
    (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2)
    (searchLimit 1) 0 c1 d1 l1 (by decide) hs1).2.2.2
  let r2 := routeResidual index r1 1 l1 d1
  have hr2 : r2<42 := by
    have hraw := Policy75Safe23.accepted_one_residual ⟨r1,hr1⟩ hd1
    change CanonicalPolicy.nextResidual r1 1 l1 d1 < 42 at hraw
    change CanonicalPolicy.nextResidual r1 1 l1 d1 - LocalRoute.ownSave index 2 < 42
    omega
  have hf2 : Policy75Safe23.threshold 2 r2<19 := by
    have h := Policy75Safe23.lower_two_floor_le ⟨r2,hr2⟩
    change Policy75Safe23.threshold 2 r2≤18 at h
    omega
  obtain ⟨⟨c2,d2,l2⟩,hs2⟩ := context_good_at_route answers hgood index hi 2
    (Policy75Safe23.threshold 2 r2) (by simpa only [show (2:Layer)≠0 by decide, show (2:Layer)≠3 by decide, if_false] using hf2)
    (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2
  have hd2 := (canonical_search_some' answers 2 (Policy75Safe23.threshold 2 r2)
    (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2)
    (searchLimit 2) 0 c2 d2 l2 (by decide) hs2).2.2.2
  let r3 := routeResidual index r2 2 l2 d2
  have hr3 : r3<24 := by
    have hraw := Policy75Safe23.accepted_two_residual ⟨r2,hr2⟩ hd2
    change CanonicalPolicy.nextResidual r2 2 l2 d2 < 24 at hraw
    change CanonicalPolicy.nextResidual r2 2 l2 d2 - LocalRoute.ownSave index 3 < 24
    omega
  have hf3 : Policy75Safe23.threshold 3 r3<24 := by
    rw [Policy75Safe23.lower_three_progress r3 hr3]; have := Policy75Safe23.lowerThreeFloor_le r3 hr3; omega
  obtain ⟨⟨c3,d3,l3⟩,hs3⟩ := context_good_at_route answers hgood index hi 3
    (Policy75Safe23.threshold 3 r3) (by simpa only [show (3:Layer)≠0 by decide, if_false, if_true] using hf3) forest.1 forest.2
  have hn1 : ¬Policy75Safe23.threshold 1 r1≥17 := by omega
  have hn2 : ¬Policy75Safe23.threshold 2 r2≥24 := by omega
  have hn3 : ¬Policy75Safe23.threshold 3 r3≥24 := by omega
  dsimp only [f0,r1,r2,r3] at hs0 hs1 hs2 hs3 hn1 hn2 hn3
  simp only [OuterSigning.searchPreparedLayers,
    evalWithAnswerFn_bind,hs0,hn1,if_false,hs1,hn2,hs2,hn3,hs3,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩


theorem signFromOutput_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ∃ witness, evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some witness := by
  let forest := evalWithAnswerFn answers
    (OuterForestMoment.forest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots (digestIndex output))
  obtain ⟨layers,hl⟩ := searchPreparedLayers_complete answers hgood cache (digestIndex output)
    (digestIndex_lt output) prepared forest.2
  dsimp only [forest,prepared] at hl
  simp only [OuterSigning.signFromOutput,evalWithAnswerFn_bind,hl,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem signPayload_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (OuterSigning.signPayload cache message)=some signature := by
  obtain ⟨⟨counter,output⟩,hs⟩ := Option.ne_none_iff_exists'.mp hd
  obtain ⟨witness,hw⟩ := signFromOutput_complete answers hgood cache
    (evalWithAnswerFn answers (privateNonce message)) counter output
  simp only [OuterSigning.signPayload,evalWithAnswerFn_bind,hs,hw,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem sign_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (OuterSigning.sign cache message)=some signature := by
  simpa only [OuterSigning.sign,evalWithAnswerFn_bind,hmac,ne_eq,not_true_eq_false,if_false] using
    signPayload_complete answers hgood cache message hd

def SigningComplete (answers : Answers) (cache : SigGolfCandidate.T3.Cache) : Prop :=
  ∀ message, ∃ signature, evalWithAnswerFn answers (OuterSigning.sign cache message)=some signature

def DigestFailed (answers : Answers) (message : Message) : Prop :=
  evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit)=none

theorem signing_failed_implies_search (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hfail : ¬SigningComplete answers cache) :
    (∃ message, DigestFailed answers message) ∨ (∃ context, ContextFailed context answers) := by
  classical
  by_contra h
  rcases not_or.mp h with ⟨hd,hc⟩
  apply hfail
  intro message
  exact sign_complete answers (not_exists.mp hc) cache message hmac (not_exists.mp hd message)

theorem tableGoodForNonces_signing (outputs : SearchKey → HashOutput) (answers : Answers)
    (nonces : Message → Digest) (hgood : TableGoodForNonces nonces outputs)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers)
    (hnonce : ∀ message, evalWithAnswerFn answers (privateNonce message)=nonces message) :
    SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 := by
  have hcontext : ContextGood answers :=
    (contextGood_agreement outputs answers SigGolfCandidate.T3.Budgets.zeroAnswers hagree).mpr hgood.2
  have hc := (SigGolfCandidate.T3.Correctness.keygen_correct answers).2.2
  have hm : (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.tag=
      evalWithAnswerFn answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) := hc
  intro message
  apply sign_complete answers hcontext _ message hm.symm
  intro hd
  rw [hnonce message] at hd
  exact hgood.1 message ((sharedDigestSearch_none_agreement outputs answers SigGolfCandidate.T3.Budgets.zeroAnswers hagree _ _).mp hd)


theorem compact_complete_of_tables (outputs : ClaudeWCT.W9.T3.QuerySpace.SearchKey→HashOutput)
    (answers : Answers) (nonces : Message→Digest) (hgood : TableGoodForNonces nonces outputs)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers)
    (hnonce : ∀ message,evalWithAnswerFn answers (privateNonce message)=nonces message)
    (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) (message : Message) :
    ∃ sig wit,evalWithAnswerFn answers (OuterExpand.signCompact (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=some sig ∧
      evalWithAnswerFn answers (OuterExpand.expandCompact message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig)=some wit := by
  obtain ⟨raw,hr⟩:=OuterSourceCompleteness.tableGoodForNonces_signing outputs answers nonces hgood hagree hnonce message
  have hs : evalWithAnswerFn answers (OuterExpand.signCompact (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message)=
      some (OuterSignatureCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC raw)) := by
    rw [OuterExpand.signCompact,evalWithAnswerFn_map,hr]
    rfl
  have hk:=SigGolfCandidate.T3.Correctness.keygen_correct answers
  obtain ⟨wit,hw⟩:=OuterCompactCorrectness.sign_expands answers _ hk.2.1 htree hlower hforest message _ hk.1 _ hs
  exact ⟨_,wit,hs,hw⟩

#print axioms tableGoodForNonces_signing
#print axioms compact_complete_of_tables

#print axioms searchPreparedLayers_complete
#print axioms sign_complete
#print axioms signing_failed_implies_search
end OuterSourceCompleteness
