import SigGolfCandidate.OuterForestDomains
import SigGolfCandidate.OuterPayloadCost
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHashOnly
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.SourceReplay SigGolfCandidate.T3.Cost

 theorem fts_isHash (index : Nat) (q : Spec.Domain)
    (hq : ClaudeWCT.W9.T3.Freshness.Paired.FtsQuery index q) : isHash q := by
  rcases q with (n|input)|coordinate
  · simp only [ClaudeWCT.W9.T3.Freshness.Paired.FtsQuery,ClaudeWCT.WCT9.FtsQuery] at hq
    rcases hq with h|⟨coord,heap,left,pad,right,_,_,_,he⟩
    · exact h.elim
    · cases he
  · trivial
  · trivial

@[aesop safe apply] theorem forest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    HashOnly (OuterForestMoment.forest index selected words) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (OuterForestDomains.forest_queries index selected words)
    (fun q hq=>fts_isHash index q hq)

@[aesop safe apply] theorem hashN (coord index heap n : Nat) (left right : Digest) :
    HashOnly (OuterGroundCore.hashN coord index heap n left right) := by
  unfold OuterGroundCore.hashN SigGolfCandidate.T3.Sampling.publicQuery
  exact hashOnly_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>hashOnly_pure _)

@[aesop safe apply] theorem node (coord index heap : Nat) (left right : Digest) :
    HashOnly (OuterGroundCore.nodeAt coord index heap left right) := by
  unfold OuterGroundCore.nodeAt
  have hh : ∀ fuel n,HashOnly (OuterGroundCore.search coord index heap left right fuel n) := by
    intro fuel
    induction fuel with
    | zero => intro n;unfold OuterGroundCore.search;exact hashOnly_bind (hashN ..) (fun _=>hashOnly_pure _)
    | succ fuel ih =>
      intro n;unfold OuterGroundCore.search
      refine hashOnly_bind (hashN ..) fun v=>?_
      split
      · exact hashOnly_pure _
      · exact ih _
  exact hh _ _

@[aesop safe apply] theorem recover (index coord : Nat) (selected : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) :
    HashOnly (OuterRecover.recover index coord selected word values path prev) := by
  unfold OuterRecover.recover
  exact hashOnly_bind (hashOnly_recoverSharedInner ..) fun inner=>
    hashOnly_bind (node ..) (fun _=>hashOnly_pure _)

@[aesop safe apply] theorem recoverPair (index pair : Nat) (selected : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    HashOnly (OuterPairModel.recover index pair selected aWord bWord opened prev) := by
  unfold OuterPairModel.recover
  exact hashOnly_bind (hashOnly_recoverSharedInner ..) fun a=>hashOnly_bind (recover ..) (fun _=>hashOnly_pure _)

@[aesop safe apply] theorem recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    HashOnly (OuterForestCorrectness.recoverSingleton index selected word opened prev) := by
  exact recover ..

@[aesop safe apply] theorem recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : HashOnly (OuterForestCorrectness.recoverForest index selected words opened) := by
  unfold OuterForestCorrectness.recoverForest
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun acc p=>?_) _) fun prev=>?_
  · exact hashOnly_bind (recoverPair ..) (fun _=>hashOnly_pure _)
  · exact hashOnly_bind (recoverSingleton ..) (fun _=>hashOnly_pure _)

@[aesop safe apply] theorem prepareRoots (index : Nat) : HashOnly (SigGolfCandidate.Research.SharedForest.prepareRoots index) := by
  unfold SigGolfCandidate.Research.SharedForest.prepareRoots
  exact hashOnly_bind (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.hashOnly_buildTreePrefixes ..) fun one=>
    hashOnly_bind (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.hashOnly_buildTreePrefixes ..) fun two=>
      hashOnly_bind (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.hashOnly_buildTreePrefixes ..) (fun _=>hashOnly_pure _)

@[aesop safe apply] theorem searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (root : PairRoot) : HashOnly (OuterSigning.searchPreparedLayers cache index prepared root) := by
  unfold OuterSigning.searchPreparedLayers
  hashes

@[aesop safe apply] theorem signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) : HashOnly (OuterSigning.signFromOutput cache rho counter output) := by
  unfold OuterSigning.signFromOutput
  hashes

@[aesop safe apply] theorem signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (OuterSigning.signPayload cache message) := by
  unfold OuterSigning.signPayload
  hashes

@[aesop safe apply] theorem sign (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (OuterSigning.sign cache message) := by
  unfold OuterSigning.sign
  hashes

@[aesop safe apply] theorem expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    HashOnly (OuterExpand.expandN message pk sig) := by
  unfold OuterExpand.expandN
  split
  · exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_sharedDigestSearch ..) fun found=>?_
    rcases found with _|⟨counter,output⟩
    · exact hashOnly_pure _
    · refine hashOnly_bind (recoverForest ..) fun forest=>?_
      refine hashOnly_bind (hashOnly_recoverHintedLayers ..) fun layers=>?_
      cases layers
      · exact hashOnly_pure _
      · dsimp only
        split
        · exact hashOnly_pure _
        · split
          · exact hashOnly_pure _
          · refine hashOnly_bind (ClaudeWCT.W9.T3.SourceReplay.hashOnly_searchTop ..) fun found=>?_
            cases found <;> exact hashOnly_pure _

@[aesop safe apply] theorem signCompact (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (OuterExpand.signCompact cache message) := by
  unfold OuterExpand.signCompact
  hashes

@[aesop safe apply] theorem expandCompact (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    HashOnly (OuterExpand.expandCompact message pk sig) := by
  unfold OuterExpand.expandCompact
  hashes

#print axioms sign
#print axioms expandN
#print axioms signCompact
#print axioms expandCompact

#print axioms recoverForest
#print axioms prepareRoots
#print axioms searchPreparedLayers

#print axioms forest
#print axioms node
end OuterHashOnly
