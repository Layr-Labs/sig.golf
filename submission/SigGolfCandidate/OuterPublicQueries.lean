import SigGolfCandidate.OuterHashOnly
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterPublicQueries
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
theorem hashN (coord index heap n : Nat) (left right : Digest) :
    Only (OuterGroundCore.hashN coord index heap n left right) := by
  unfold OuterGroundCore.hashN SigGolfCandidate.T3.Sampling.publicQuery
  exact public_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>public_pure _)

theorem node (coord index heap : Nat) (left right : Digest) :
    Only (OuterGroundCore.nodeAt coord index heap left right) := by
  unfold OuterGroundCore.nodeAt
  have hh : ∀ fuel n,Only (OuterGroundCore.search coord index heap left right fuel n) := by
    intro fuel
    induction fuel with
    | zero => intro n;unfold OuterGroundCore.search;exact public_bind (hashN ..) (fun _=>public_pure _)
    | succ fuel ih =>
      intro n;unfold OuterGroundCore.search
      refine public_bind (hashN ..) fun v=>?_
      split
      · exact public_pure _
      · exact ih _
  exact hh _ _

theorem recover (index coord : Nat) (selected : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) :
    Only (OuterRecover.recover index coord selected word values path prev) := by
  unfold OuterRecover.recover
  exact public_bind (public_recoverSharedInner ..) fun inner=>
    public_bind (node ..) (fun _=>public_pure _)

theorem recoverPair (index pair : Nat) (selected : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    Only (OuterPairModel.recover index pair selected aWord bWord opened prev) := by
  unfold OuterPairModel.recover
  exact public_bind (public_recoverSharedInner ..) fun a=>public_bind (recover ..) (fun _=>public_pure _)

theorem recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    Only (OuterForestCorrectness.recoverSingleton index selected word opened prev) := by
  exact recover ..

theorem recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : Only (OuterForestCorrectness.recoverForest index selected words opened) := by
  unfold OuterForestCorrectness.recoverForest
  refine public_bind (public_foldlM _ _ (fun acc p=>?_) _) fun prev=>?_
  · exact public_bind (recoverPair ..) (fun _=>public_pure _)
  · exact public_bind (recoverSingleton ..) (fun _=>public_pure _)

theorem expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    Only (OuterExpand.expandN message pk sig) := by
  unfold OuterExpand.expandN
  split
  · exact public_pure _
  · refine public_bind (public_sharedDigestSearch ..) fun found=>?_
    rcases found with _|⟨counter,output⟩
    · exact public_pure _
    · refine public_bind (recoverForest ..) fun forest=>?_
      refine public_bind (public_recoverHintedLayers ..) fun layers=>?_
      cases layers
      · exact public_pure _
      · dsimp only
        split
        · exact public_pure _
        · split
          · exact public_pure _
          · refine public_bind (public_searchTop ..) fun found=>?_
            cases found <;> exact public_pure _

theorem expandCompact (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    Only (OuterExpand.expandCompact message pk sig) := by
  unfold OuterExpand.expandCompact
  exact public_map _ (expandN ..)

#print axioms expandCompact
end OuterPublicQueries
