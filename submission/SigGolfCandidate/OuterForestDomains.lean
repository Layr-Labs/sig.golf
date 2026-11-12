import SigGolfCandidate.OuterForestMoment
import SigGolfCandidate.Merge054
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterForestDomains
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_foldlM)
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh (heapStep)
abbrev Q := ClaudeWCT.W9.T3.Freshness.Paired.FtsQuery

theorem hashN_queries (index coord heap n : Nat) (l r : Digest) (hc : coord<9) (hl : 2≤heap) (hh : heap<32) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n l r) (Q index) := by
  have hq : Q index (.inl (.inr (OuterGroundCore.trial coord index heap n l r))) := by
    refine Or.inr ⟨coord,heap,l,BitVec.ofNat 128 (n%2^64),r,hc,hl,hh,?_⟩
    rfl
  unfold OuterGroundCore.hashN publicQuery
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr hq) (fun _ => allQ_pure _)

theorem search_queries (index coord heap : Nat) (l r : Digest) (hc : coord<9) (hl : 2≤heap) (hh : heap<32) :
    ∀ fuel n,AllQueriesSatisfy (OuterGroundCore.search coord index heap l r fuel n) (Q index)
  | 0,n => by unfold OuterGroundCore.search;exact allQ_bind (hashN_queries index coord heap n l r hc hl hh) (fun _ => allQ_pure _)
  | fuel+1,n => by
    unfold OuterGroundCore.search
    apply allQ_bind (hashN_queries index coord heap n l r hc hl hh)
    intro v
    split
    · exact allQ_pure _
    · exact search_queries index coord heap l r hc hl hh fuel (n+1)

theorem finish_queries (index coord : Nat) (nodes : Array Digest) (hc : coord<9) :
    AllQueriesSatisfy (OuterHeapMoment.finish coord index nodes) (Q index) := by
  unfold OuterHeapMoment.finish OuterGroundCore.nodeAt
  exact allQ_bind (search_queries index coord 3 _ _ hc (by decide) (by decide) _ _) fun _ =>
    allQ_bind (search_queries index coord 2 _ _ hc (by decide) (by decide) _ _) fun _ => allQ_pure _

theorem inner_queries (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (leaves : List Digest) (hc : coord<9) :
    AllQueriesSatisfy (OuterInnerMoment.innerHeap first index coord pads leaves) (Q index) := by
  unfold OuterInnerMoment.innerHeap
  apply OuterInnerMoment.allQ_foldlM_mem
  intro nodes heap hh
  have hm : 4≤heap ∧ heap<128 := by rw [List.mem_reverse,List.mem_range'_1] at hh;omega
  unfold heapStep
  exact allQ_bind (allQueriesSatisfy_of_bound
    (ClaudeWCT.W9.T3.Freshness.Paired.bound_sharedNode first coord index heap pads _ _ hc (by omega) hm.2))
      (fun _ => allQ_pure _)

theorem build_queries (first : Bool) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) (hc : coord<9) :
    AllQueriesSatisfy (OuterForestBudget.buildCoord first index coord selected word pads) (Q index) := by
  cases first with
  | true =>
    rw [OuterForestBudget.buildCoord,if_pos rfl,OuterForestBudget.buildA_eq]
    exact allQueriesSatisfy_of_bound (ClaudeWCT.W9.T3.Freshness.Paired.bound_buildSharedCoordinate true index coord hc selected word pads)
  | false =>
    unfold OuterForestBudget.buildCoord
    simp only [Bool.false_eq_true,↓reduceIte]
    unfold OuterCoordinate.build OuterHeapMoment.heap
    exact allQ_bind (allQueriesSatisfy_of_bound (ClaudeWCT.W9.T3.Freshness.Paired.lift_bound
      (OuterCoordinate.bound_prelude false index coord hc selected word pads))) fun st =>
        allQ_bind (allQ_bind (inner_queries false index coord pads st.1 hc) (fun nodes => finish_queries index coord nodes hc))
          (fun _ => allQ_pure _)

theorem pair_queries (index p : Nat) (hp : p<4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    AllQueriesSatisfy (OuterForestMoment.pair index p s aWord bWord prev) (Q index) := by
  unfold OuterForestMoment.pair
  exact allQ_bind (build_queries true index (2*p) (firstChild s) aWord (fun _ => prev) (by omega)) fun a =>
    allQ_bind (build_queries false index (2*p+1) (secondChild s) bWord (nodesPair a.1) (by omega)) (fun _ => allQ_pure _)

theorem singleton_queries (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    AllQueriesSatisfy (OuterForestMoment.singleton index selected word prev) (Q index) := by
  unfold OuterForestMoment.singleton
  exact allQ_bind (build_queries false index 8 selected word (fun _ => prev) (by decide)) (fun _ => allQ_pure _)

theorem forest_queries (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (OuterForestMoment.forest index selected words) (Q index) := by
  unfold OuterForestMoment.forest
  refine allQ_bind ?_ ?_
  · apply allQ_foldlM
    intro (st : List PairOpening × PairRoot) (p : Fin 4)
    refine allQ_bind (pair_queries index p.val p.isLt (selected.pairs p) (words.first p) (words.second p) st.2) ?_
    intro built
    exact allQ_pure _
  · intro st
    refine allQ_bind (singleton_queries index selected.singleton words.singleton st.2) ?_
    intro last
    exact allQ_pure _

#print axioms forest_queries
end OuterForestDomains
