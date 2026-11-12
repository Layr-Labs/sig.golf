import SigGolfCandidate.OuterCoordinate
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterCoordinateAvoid
open OracleComp OracleSpec OuterGroundCore
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open SigGolfCandidate.T3M (allQ_pure allQ_bind)
open OuterGroundAvoid
section
variable {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop}
    (hS : OuterSet index S) (coord : Nat) (hc : coord<9) (hco : ∀ c h,S c h→c≠coord)
include hS hc hco

theorem notF_hashN (heap n : Nat) (hh : heap<128) (l r : Digest) :
    AllQueriesSatisfy (hashN coord index heap n l r) (NotF secret index S) := by
  have hne:=node_ne_set hS coord heap hc hh (fun hs => hco coord heap hs rfl)
  unfold hashN publicQuery
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr (notF_public (fTrial_header coord index heap n l r) hne))
    (fun _ => allQ_pure _)

theorem notF_search (heap : Nat) (hh : heap<128) (l r : Digest) :
    ∀ fuel n,AllQueriesSatisfy (search coord index heap l r fuel n) (NotF secret index S)
  | 0,n => by unfold search;exact allQ_bind (notF_hashN hS coord hc hco heap n hh l r) (fun _ => allQ_pure _)
  | fuel+1,n => by
    unfold search
    apply allQ_bind (notF_hashN hS coord hc hco heap n hh l r)
    intro v
    split
    · exact allQ_pure _
    · exact notF_search heap hh l r fuel (n+1)

theorem notF_finish (nodes : Array Digest) :
    AllQueriesSatisfy (OuterHeapMoment.finish coord index nodes) (NotF secret index S) := by
  unfold OuterHeapMoment.finish nodeAt
  exact allQ_bind (notF_search hS coord hc hco 3 (by decide) _ _ _ _) fun a =>
    allQ_bind (notF_search hS coord hc hco 2 (by decide) _ _ _ _) fun b => allQ_pure _

theorem notF_inner (first : Bool) (pads : Nat → PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterInnerMoment.innerHeap first index coord pads leaves) (NotF secret index S) := by
  unfold OuterInnerMoment.innerHeap
  apply OuterInnerMoment.allQ_foldlM_mem
  intro nodes heap hh
  have hm : 4≤heap ∧ heap<128 := by rw [List.mem_reverse,List.mem_range'_1] at hh;omega
  unfold heapStep
  exact allQ_bind (notF_sharedNode_external hS first coord heap pads _ _ hc hm.2
    (fun hs => hco coord heap hs rfl)) fun _ => allQ_pure _

theorem notF_build (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (OuterCoordinate.build index coord selected word pads) (NotF secret index S) := by
  unfold OuterCoordinate.build OuterHeapMoment.heap
  exact allQ_bind (OuterCoordinate.notF_prelude secret index S hS false coord selected word pads) fun st =>
    allQ_bind (allQ_bind (notF_inner hS coord hc hco false pads st.1) (notF_finish hS coord hc hco))
      (fun _ => allQ_pure _)
end
#print axioms notF_hashN
#print axioms notF_build
end OuterCoordinateAvoid
