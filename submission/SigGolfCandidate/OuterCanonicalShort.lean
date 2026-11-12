import SigGolfCandidate.OuterCanonicalForestCount
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalShort
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
theorem hashN_short (coord index heap n : Nat) (left right : Digest) :
    ShortRespects (OuterGroundCore.hashN coord index heap n left right) := by
  rw [OuterVerifierHash.hashN_eq]
  split
  · exact topLow_short _ _ _ _ _ _
  · exact topHigh_short _ _ _ _ _ _

theorem search_short (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    ShortRespects (OuterGroundCore.search coord index heap left right fuel n) := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact ShortRespects.bind (hashN_short _ _ _ _ _ _) fun _=>ShortRespects.pure' _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply ShortRespects.bind (hashN_short _ _ _ _ _ _)
    intro value
    split
    · exact ShortRespects.pure' _
    · exact ih _

theorem node_short (coord index heap : Nat) (left right : Digest) :
    ShortRespects (OuterGroundCore.nodeAt coord index heap left right) :=search_short _ _ _ _ _ _ _

theorem inner_short (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    ShortRespects (OuterInnerMoment.innerHeap first index coord pads leaves) := by
  unfold OuterInnerMoment.innerHeap
  apply ShortRespects.foldlM _ _
  intro heap _ nodes
  unfold ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.heapStep
  exact ShortRespects.bind (sharedNode_short _ _ _ _ _ _ _) fun _=>ShortRespects.pure' _

theorem finish_short (coord index : Nat) (nodes : Array Digest) :
    ShortRespects (OuterHeapMoment.finish coord index nodes) := by
  unfold OuterHeapMoment.finish
  exact ShortRespects.bind (node_short _ _ _ _ _) fun _=>ShortRespects.bind (node_short _ _ _ _ _) fun _=>ShortRespects.pure' _

theorem heap_short (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    ShortRespects (OuterHeapMoment.heap coord index pads leaves) :=
  ShortRespects.bind (inner_short _ _ _ _ _) fun _=>finish_short _ _ _


theorem hybrid_short (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    ShortRespects (OuterCanonicalModel.heap first index coord pads leaves) := by
  cases first
  · exact heap_short _ _ _ _
  · exact sharedHeap_short _ _ _ _ _
#print axioms hybrid_short
end OuterCanonicalShort
