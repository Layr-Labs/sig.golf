import SigGolfCandidate.Merge124
import SigGolfCandidate.OuterSourceQueries
import SigGolfCandidate.OuterVerifierHash
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterWorldFree
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SourceQueries
open ClaudeWCT.W9.T3.Security.WPair ClaudeWCT.W9.T3.Security.WPair.Paired
theorem layers_free (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) :
    AllQueriesSatisfy (OuterSigning.searchPreparedLayers cache index prepared forest) WFree := by
  unfold OuterSigning.searchPreparedLayers
  apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
  rintro (_ | ⟨c0, d0⟩)
  · exact pure_allowed _ _
  · dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
      rintro (_ | ⟨c1, d1⟩)
      · exact pure_allowed _ _
      · dsimp only
        split
        · exact pure_allowed _ _
        · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
          rintro (_ | ⟨c2, d2⟩)
          · exact pure_allowed _ _
          · dsimp only
            split
            · exact pure_allowed _ _
            · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
              rintro (_ | ⟨c3, d3⟩)
              · exact pure_allowed _ _
              · exact bind_allowed WFree (signTop_free _ _ _) fun _ => pure_allowed _ _

theorem hashN_free (coord index heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) WFree := by
  rw [OuterVerifierHash.hashN_eq]
  split
  · exact lowTop_free _ _ _ _ _ _
  · exact wctTopHash_free _ _ _ _ _ _

theorem search_free (coord index heap : Nat) (left right : Digest) : ∀fuel n,
    AllQueriesSatisfy (OuterGroundCore.search coord index heap left right fuel n) WFree := by
  intro fuel
  induction fuel with
  | zero=>intro n;unfold OuterGroundCore.search;exact bind_allowed WFree (hashN_free ..) fun _=>pure_allowed _ _
  | succ fuel ih=>
    intro n
    unfold OuterGroundCore.search
    apply bind_allowed WFree (hashN_free ..)
    intro value
    split
    · exact pure_allowed _ _
    · exact ih _

theorem node_free (coord index heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.nodeAt coord index heap left right) WFree :=search_free ..

theorem inner_free (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterInnerMoment.innerHeap first index coord pads leaves) WFree := by
  unfold OuterInnerMoment.innerHeap
  apply foldlM_allowed WFree
  intro nodes heap
  unfold ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.heapStep
  exact bind_allowed WFree (sharedNode_free ..) fun _=>pure_allowed _ _

theorem finish_free (coord index : Nat) (nodes : Array Digest) :
    AllQueriesSatisfy (OuterHeapMoment.finish coord index nodes) WFree := by
  unfold OuterHeapMoment.finish
  exact bind_allowed WFree (node_free ..) fun _=>bind_allowed WFree (node_free ..) fun _=>pure_allowed _ _

theorem heap_free (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterHeapMoment.heap coord index pads leaves) WFree :=
  bind_allowed WFree (inner_free ..) fun _=>finish_free ..

#print axioms layers_free
#print axioms heap_free
end OuterWorldFree
