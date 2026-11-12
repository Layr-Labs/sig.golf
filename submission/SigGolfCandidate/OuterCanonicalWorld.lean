import SigGolfCandidate.OuterCanonicalModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalWorld
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open SourceQueries
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.WPair ClaudeWCT.W9.T3.Security.WPair.Paired

theorem heap_free (first : Bool) (index coord : Nat) (pads : Nat→PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (OuterCanonicalModel.heap first index coord pads leaves) WFree := by
  cases first
  · exact OuterWorldFree.heap_free ..
  · exact sharedHeap_free ..

variable {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs ⊆ U) (ω : ClaudeWCT.W9.CanonTable.Omega U)
theorem nodes_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (first : Bool)
    (index : Nat) (hindex : index < 2 ^ 31) (coord : Fin 9) (pads : Nat → PairRoot) :
    OuterCanonicalModel.nodes (wA hU ω hidden) first index coord.val pads =
      OuterCanonicalModel.nodes (wA hU ω hidden') first index coord.val pads := by
  unfold OuterCanonicalModel.nodes
  rw [sharedLeaves_world hU ω hidden hidden' first index hindex coord]
  exact eval_free hU ω hidden hidden' (heap_free _ _ _ _ _)

theorem firstNodes_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    OuterCanonicalModel.firstNodes (wA hU ω hidden) index pair.val prev = OuterCanonicalModel.firstNodes (wA hU ω hidden') index pair.val prev := by
  exact nodes_world hU ω hidden hidden' true index hindex
    ⟨2 * pair.val, by have := pair.isLt; omega⟩ (fun _ => prev)

theorem secondNodes_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    OuterCanonicalModel.secondNodes (wA hU ω hidden) index pair.val prev = OuterCanonicalModel.secondNodes (wA hU ω hidden') index pair.val prev := by
  unfold OuterCanonicalModel.secondNodes
  rw [firstNodes_world hU ω hidden hidden' index hindex pair]
  exact nodes_world hU ω hidden hidden' false index hindex
    ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _

theorem root_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    OuterCanonicalModel.root (wA hU ω hidden) index pair.val prev =
      OuterCanonicalModel.root (wA hU ω hidden') index pair.val prev := by
  unfold OuterCanonicalModel.root
  rw [secondNodes_world hU ω hidden hidden' index hindex pair]


theorem commitment_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) :
    OuterCanonicalModel.commitment (wA hU ω hidden) index = OuterCanonicalModel.commitment (wA hU ω hidden') index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    root_world hU ω hidden hidden' index hindex ⟨pair, hp⟩ prev
  dsimp only [OuterCanonicalModel.commitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    nodes_world hU ω hidden hidden' false index hindex ⟨8, by decide⟩]

#print axioms commitment_world
end OuterCanonicalWorld
