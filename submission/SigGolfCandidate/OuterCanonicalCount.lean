import SigGolfCandidate.OuterCanonicalWorld
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalCount
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure)
open ClaudeWCT.W9.T3.Security.WPair.Counted (queried_length_ftsCoefs queried_length_free)
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.WPair ClaudeWCT.W9.T3.Security.WPair.Paired
open OuterCanonicalWorld
theorem coordinate_count (A : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    (SourceReplay.queried A (OuterCanonicalModel.coordinate first index coord selected word pads)).length =
      21 + (3200 + ((SourceReplay.queried A (OuterCanonicalModel.heap first index coord pads
        (sharedLeaves A first index coord pads))).length + 0)) := by
  rw [OuterCanonicalModel.coordinate, queried_length_bind, queried_length_ftsCoefs, queried_length_bind,
    queried_length_sharedRows, eval_ftsCoefs, sharedRows_roots_eq, queried_length_bind, queried_length_pure]

variable {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs ⊆ U) (omega : ClaudeWCT.W9.CanonTable.Omega U)

theorem coordinate_world (hidden hidden' : ClaudeWCT.W9.CanonTable.HiddenF) (first : Bool)
    (index : Nat) (hindex : index < 2 ^ 31) (coord : Nat) (hcoord : coord < 9) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) :
    (SourceReplay.queried (wA hU omega hidden) (OuterCanonicalModel.coordinate first index coord selected word pads)).length =
      (SourceReplay.queried (wA hU omega hidden') (OuterCanonicalModel.coordinate first index coord selected word pads)).length := by
  have hl := sharedLeaves_world hU omega hidden hidden' first index hindex ⟨coord, hcoord⟩ pads
  simp only at hl
  rw [coordinate_count, coordinate_count, hl,
    queried_length_free hU omega hidden hidden' (heap_free _ _ _ _ _)]


#print axioms coordinate_world
end OuterCanonicalCount
