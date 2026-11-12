import SigGolfCandidate.OuterSignHeapSource
import SigGolfCandidate.OuterSignCoordinate
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignCoordinateSource
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate

theorem build_expand (first : Bool) (index c : Nat) (selected : WCT9.Child) (word : WCT9.Rank) (pads : Nat→SharedForest.PairRoot) :
    OuterForestBudget.buildCoord first index c selected word pads=(do
      let state←OuterCoordinate.prelude first index c selected word pads
      let nodes←if first then OuterInnerMoment.innerHeap true index c pads state.1 else OuterHeapMoment.heap c index pads state.1
      pure (nodes,state.2)) := by
  cases first <;> rfl

#check build_expand

theorem source (c index : Nat) (hc:c<9) (selected : WCT9.Child) (word : WCT9.Rank) (pads : Nat→SharedForest.PairRoot) :
    OuterSignCoordinate.program index c selected.val word (fun j=>(pads (j/64)).1) (rightPads pads)=
      OuterForestBudget.buildCoord (SharedLeaf.first c) index c selected word pads := by
  conv_rhs => rw [build_expand]
  unfold OuterSignCoordinate.program OuterSignCoordinate.rowsHeap OuterCoordinate.prelude OuterCoordinate.children
  simp only [bind_assoc]
  apply bind_congr
  intro coefs
  have hraw : SharedNext.raw c=SharedForest.rawChild (SharedLeaf.first c) := rfl
  simp only [SharedLeaves.leafRows,hraw]
  apply bind_congr
  intro rows
  rw [OuterSignHeapSource.heap c index hc]
  split_ifs <;> rfl
#print axioms source
end OuterSignCoordinateSource
