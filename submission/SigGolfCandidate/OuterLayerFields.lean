import SigGolfCandidate.OuterSignLayers
import SigGolfCandidate.OuterSerializeWords
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterLayerFields
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign.SharedSearches
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
theorem completed_layer_fields {index : Nat} {p : PreparedRoots} {a : OuterSignSearchSource.Choices} {top : SigGolfCandidate.T3.Pieces}
    {s : MachineState} (h : OuterSignSearchSource.Completed index p a top s) : LayerFields s (OuterSignSearchSource.layersValue index p a top).pieces := by
  intro lay
  fin_cases lay
  · constructor
    · intro i hi
      simpa [OuterSignSearchSource.layersValue,SigGolfCandidate.T3M.layIdx,Nat.mul_add,←Nat.add_assoc] using h.topValues i hi
    · intro j hj
      simpa [OuterSignSearchSource.layersValue,SigGolfCandidate.T3M.layIdx,chainCount,Nat.mul_add,←Nat.add_assoc] using h.topPath j hj
  · exact stored_layer_fields (by decide) (prepared_length 1 (by decide) _ _ _).1
      (prepared_length 1 (by decide) _ _ _).2 h.one
  · exact stored_layer_fields (by decide) (prepared_length 2 (by decide) _ _ _).1
      (prepared_length 2 (by decide) _ _ _).2 h.two
  · exact stored_layer_fields (by decide) (prepared_length 3 (by decide) _ _ _).1
      (prepared_length 3 (by decide) _ _ _).2 h.three


#print axioms completed_layer_fields
end OuterLayerFields
