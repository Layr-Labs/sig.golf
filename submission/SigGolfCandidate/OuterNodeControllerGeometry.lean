import SigGolfCandidate.OuterNodeBufferGeometry
import SigGolfCandidate.Merge093
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterNodeControllerGeometry
open ClaudeWCT.W9.Machine.Expand.SharedScatter

theorem actual_frame (coord : Fin 9) : coordRegion coord.val=OuterNodeBufferGeometry.frameBase coord.val :=
  coordRegion_source coord

theorem b_geometry (coord : Fin 9) (child : Nat) :
    let A:=coordRegion coord.val+W9Drv.SharedBProof.blkO child 5
    let D:=coordRegion coord.val-W9Drv.SharedBProof.handO child
    2048≤A ∧ A<2^20 ∧ A%8=0 ∧ 2048≤D ∧ D<2^20 ∧ D%8=0 ∧ D+32≤A := by
  rw [actual_frame]
  exact OuterNodeBufferGeometry.b_geometry coord.val child coord.isLt

theorem c_geometry (coord : Fin 9) (child : Nat) :
    let A:=coordRegion coord.val+W9Drv.SharedCProof.blkO child 5
    let D:=coordRegion coord.val-W9Drv.SharedCProof.handO child
    2048≤A ∧ A<2^20 ∧ A%8=0 ∧ 2048≤D ∧ D<2^20 ∧ D%8=0 ∧ D+32≤A := by
  rw [actual_frame]
  exact OuterNodeBufferGeometry.c_geometry coord.val child coord.isLt

#print axioms b_geometry
#print axioms c_geometry
end OuterNodeControllerGeometry
