import SigGolfCandidate.Merge091
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeBufferGeometry

def frameBase (coord : Nat) : Nat := 2904+W9Machine.V3.regionOffset coord

theorem frame_bounds (coord : Nat) (hc : coord<9) :
    2984≤frameBase coord ∧ frameBase coord≤9768 ∧ frameBase coord%8=0 := by
  unfold frameBase W9Machine.V3.regionOffset
  omega

theorem b_block (child : Nat) : W9Drv.SharedBProof.blkO child 5=784 := rfl
theorem c_block (child : Nat) : W9Drv.SharedCProof.blkO child 5=784 := rfl

theorem b_geometry (coord child : Nat) (hc : coord<9) :
    let A:=frameBase coord+W9Drv.SharedBProof.blkO child 5
    let D:=frameBase coord-W9Drv.SharedBProof.handO child
    2048≤A ∧ A<2^20 ∧ A%8=0 ∧ 2048≤D ∧ D<2^20 ∧ D%8=0 ∧ D+32≤A := by
  have hb:=frame_bounds coord hc
  simp only [b_block]
  unfold W9Drv.SharedBProof.handO
  split_ifs <;> omega

theorem c_geometry (coord child : Nat) (hc : coord<9) :
    let A:=frameBase coord+W9Drv.SharedCProof.blkO child 5
    let D:=frameBase coord-W9Drv.SharedCProof.handO child
    2048≤A ∧ A<2^20 ∧ A%8=0 ∧ 2048≤D ∧ D<2^20 ∧ D%8=0 ∧ D+32≤A := by
  have hb:=frame_bounds coord hc
  simp only [c_block]
  unfold W9Drv.SharedCProof.handO
  split_ifs <;> omega

#print axioms b_geometry
#print axioms c_geometry
end OuterNodeBufferGeometry
