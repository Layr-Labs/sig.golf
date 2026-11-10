import SigGolfCandidate.AllRouteAccounting
import SigGolfCandidate.Merge055
set_option debug.skipKernelTC false
namespace AllRouteQueryLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.T3 SigGolfCandidate.T3M
open ClaudeWCT.WCT9
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
 theorem pad64_aligned_local (y : HashInput) (hy : 0 < y.length) : Aligned (pad64 y) :=
  ⟨SigGolfCandidate.T3.Cost.pad64_positive y hy, SigGolfCandidate.T3.Cost.pad64_aligned y⟩
 theorem qLeaf_of_row (a : Digest) (lay : Layer) (tree leaf : Nat)
    (hl : leaf < 2^height lay) (hr : tree*2^height lay+leaf < 2^hyperW lay.val)
    (hi : BitVec 64) (rest : List UInt8) :
    qLeaf lay (toQ (pad64 (bytesLE 16 a ++ bytesLE 16 (hi ++ hyperWord lay.val (tree*2^height lay+leaf)) ++ rest))) = leaf := by
  apply qLeaf_of_header _ (pad64_aligned_local _ (by simp [bytesLE_length])) lay tree leaf hl hr hi
  unfold pad64
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a),
    List.take_left' (bytesLE_length 16 _)]
attribute [local irreducible] qLeaf toQ
 theorem qLeaf_encodingP (lay : Layer) (tree leaf : Nat)
    (hl : leaf < 2^height lay) (hr : tree*2^height lay+leaf < 2^hyperW lay.val)
    (M : LayerMsg) (c : BitVec 32) (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    qLeaf lay (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf M c pad padR hi))) = leaf := by
  cases M with
  | forest root =>
    simpa only [ClaudeWCT.W9.T3M.layerEncodingInputP, pairEncodingInputH, List.append_assoc] using
      qLeaf_of_row root lay tree leaf hl hr hi (bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 padR)
  | pair left right =>
    simpa only [ClaudeWCT.W9.T3M.layerEncodingInputP, pairEncodingInputH, List.append_assoc] using
      qLeaf_of_row left lay tree leaf hl hr hi (bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 right)
 theorem routed_bounds (index : Nat) (hindex : index < 2^31) (lay : Layer) :
    (route index lay).1 < 2^height lay ∧
      (route index lay).2 * 2^height lay + (route index lay).1 < 2^hyperW lay.val := by
  fin_cases lay <;> norm_num [route, height, hyperW] at * <;> omega
 theorem qLeaf_route_encodingP (index : Nat) (hindex : index < 2^31) (lay : Layer)
    (M : LayerMsg) (c : BitVec 32) (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    qLeaf lay (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2
      (route index lay).1 M c pad padR hi))) = (route index lay).1 :=
    qLeaf_encodingP lay _ _ (routed_bounds index hindex lay).1 (routed_bounds index hindex lay).2 M c pad padR hi
#print axioms qLeaf_route_encodingP
end AllRouteQueryLeaf

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open ClaudeWCT.WCT9
 theorem queryPathSave_lower_encodingP (index : Nat) (hindex : index < 2^31) (lay : Layer) (hl : lay ≠ 0)
    (M : LayerMsg) (c : BitVec 32) (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    queryPathSaveAllRoute lay (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2
      (route index lay).1 M c pad padR hi))) = SigGolfCandidate.AllRoute.usedSave lay.val (route index lay).1 := by
  rw [queryPathSaveAllRoute, if_neg hl, AllRouteQueryLeaf.qLeaf_route_encodingP index hindex lay M c pad padR hi]
#print axioms queryPathSave_lower_encodingP
end SigGolfCandidate.T3M.Verify
