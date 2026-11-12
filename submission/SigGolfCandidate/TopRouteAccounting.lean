import SigGolfCandidate.AllRouteAccounting
import SigGolfCandidate.Merge047
set_option debug.skipKernelTC false
namespace TopRouteQueryLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.T3 SigGolfCandidate.T3M
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
def qLeaf (q : Query) : Nat := readLE (((ofQ q).drop 16).take 16) / 2^16 % 4096
theorem qLeaf_of_header (input : List UInt8) (hi : Aligned input) (leaf : Nat) (hl : leaf<4096)
    (hp : BitVec 64) (hhdr : (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (hp ++ hyperWord 0 leaf)) :
    qLeaf (toQ input) = leaf := by
  unfold qLeaf
  rw [ofQ_toQ hi, hhdr, readLE_bytesLE]
  have hh : hyperHonest 0 leaf := by
    norm_num [hyperHonest, hyperW]
    omega
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (hyperWord 0 leaf).isLt, Nat.shiftLeft_eq]
  norm_num [hyperWord, hh, hyperW]
  omega
end TopRouteQueryLeaf
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open ClaudeWCT.WCT9
def queryPathSave (lay : Layer) (q : Query) : Nat :=
  if lay=0 then CanonicalPolicy.topPathSave (TopRouteQueryLeaf.qLeaf q) else 0
theorem queryPathSave_le (lay : Layer) (q : Query) : queryPathSave lay q ≤ 2 := by
  unfold queryPathSave CanonicalPolicy.topPathSave CanonicalPolicy.topPairSave
  split_ifs <;> omega
end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open ClaudeWCT.WCT9
 def queryPathSaveAllRoute (lay : Layer) (q : Query) : Nat :=
  if lay=0 then CanonicalPolicy.topPathSave (TopRouteQueryLeaf.qLeaf q)
  else SigGolfCandidate.AllRoute.usedSave lay.val (AllRouteQueryLeaf.qLeaf lay q)
 theorem queryPathSaveAllRoute_le (lay : Layer) (q : Query) : queryPathSaveAllRoute lay q ≤ 2 := by
  unfold queryPathSaveAllRoute
  split_ifs
  · unfold CanonicalPolicy.topPathSave CanonicalPolicy.topPairSave
    split_ifs <;> omega
  · exact SigGolfCandidate.AllRoute.usedSave_le_two _ _
end SigGolfCandidate.T3M.Verify
