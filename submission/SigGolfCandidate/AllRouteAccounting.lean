import SigGolfCandidate.Merge047
import SigGolfCandidate.AllRouteSavings
set_option debug.skipKernelTC false
namespace AllRouteQueryLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.T3 SigGolfCandidate.T3M
open ClaudeWCT.WCT9
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
def qLeaf (lay : Layer) (q : Query) : Nat := readLE (((ofQ q).drop 16).take 16) / 2^16 % (2^height lay)
theorem qLeaf_of_header (input : List UInt8) (hi : Aligned input) (lay : Layer) (tree leaf : Nat)
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ hyperW lay.val)
    (hp : BitVec 64) (hhdr : (input.drop 16).take 16 =
      SphincsSecurity.bytesLE 16 (hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf))) :
    qLeaf lay (toQ input) = leaf := by
  unfold qLeaf
  rw [ofQ_toQ hi, hhdr, readLE_bytesLE]
  have hh : hyperHonest lay.val (tree * 2 ^ height lay + leaf) := by
    fin_cases lay <;> norm_num [hyperHonest, height, hyperW] at * <;> omega
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (hyperWord lay.val (tree * 2^height lay+leaf)).isLt,
    Nat.shiftLeft_eq]
  simp only [hyperWord, if_pos hh]
  fin_cases lay <;> norm_num [height, hyperW] at * <;> omega
end AllRouteQueryLeaf
#print axioms AllRouteQueryLeaf.qLeaf_of_header
