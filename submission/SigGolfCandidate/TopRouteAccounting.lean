import SigGolfCandidate.Merge047
import SigGolfCandidate.LocalRouteAddress
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
theorem qLeaf_mod8_of_header (input : List UInt8) (hi : Aligned input)
    (lay : Layer) (routed : Nat) (hr : routed<2^hyperW lay.val) (hp : BitVec 64)
    (hhdr : (input.drop 16).take 16 = SphincsSecurity.bytesLE 16 (hp ++ hyperWord lay.val routed)) :
    qLeaf (toQ input)%8 = routed%8 := by
  unfold qLeaf
  rw [ofQ_toQ hi,hhdr,readLE_bytesLE]
  have hr32 : routed<2^32 := by
    fin_cases lay <;> norm_num [hyperW] at hr ⊢ <;> omega
  have hlay : lay.val<256 := by have := lay.isLt; omega
  have hh : hyperHonest lay.val routed := by
    simp only [hyperHonest,Nat.mod_eq_of_lt hlay,Nat.mod_eq_of_lt hr32]
    exact ⟨lay.isLt,hr⟩
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (hyperWord lay.val routed).isLt,Nat.shiftLeft_eq]
  simp only [hyperWord,if_pos hh,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hr32,Nat.mod_eq_of_lt hlay]
  fin_cases lay <;> norm_num [hyperW] at * <;> omega

end TopRouteQueryLeaf
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open ClaudeWCT.WCT9
def queryPathSave (lay : Layer) (q : Query) : Nat :=
  if lay=0 then CanonicalPolicy.topPathSave (TopRouteQueryLeaf.qLeaf q)
  else CanonicalPolicy.lowerPathSave lay.val (TopRouteQueryLeaf.qLeaf q)
theorem queryPathSave_le (lay : Layer) (q : Query) : queryPathSave lay q ≤ 2 := by
  unfold queryPathSave
  split_ifs
  · unfold CanonicalPolicy.topPathSave CanonicalPolicy.topPairSave
    split_ifs <;> omega
  · exact (CanonicalPolicy.lowerPathSave_le_one _ _).trans (by decide)

theorem queryPathSave_lower (lay : Layer) (q : Query) (hl : lay≠0) :
    queryPathSave lay q = CanonicalPolicy.lowerPathSave lay.val (TopRouteQueryLeaf.qLeaf q) := by
  simp only [queryPathSave,if_neg hl]
#print axioms queryPathSave_le
end SigGolfCandidate.T3M.Verify
