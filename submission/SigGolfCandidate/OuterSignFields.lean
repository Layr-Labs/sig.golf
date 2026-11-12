import SigGolfCandidate.OuterNodeRecordHeader
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem low16 (w : BitVec 64) : (w <<< 48) >>> 48=BitVec.ofNat 64 (w.toNat%65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat]
  rw [show 2^64=65536*2^48 from by decide,Nat.mul_mod_mul_right]
  omega

theorem fts_tag (coord index : Nat) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) :
    ((ftsNodeWord coord index <<< 48) >>> 48)=63488#64 := by
  rw [low16,OuterHeaderFields.low16 coord index hc hc9 hi]

theorem coordinate (coord index : Nat) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) :
    ((ftsNodeWord coord index >>> 16) &&& 15#64)=7#64 ↔ coord=8 := by
  have h:=OuterNodeRecordHeader.nibble coord index hc hc9 hi
  constructor
  · intro he
    have hn:=congrArg BitVec.toNat he
    rw [h] at hn
    change coord-1=7 at hn
    omega
  · intro he
    apply BitVec.eq_of_toNat_eq
    rw [h,he]
    rfl

#print axioms fts_tag
#print axioms coordinate
end OuterSignFields
