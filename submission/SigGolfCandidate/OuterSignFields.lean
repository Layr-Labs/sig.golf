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

/-- C31: a two-word FTS node word has zero low 11 bits. -/
theorem fts_low11 (coord index : Nat) (hc9 : coord<9) : ftsNodeWord coord index <<< 53=0#64 := by
  apply BitVec.eq_of_toNat_eq
  have h:=OuterHeaderFields.low11 coord index hc9
  have hw:=(ftsNodeWord coord index).isLt
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat]
  rw [show 2^64=2048*2^53 from by decide,Nat.mul_mod_mul_right]
  simp [h]

/-- C46: bits 11..15 of a two-word FTS node word are `31 - coordinate / 2`. -/
theorem fts_field (coord index : Nat) (hc9 : coord<9) :
    (ftsNodeWord coord index <<< 48) >>> 59=BitVec.ofNat 64 (31-coord/2) := by
  have h:=OuterHeaderFields.coordField coord index hc9
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat]
  have hw:=(ftsNodeWord coord index).isLt
  rw [Nat.mod_eq_of_lt (show 31-coord/2<2^64 by omega)]
  rw [show 2^64=65536*2^48 from by decide,Nat.mul_mod_mul_right]
  rw [show 2^59=2048*2^48 from by decide,Nat.mul_div_mul_right _ _ (by positivity)]
  omega

/-- C46: the classifier's coordinate field is 27 exactly for coordinate 8. -/
theorem coordinate (coord : Nat) (hc9 : coord<9) :
    BitVec.ofNat 64 (31-coord/2)=27#64 ↔ coord=8 := by
  constructor
  · intro he
    have hn:=congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hn
    change 31-coord/2=27 at hn
    omega
  · intro he
    subst he
    rfl

#print axioms fts_low11
#print axioms fts_field
#print axioms coordinate
end OuterSignFields
