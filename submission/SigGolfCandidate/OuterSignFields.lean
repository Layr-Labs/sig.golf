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

/-- C46: bits 11..15 of a two-word FTS node word are `31 - coordinate / 2`. C47: `31 - ftsPair coordinate`. -/
theorem fts_field (coord index : Nat) (hc9 : coord<9) :
    (ftsNodeWord coord index <<< 48) >>> 59=BitVec.ofNat 64 (31-ftsPair coord) := by
  have h:=OuterHeaderFields.coordField coord index hc9
  have hp:=ftsPair_le coord
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat]
  have hw:=(ftsNodeWord coord index).isLt
  rw [Nat.mod_eq_of_lt (show 31-ftsPair coord<2^64 by omega)]
  rw [show 2^64=65536*2^48 from by decide,Nat.mul_mod_mul_right]
  rw [show 2^59=2048*2^48 from by decide,Nat.mul_div_mul_right _ _ (by positivity)]
  omega

/-- C47: the classifier's field test passes (`≥ 28`) on every coordinate (pairs 0..3). -/
theorem field_ge (coord index : Nat) (hc9 : coord<9) :
    ¬ ((ftsNodeWord coord index <<< 48) >>> 59).toNat<28 := by
  rw [fts_field coord index hc9,BitVec.toNat_ofNat]
  have h : ftsPair coord ≤ 3 := by unfold ftsPair; split_ifs <;> omega
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- C47: an FTS node word (low 16 bits `0xF800 - 2048 p ≠ 0`) is never the c8 heap-3 label `929 * 2^50`. -/
theorem ne_T4 (coord index : Nat) (hc9 : coord<9) : ftsNodeWord coord index≠1045961013456797696#64 := by
  intro he
  have h:=OuterHeaderFields.low16 coord index hc9
  have hp : ftsPair coord ≤ 3 := by unfold ftsPair; split_ifs <;> omega
  rw [he] at h
  change 1045961013456797696%65536=_ at h
  omega

#print axioms fts_low11
#print axioms fts_field
#print axioms field_ge
#print axioms ne_T4
end OuterSignFields
