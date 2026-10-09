import SigGolfCandidate.Legacy
set_option autoImplicit false
namespace SigGolfCandidate.Research.V7Composed198Gate
theorem even_gate (g : Nat) : g / 2 < 1182 ↔ g < 2364 := by omega

theorem gate_shift44_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 44).toNat =
      (answer.toNat / 2^235 % 2^21) / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem gate_ult_shift44 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 44) 1182#64 =
      decide (answer.toNat / 2^235 % 2^21 < 2364) := by
  simp only [BitVec.ult, gate_shift44_toNat, show (1182#64 : BitVec 64).toNat = 1182 from rfl,
    even_gate]

/-- T8E gate (14 bits at 242, limit 1451): the top 14 bits of the last 64-bit digest word. -/
theorem gate_shift50_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 50).toNat = answer.toNat / 2^242 % 2^14 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h := BitVec.isLt answer
  omega

theorem gate_ult_shift50 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 50) 1451#64 =
      decide (answer.toNat / 2^242 % 2^14 < 1451) := by
  simp only [BitVec.ult, gate_shift50_toNat, show (1451#64 : BitVec 64).toNat = 1451 from rfl]

end SigGolfCandidate.Research.V7Composed198Gate
