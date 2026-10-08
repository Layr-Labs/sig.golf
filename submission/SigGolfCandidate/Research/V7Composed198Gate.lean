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

theorem gate_ult_const (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64) 0x0049e00000000000#64 =
      decide (answer.toNat / 2^235 % 2^21 < 2364) := by
  rw [← gate_ult_shift44]
  simp only [BitVec.ult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0x0049e00000000000#64 : BitVec 64).toNat = 20793963904499712 from rfl,
    show (1182#64 : BitVec 64).toNat = 1182 from rfl, decide_eq_decide]
  omega

end SigGolfCandidate.Research.V7Composed198Gate
