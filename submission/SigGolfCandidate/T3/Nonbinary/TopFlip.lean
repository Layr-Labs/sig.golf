import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3
theorem topMask_lt : topMask < 2 ^ 119 := by decide
theorem topFlip_topFlip (v : Digest) : topFlip (topFlip v) = v := by
  simp [topFlip]
theorem topFlip_injective : Function.Injective topFlip := fun a b h => by
  simpa [topFlip_topFlip] using congrArg topFlip h
def topFlipEquiv : Digest ≃ Digest := ⟨topFlip, topFlip, topFlip_topFlip, topFlip_topFlip⟩
theorem topCode_eq_xor (v : Digest) : topCode v = v.toNat ^^^ topMask := by
  simp [topCode, topFlip, BitVec.toNat_xor, topMask]
theorem topCode_topFlip (v : Digest) : topCode (topFlip v) = v.toNat := by
  rw [topCode, topFlip_topFlip]
theorem topCode_div_high (v : Digest) (n : Nat) (hn : 119 ≤ n) : topCode v / 2 ^ n = v.toNat / 2 ^ n := by
  rw [topCode_eq_xor, Nat.xor_div_two_pow,
    Nat.div_eq_of_lt (lt_of_lt_of_le topMask_lt (Nat.pow_le_pow_right (by decide) hn)), Nat.xor_zero]
theorem topCode_lt_iff (v : Digest) (n : Nat) (hn : 119 ≤ n) : topCode v < 2 ^ n ↔ v.toNat < 2 ^ n := by
  have h := topCode_div_high v n hn
  constructor <;> intro hh
  · have : topCode v / 2 ^ n = 0 := Nat.div_eq_of_lt hh
    rw [h] at this; exact (Nat.div_eq_zero_iff_lt (by positivity)).mp this
  · have : v.toNat / 2 ^ n = 0 := Nat.div_eq_of_lt hh
    rw [← h] at this; exact (Nat.div_eq_zero_iff_lt (by positivity)).mp this
theorem topFlip_toNat_lt (v : Digest) : (topFlip v).toNat < 2 ^ 125 ↔ v.toNat < 2 ^ 125 :=
  topCode_lt_iff v 125 (by decide)
end SigGolfCandidate.T3
