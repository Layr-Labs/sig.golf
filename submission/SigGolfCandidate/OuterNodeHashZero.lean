import SigGolfCandidate.OuterGroundCore
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeHashZero
open SigGolfCandidate.T3 OuterGroundCore

theorem upper_word_iff (v : BitVec 128) (b : Nat) (hb : b≤64) :
    (v.extractLsb' 64 64 >>> (64-b))=0#64 ↔ v.toNat/2^(128-b)=0 := by
  have hq : v.toNat/2^64<2^64 := by have h:=v.isLt;omega
  have he : (v.extractLsb' 64 64 >>> (64-b)).toNat=v.toNat/2^(128-b) := by
    simp only [BitVec.extractLsb',BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hq,Nat.div_div_eq_div_mul,←Nat.pow_add]
    congr 2
    omega
  constructor
  · intro h
    have hz : (v.extractLsb' 64 64 >>> (64-b)).toNat=0 := congrArg BitVec.toNat h
    rw [he] at hz
    exact hz
  · intro h
    apply BitVec.eq_of_toNat_eq
    change (v.extractLsb' 64 64 >>> (64-b)).toNat=0
    rw [he]
    exact h

theorem high_word (a : HashOutput) : (a.extractLsb' 128 128).extractLsb' 64 64=a.extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_extractLsb',hi,show 64+i<128 by omega,Nat.add_assoc]
  congr 1
  omega

theorem low_word (a : HashOutput) : (a.extractLsb' 0 128).extractLsb' 64 64=a.extractLsb' 64 64 :=
  BitVec.extractLsb'_extractLsb'_of_le (by decide)

theorem b_zero (a : HashOutput) (coord heap : Nat) (hc : coord≠8) :
    zeroOk coord (value coord heap a)=true ↔ (a.extractLsb' 192 64 >>> 61)=0 := by
  have h:=upper_word_iff (a.extractLsb' 128 128) 3 (by decide)
  simpa [zeroOk,value,offset,OuterGroundCore.width,hc,high_word] using h.symm

theorem c_two_zero (a : HashOutput) :
    zeroOk 8 (value 8 2 a)=true ↔ (a.extractLsb' 192 64 >>> 60)=0 := by
  have h:=upper_word_iff (a.extractLsb' 128 128) 4 (by decide)
  simpa [zeroOk,value,offset,OuterGroundCore.width,high_word] using h.symm

theorem c_three_zero (a : HashOutput) :
    zeroOk 8 (value 8 3 a)=true ↔ (a.extractLsb' 64 64 >>> 60)=0 := by
  have h:=upper_word_iff (a.extractLsb' 0 128) 4 (by decide)
  simpa [zeroOk,value,offset,OuterGroundCore.width,low_word] using h.symm

#print axioms b_zero
#print axioms c_three_zero
end OuterNodeHashZero
