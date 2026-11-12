import SigGolfCandidate.OuterGroundCore
import SigGolfCandidate.OuterTailPacket
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace OuterCarrierBits
open SigGolfCandidate.T3

def highByte (v : Digest) : BitVec 8 := v.extractLsb' 120 8

theorem highByte_lt (v : Digest) (b : Nat) (hb : b≤8) (hv : v.toNat<2^(128-b)) :
    (highByte v).toNat<2^(8-b) := by
  have hd : v.toNat/2^120<2^(8-b) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    rw [←pow_add]
    have he : 8-b+120=128-b := by omega
    simpa only [he] using hv
  simp only [highByte,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  exact lt_of_le_of_lt (Nat.mod_le _ _) hd

theorem and_clear (v : Digest) (b : Nat) (hb : b≤8) (hv : v.toNat<2^(128-b)) :
    highByte v &&& BitVec.ofNat 8 (2^(8-b)-1)=highByte v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  have hm : 2^(8-b)-1<2^8 := by
    have hp : 2^(8-b)≤2^8 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 0<2^(8-b) := by positivity
    omega
  rw [Nat.mod_eq_of_lt hm]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (highByte_lt v b hb hv)

theorem zeroOk_clear (coord : Nat) (v : Digest) (h : OuterGroundCore.zeroOk coord v=true) :
    highByte v &&& BitVec.ofNat 8 (2^(8-OuterGroundCore.width coord)-1)=highByte v := by
  have hw:=OuterGroundCore.width_bounds coord
  have hz : v.toNat/2^(128-OuterGroundCore.width coord)=0 := by simpa only [OuterGroundCore.zeroOk,beq_iff_eq] using h
  exact and_clear v _ (by omega) (Nat.lt_of_div_eq_zero (by positivity) hz)

def carrierBytes (a b c d e : Digest) : OuterTailPacket.Five :=
  ⟨highByte a,highByte b,highByte c,highByte d,highByte e⟩

theorem five_clear (a b c d e : Digest)
    (ha : OuterGroundCore.zeroOk 1 a=true) (hb : OuterGroundCore.zeroOk 3 b=true)
    (hc : OuterGroundCore.zeroOk 5 c=true) (hd : OuterGroundCore.zeroOk 7 d=true)
    (he : OuterGroundCore.zeroOk 8 e=true) :
    OuterTailPacket.clear (carrierBytes a b c d e)=carrierBytes a b c d e := by
  apply OuterTailPacket.Five.ext
  · simpa [carrierBytes,OuterTailPacket.clear,OuterGroundCore.width] using zeroOk_clear 1 a ha
  · simpa [carrierBytes,OuterTailPacket.clear,OuterGroundCore.width] using zeroOk_clear 3 b hb
  · simpa [carrierBytes,OuterTailPacket.clear,OuterGroundCore.width] using zeroOk_clear 5 c hc
  · simpa [carrierBytes,OuterTailPacket.clear,OuterGroundCore.width] using zeroOk_clear 7 d hd
  · simpa [carrierBytes,OuterTailPacket.clear,OuterGroundCore.width] using zeroOk_clear 8 e he

#print axioms five_clear
#print axioms zeroOk_clear
end OuterCarrierBits
