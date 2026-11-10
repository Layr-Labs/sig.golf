import Mathlib.Data.BitVec
import Lean.Elab.Tactic.Omega
set_option debug.skipKernelTC true
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.OneRegisterMask
 theorem clear_nat (x : Nat) (hx : x < 2^64) :
    x &&& (2^64-2) = x/2*2 := by
  have hd := Nat.and_div_two (a:=x) (b:=2^64-2)
  have hl : x/2 < 2^63 := by omega
  have hb : (2^64-2)/2 = 2^63-1 := by decide
  rw [hb,Nat.and_two_pow_sub_one_of_lt_two_pow hl] at hd
  have hm := Nat.and_mod_two_pow (a:=x) (b:=2^64-2) (n:=1)
  simp only [Nat.reducePow,Nat.reduceSub,Nat.reduceMod,Nat.and_zero] at hm
  simp only [Nat.reducePow,Nat.reduceSub] at hd ⊢
  omega
 theorem clear_eq (x y : BitVec 64) (h:x.toNat/2=y.toNat/2) :
    x &&& (~~~1#64) = y &&& (~~~1#64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_not,BitVec.toNat_ofNat]
  change x.toNat &&& (2^64-2) = y.toNat &&& (2^64-2)
  rw [clear_nat _ x.isLt,clear_nat _ y.isLt,h]
 theorem masked_jump_general (a offset : BitVec 64) (m : Nat) (hm : m%2=0)
    (he : offset.toNat%2=0) :
    (((a &&& BitVec.ofNat 64 (m+1)) + offset) &&& (~~~1#64)) =
    (((a &&& BitVec.ofNat 64 m) + offset) &&& (~~~1#64)) := by
  apply clear_eq
  simp only [BitVec.toNat_add,BitVec.toNat_and,BitVec.toNat_ofNat]
  have hd := Nat.and_div_two (a:=a.toNat) (b:=(m+1)%2^64)
  have hd' := Nat.and_div_two (a:=a.toNat) (b:=m%2^64)
  have hq : ((m+1)%2^64)/2=(m%2^64)/2 := by omega
  rw [hq] at hd
  have hp := Nat.and_mod_two_pow (a:=a.toNat) (b:=m%2^64) (n:=1)
  have hp' : (m%2^64)%2=0 := by omega
  simp only [Nat.reducePow,hp',Nat.and_zero] at hp
  have hb := Nat.mod_lt a.toNat (by decide : 0<2)
  have hb' := Nat.mod_lt (a.toNat &&& ((m+1)%2^64)) (by decide : 0<2)
  omega
 theorem base_jump_general (a offset : BitVec 64) (m : Nat) (hm : m%2=0)
    (ha : a.toNat%2=0) (he : offset.toNat%2=0) :
    (((a + BitVec.ofNat 64 (m+1)) + offset) &&& (~~~1#64)) =
    (((a + BitVec.ofNat 64 m) + offset) &&& (~~~1#64)) := by
  apply clear_eq
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega
 theorem shifted_mask : ((523265 : BitVec 64) >>> 1) = ((523264 : BitVec 64) >>> 1) := by decide

theorem masked_jump_conditional (a offset : BitVec 64) (m : Nat) (hm : m%2=0)
    (he : offset.toNat%2=0) (p : Prop) [Decidable p] :
    (((a &&& BitVec.ofNat 64 (m + if p then 0 else 1)) + offset) &&& (~~~1#64)) =
    (((a &&& BitVec.ofNat 64 m) + offset) &&& (~~~1#64)) := by
  by_cases hp : p
  · simp [hp]
  · simpa only [if_neg hp] using masked_jump_general a offset m hm he

end SigGolfCandidate.T3M.OneRegisterMask
