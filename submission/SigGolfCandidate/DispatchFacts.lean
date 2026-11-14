import SigGolfCandidate.SimCore
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Rv

theorem r6_land_window (n s k : Nat) :
    n &&& (2^s*(2^k-1)) = 2^s*(n/2^s%2^k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : s ≤ j
  · simp only [h, decide_true, Bool.true_and, show j-s+s=j by omega]
    by_cases hj : j-s<k <;> simp [hj]
  · simp [h]

theorem r6_field_shl11 (W s : Nat) (hs : s≤11) :
    W*2^s%2^64/2048%256 = W/2^(11-s)%256 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256:Nat)=2^8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    show (2048:Nat)=2^11 by rfl, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j<8
  · simp only [hj, decide_true, Bool.true_and, show j+11<64 by omega, show s≤j+11 by omega]
    rw [show j+11-s=j+(11-s) by omega]
  · simp [hj]

def r6_shift11 (W : BitVec 64) (b : Nat) : BitVec 64 :=
  if b<11 then W<<<(11-b) else W>>>(b-11)

theorem r6_word_mask11 (W : BitVec 64) (b : Nat) :
    r6_shift11 W b &&& 522240#64 = BitVec.ofNat 64 (2048*(W.toNat/2^b%256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (522240#64).toNat=2^11*(2^8-1) by rfl, r6_land_window]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2048*(W.toNat/2^b%256)<2^64 by omega)]
  change 2048 * _ = 2048 * _
  apply congrArg (fun x => 2048*x)
  unfold r6_shift11
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change W.toNat*2^(11-b)%2^64/2048%256 = W.toNat/2^b%256
    rw [r6_field_shl11 _ _ (by omega), show 11-(11-b)=b by omega]
  · simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-11)*2^11=2^b by rw [←pow_add]; congr 1; omega]
    rfl

theorem r6_even_andNot1 (n : Nat) (h : n%2=0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j=0
  · subst h0
    simp
    rw [←BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0,hj]

theorem r6_high_byte (W : BitVec 64) :
    (W >>> 56) <<< 8 = BitVec.ofNat 64 (256*(W.toNat/2^56%256)) := by
  apply BitVec.eq_of_toNat_eq
  have hw := W.isLt
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

theorem r6_direct_target (raw col : Nat) (hr : 3≤raw) :
    (BitVec.ofNat 64 (2048*raw) + BitVec.ofNat 64 (2^64+4*col-2048)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*(512*(raw-3)+col)) := by
  rw [ofNat_add_ofNat, r6_even_andNot1 _ (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem r6_direct_wrapped (raw col : Nat) (hr : raw<3) (hc : col<512) :
    (BitVec.ofNat 64 (2048*raw) + BitVec.ofNat 64 (2^64+4*col-2048)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*(2^62+512*raw+col-1536)) := by
  rw [ofNat_add_ofNat, r6_even_andNot1 _ (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem r6_wrapped_fault (raw col : Nat) (hr : raw<3) (hc : col<512) :
    (BitVec.ofNat 64 (4096+4*(2^62+512*raw+col-1536))).toNat < 4096 ∨
      4096+4*257280 ≤ (BitVec.ofNat 64 (4096+4*(2^62+512*raw+col-1536))).toNat := by
  simp only [BitVec.toNat_ofNat]
  interval_cases raw <;> omega
end SigGolfCandidate.T3M.Nonbinary

