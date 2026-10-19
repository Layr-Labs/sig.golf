import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsLayout
import SigGolfCandidate.T3M_Verify_ChainSem
import SigGolfCandidate.T3M_Search_TopWindow
set_option Elab.async false

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem land_mask12 (n k : Nat) (hk : k≤7) :
    n &&& (4096*(2^k-1))=4096*(n/4096%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (4096 : Nat)=2^12 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 12≤j
  · simp only [h,decide_true,Bool.true_and,show j-12+12=j by omega]
    by_cases hj : j-12<k <;> simp [hj]
  · simp [h]
theorem field_shl12 (W s k : Nat) (hs : s≤12) (hk : k≤7) :
    W*2^s%2^64/4096%2^k=W/2^(12-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (4096 : Nat)=2^12 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+12<64 by omega,show s≤j+12 by omega]
    rw [show j+12-s=j+(12-s) by omega]
  · simp [hj]
def shiftWord12 (W : Word) (b : Nat) : Word := if b<12 then W<<<(12-b) else W>>>(b-12)
theorem word_mask12 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord12 W b &&& 520192#64=BitVec.ofNat 64 (4096*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 4096*x)
  unfold shiftWord12
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl12 _ _ _ (by omega) (by decide +kernel),show 12-(12-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-12)*4096=2^b by rw [show (4096 : Nat)=2^12 by rfl,←pow_add];congr 1;omega]
    rfl
theorem shift12_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift12 w b).eval s=shiftWord12 W b := by
  unfold shift12 shiftWord12
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 12-b<2^64 by omega),Nat.mod_eq_of_lt (show 12-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-12<2^64 by omega),Nat.mod_eq_of_lt (show b-12<64 by omega)]
theorem sub127_xor : ∀ f, f<128 → 127-f=127 ^^^ f := by decide +kernel
theorem not_field (X : Word) (b : Nat) (hb : b+7 ≤ 64) :
    (~~~X).toNat/2^b%128=127-X.toNat/2^b%128 := by
  rw [sub127_xor _ (Nat.mod_lt _ (by decide +kernel))]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, show (128:Nat)=2^7 by norm_num, show (127:Nat)=2^7-1 by norm_num,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]
  by_cases hj : j<7
  · simp [hj, show j+b<64 by omega]
  · simp [hj]
theorem entOff_le (q : Nat) (hq : q<17) : entOff q ≤ 1532 := by interval_cases q <;> decide +kernel
theorem entOff_ge (q : Nat) : 64 ≤ entOff q := by
  by_cases h : q<17
  · interval_cases q <;> decide +kernel
  · simp only [entOff, if_neg (show q≠0 by omega), if_neg (show q≠1 by omega),
      if_neg (show q≠2 by omega), if_neg (show q≠3 by omega), if_neg (show q≠4 by omega),
      if_neg (show q≠5 by omega), if_neg (show q≠6 by omega), if_neg (show q≠7 by omega),
      if_neg (show q≠8 by omega), if_neg (show q≠9 by omega), if_neg (show q≠10 by omega),
      if_neg (show q≠11 by omega), if_neg (show q≠12 by omega), if_neg (show q≠13 by omega),
      if_neg (show q≠14 by omega), if_neg (show q≠15 by omega)]
    decide +kernel
theorem dispatch_value (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord12 W b &&& 520192#64)+BitVec.ofNat 64 (2^64+4*entOff q-4096)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat/2^b%128)+2^64+4*entOff q-4096) := by
  have he := entOff_le q hq
  rw [word_mask12 W b hb,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  apply congrArg (BitVec.ofNat 64); omega
theorem cell_value (q k : Nat) (hq : q<17) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)=pcOf (cellW q k) := by
  have he := entOff_le q hq
  unfold pcOf cellW; rw [if_pos hq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault125_value (q : Nat) (hq : q<17) :
    BitVec.ofNat 64 (4096*(127-125)+2^64+4*entOff q-4096)=pcOf (entOff q) := by
  have he := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault_value (q k : Nat) (hq : q<17) (hk : 127 ≤ k) (hk' : k<128) :
    (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat<0x1000 ∨
      0x1000+4*257280 ≤ (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat := by
  have he := entOff_le q hq
  have hl := entOff_ge q
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_value (q : Nat) (hq : q<17) (he : 1024≤entOff q) :
    BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)=pcOf (entOff q-1024) := by
  have hu := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_low (q : Nat) (he : entOff q<1024) :
    (BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)).toNat<0x1000 := by
  simp only [BitVec.toNat_ofNat]
  omega
theorem g9_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64)+256#64) &&& ~~~1#64 =
      BitVec.ofNat 64 (8192*(W.toNat%64)+256) := by
  have hm : ((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64) = BitVec.ofNat 64 (8192*(W.toNat%64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hw := W.isLt
    rw [show (13 : Nat) % 2^64 = 13 by rfl]
    rw [Nat.mod_eq_of_lt (show 8192*(W.toNat%64) < 2^64 by omega)]
    have : W.toNat*2^13%2^64/4096%2^7 = 2*(W.toNat%64) := by
      rw [show (2:Nat)^64 = 2^13*2^51 by norm_num, Nat.mul_comm, Nat.mul_mod_mul_left,
        show (2:Nat)^13*(W.toNat%2^51) = 4096*(2*(W.toNat%2^51)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
    rw [this]; ring
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
theorem g9_cell (u : Nat) (hu : u ≤ 62) : BitVec.ofNat 64 (8192*(63-u)+256)=pcOf (cellW 9 (2*u)) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
theorem g9_fault : (BitVec.ofNat 64 (8192*(63-63)+256)).toNat<0x1000 := by decide +kernel
theorem prologue_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 12).toNat) &&& 520192#64)+BitVec.ofNat 64 (1168)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat%128)+1168) := by
  have hm := word_mask12 W 0 (by decide +kernel)
  simp only [shiftWord12, show (0 : Nat) < 12 from by omega, if_true,
    Nat.sub_zero, Nat.pow_zero, Nat.div_one] at hm
  change ((W <<< 12 &&& 520192#64) + BitVec.ofNat 64 (1168)) &&& ~~~1#64 = _
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
end SigGolfCandidate.T3M.Nonbinary
