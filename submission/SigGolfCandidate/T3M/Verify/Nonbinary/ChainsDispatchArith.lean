import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout
import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.T3M.Search.TopWindow

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem land_mask10 (n k : Nat) (hk : k≤7) :
    n &&& (1024*(2^k-1))=1024*(n/1024%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (1024 : Nat)=2^10 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 10≤j
  · simp only [h,decide_true,Bool.true_and,show j-10+10=j by omega]
    by_cases hj : j-10<k <;> simp [hj]
  · simp [h]
theorem field_shl10 (W s k : Nat) (hs : s≤10) (hk : k≤7) :
    W*2^s%2^64/1024%2^k=W/2^(10-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (1024 : Nat)=2^10 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+10<64 by omega,show s≤j+10 by omega]
    rw [show j+10-s=j+(10-s) by omega]
  · simp [hj]
def shiftWord10 (W : Word) (b : Nat) : Word := if b<10 then W<<<(10-b) else W>>>(b-10)
theorem word_mask10 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord10 W b &&& 130048#64=BitVec.ofNat 64 (1024*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide +kernel)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 1024*x)
  unfold shiftWord10
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl10 _ _ _ (by omega) (by decide +kernel),show 10-(10-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-10)*1024=2^b by rw [show (1024 : Nat)=2^10 by rfl,←pow_add];congr 1;omega]
    rfl
theorem shift10_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift10 w b).eval s=shiftWord10 W b := by
  unfold shift10 shiftWord10
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega),Nat.mod_eq_of_lt (show 10-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega),Nat.mod_eq_of_lt (show b-10<64 by omega)]
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
theorem entOff_le (q : Nat) (hq : q<17) : entOff q ≤ 211 := by unfold entOff; split_ifs <;> omega
theorem dispatch_value (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord10 W b &&& 130048#64)+BitVec.ofNat 64 (1024+4*entOff q)) &&& ~~~1#64 =
      BitVec.ofNat 64 (1024*(W.toNat/2^b%128)+1024+4*entOff q) := by
  have he := entOff_le q hq
  rw [word_mask10 W b hb,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  congr 1; omega
theorem cell_value (q k : Nat) (hq : q<17) (h8 : q≠8) (hk : k ≤ 124) :
    BitVec.ofNat 64 (1024*(127-k)+1024+4*entOff q)=pcOf (cellW q k) := by
  unfold pcOf cellW; rw [if_neg h8, if_pos hq]; congr 1; omega
theorem fault_value (q k : Nat) (hq : q<17) (hk : 125 ≤ k) (hk' : k<128) :
    (BitVec.ofNat 64 (1024*(127-k)+1024+4*entOff q)).toNat<0x1000 := by
  have he := entOff_le q hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
theorem g9_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 11).toNat) &&& 130048#64)+2300#64) &&& ~~~1#64 =
      BitVec.ofNat 64 (2048*(W.toNat%64)+2300) := by
  have hm : ((W <<< (BitVec.ofNat 64 11).toNat) &&& 130048#64) = BitVec.ofNat 64 (2048*(W.toNat%64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide +kernel)]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hw := W.isLt
    rw [show (11 : Nat) % 2^64 = 11 by rfl]
    rw [Nat.mod_eq_of_lt (show 2048*(W.toNat%64) < 2^64 by omega)]
    have : W.toNat*2^11%2^64/1024%2^7 = 2*(W.toNat%64) := by
      rw [show (2:Nat)^64 = 2^11*2^53 by norm_num, Nat.mul_comm, Nat.mul_mod_mul_left,
        show (2:Nat)^11*(W.toNat%2^53) = 1024*(2*(W.toNat%2^53)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
    rw [this]; ring
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
/-- BIG74: `g9_value` with the jalr constant of a group-8 inline slot (2304 or 1276). -/
theorem g9_valueC (W : Word) (C : Nat) (hC : C%2=0) :
    (((W <<< (BitVec.ofNat 64 11).toNat) &&& 130048#64)+BitVec.ofNat 64 C) &&& ~~~1#64 =
      BitVec.ofNat 64 (2048*(W.toNat%64)+C) := by
  have hm : ((W <<< (BitVec.ofNat 64 11).toNat) &&& 130048#64) = BitVec.ofNat 64 (2048*(W.toNat%64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (130048#64).toNat=1024*(2^7-1) by rfl,land_mask10 _ _ (by decide +kernel)]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hw := W.isLt
    rw [show (11 : Nat) % 2^64 = 11 by rfl]
    rw [Nat.mod_eq_of_lt (show 2048*(W.toNat%64) < 2^64 by omega)]
    have : W.toNat*2^11%2^64/1024%2^7 = 2*(W.toNat%64) := by
      rw [show (2:Nat)^64 = 2^11*2^53 by norm_num, Nat.mul_comm, Nat.mul_mod_mul_left,
        show (2:Nat)^11*(W.toNat%2^53) = 1024*(2*(W.toNat%2^53)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
    rw [this]; ring
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
/-- BIG74: the q8 -> q9 targets: b63 = 0 lands after the `bge` of the even cell, b63 = 1 on the odd cell. -/
theorem g9_even (u : Nat) (hu : u ≤ 62) : BitVec.ofNat 64 (2048*(63-u)+2304)=pcOf (cellW 9 (2*u)+1) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
theorem g9_odd (u : Nat) (hu : u ≤ 61) : BitVec.ofNat 64 (2048*(63-u)+1276)=pcOf (cellW 9 (1+2*u)) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
/-- BIG74: the q7 -> q8 dispatch `srli a4,a6,56; addi a4,a4,1735; slli a4,a4,9; jalr 200(a4)` on `a6 = ~X`. -/
theorem disp8_value (X : Word) :
    (((((~~~X) >>> ((BitVec.ofNat 64 56 : Word).toNat % 64))+BitVec.ofNat 64 1735) <<<
      ((BitVec.ofNat 64 9 : Word).toNat % 64))+BitVec.ofNat 64 200) &&& ~~~1#64 =
      BitVec.ofNat 64 (512*(255-X.toNat/2^56)+888520) := by
  rw [show (BitVec.ofNat 64 56 : Word).toNat % 64 = 56 from rfl, show (BitVec.ofNat 64 9 : Word).toNat % 64 = 9 from rfl]
  have hx := X.isLt
  have h1 : (~~~X) >>> 56 = BitVec.ofNat 64 (255-X.toNat/2^56) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_not, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega
  rw [h1, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  congr 1
  omega
theorem g9_cell (u : Nat) (hu : u ≤ 62) : BitVec.ofNat 64 (2048*(63-u)+2300)=pcOf (cellW 9 (2*u)) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
theorem g9_fault : (BitVec.ofNat 64 (2048*(63-63)+2300)).toNat<0x1000 := by decide +kernel
theorem prologue_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 10).toNat) &&& 130048#64)+BitVec.ofNat 64 1060) &&& ~~~1#64 =
      BitVec.ofNat 64 (1024*(W.toNat%128)+1060) := by
  have hm := word_mask10 W 0 (by decide +kernel)
  simp only [shiftWord10, show (0 : Nat) < 10 from by omega, if_true,
    Nat.sub_zero, Nat.pow_zero, Nat.div_one] at hm
  change ((W <<< 10 &&& 130048#64) + 1060#64) &&& ~~~1#64 = _
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
end SigGolfCandidate.T3M.Nonbinary
