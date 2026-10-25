import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsLayout
import SigGolfCandidate.T3M_Verify_ChainSem
import SigGolfCandidate.T3M_Search_TopWindow

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
/-- T51: #938's r5 groups 9..15 keep their cell column `1024 (125 - k) + entOff q`. -/
theorem cell_value (q k : Nat) (hq : q<16) (h9 : 9≤q) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)=pcOf (cellW q k) := by
  have he := entOff_le q (by omega)
  unfold pcOf cellW; rw [if_neg (by omega), if_pos hq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
/-- T51: the r7 pair (group 16) is reached by #938's dispatch into group 8 (`entOff 8 = 676`): rank `k < 49` lands
on its cell `cellW 16 k = 1024 (125 - k) + 676`. -/
theorem cell_value_pair (k : Nat) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff 8-4096)=pcOf (cellW 16 k) := by
  unfold pcOf cellW entOff
  simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]
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
/-! ### T51 dispatch arithmetic (ported from R6)
g0 (prologue): `slli a4,a6,56; srli a4,a4,45; jalr -744(a4)` lands on `cell6 0 raw` (raw = a6 % 256 >= 3), below the
code start (raw = 1, 2) or far above it (raw = 0).  r6 groups 1..8: `a4 = field & 0xFF00 = 256 raw`, table B
(g1..g3, g8) `s2 - a4`, table A `a4 + s2`, `jalr` to `cell6 h raw`.  Checksum: `((s8 + 89) << 11) + 1168` with
`s8 = T - ds` (T = 152, ds <= 231) lands on `ckWord ds`. -/
/-- The g0 dispatch shift pair `slli a4,a6,56; srli a4,a4,45`: `2048 * (a6 % 256)`. -/
theorem g0_shift (W : Word) : (W <<< 56) >>> 45 = BitVec.ofNat 64 (2048 * (W.toNat % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have hW := W.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2048 * (W.toNat % 256) < 2^64 by omega)]
  rw [show (2:Nat)^64 = 2^56 * 2^8 by norm_num, Nat.mul_comm W.toNat, Nat.mul_mod_mul_left,
    show (2:Nat)^56 = 2^45 * 2048 by norm_num, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  norm_num
/-- The g0 dispatch target (jalr -744) for a field value `raw >= 1`. -/
theorem g0_target (W : Word) (raw : Nat) (hr : W.toNat % 256 = raw) (h1 : 1 ≤ raw) :
    (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64 = BitVec.ofNat 64 (2048 * raw - 744) := by
  have hr' : raw < 256 := by omega
  have e : BitVec.ofNat 64 (2048 * raw) + BitVec.ofNat 64 (2^64-744) = BitVec.ofNat 64 (2048 * raw - 744) := by
    rw [ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [g0_shift, hr, e, even_andNot1' _ (by omega)]
theorem g0_cell (raw : Nat) (h3 : 3 ≤ raw) : BitVec.ofNat 64 (2048 * raw - 744) = pcOf (cell6 0 raw) := by
  unfold pcOf cell6; simp only [if_true]; congr 1; omega
theorem g0_low (raw : Nat) (h3 : raw < 3) : (BitVec.ofNat 64 (2048 * raw - 744)).toNat < 0x1000 := by
  simp only [BitVec.toNat_ofNat]; omega
/-- Field value 0: the target `2^64 - 744` lies far above the code. -/
theorem g0_target0 (W : Word) (hr : W.toNat % 256 = 0) :
    0x1000 + 4 * 257280 ≤ ((((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64).toNat := by
  rw [g0_shift, hr, Nat.mul_zero, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  simp only [BitVec.toNat_ofNat]; omega
theorem land_mask8 (n : Nat) : n &&& (256*(2^8-1)) = 256*(n/256%2^8) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (256 : Nat)=2^8 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : 8 ≤ j
  · simp only [h, decide_true, Bool.true_and, show j-8+8=j by omega]
    by_cases hj : j-8<8 <;> simp [hj]
  · simp [h]
/-- `X &&& 0xFF00 = 256 * (X / 2^8 % 256)`. -/
theorem word_ff00 (X : Word) : X &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^8 % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : X.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [BitVec.toNat_and, show (65280#64).toNat = 256*(2^8-1) by rfl, land_mask8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 256 * (X.toNat / 2^8 % 256)) (by omega)]
  norm_num
/-- `(X >>> s) &&& 0xFF00 = 256 * (X / 2^(s+8) % 256)`. -/
theorem field_ff00 (X : Word) (s : Nat) :
    (X >>> s) &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^(s+8) % 256)) := by
  rw [word_ff00, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
theorem s2_sub (r : Nat) (hr : r < 256) :
    856064#64 - BitVec.ofNat 64 (256*r) = BitVec.ofNat 64 (856064-256*r) := by
  rw [BitVec.sub_eq_iff_eq_add, ofNat_add_ofNat]
  congr 1; omega
/-- Table B target (r6 groups 1..3): `s2 - 256 raw + (4 off - 256)`. -/
theorem tabB_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((856064#64 - BitVec.ofNat 64 (256*r)) + BitVec.ofNat 64 (2^64+4*o-256)) &&& ~~~1#64 =
      pcOf (64*(3327-r)+o) := by
  rw [s2_sub r hr, ofNat_add_ofNat]
  have e : BitVec.ofNat 64 (856064-256*r+(2^64+4*o-256)) = BitVec.ofNat 64 (856064-256*r+4*o-256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [e, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
/-- Table A target (r6 groups 4..7): `256 raw + s2 + 4 off`. -/
theorem tabA_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((BitVec.ofNat 64 (256*r) + 856064#64) + BitVec.ofNat 64 (4*o)) &&& ~~~1#64 =
      pcOf (64*(3328+r)+o) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
theorem ck_s8 (ds : Nat) (hd : ds ≤ 231) :
    (BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64 = BitVec.ofNat 64 (241-ds) := by
  rw [BitVec.ofNat_sub_ofNat, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [topT, BitVec.toNat_ofNat]
  omega
/-- The checksum dispatch target `(((s8 + 89) << 11) + 1168) & ~1` for s8 = T - ds, ds <= 231. -/
theorem ck_target (ds : Nat) (hd : ds ≤ 231) :
    ((((BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64) <<< 11) + 1168#64) &&& ~~~1#64 =
      pcOf (ckWord ds) := by
  have e2 : BitVec.ofNat 64 (241-ds) <<< 11 = BitVec.ofNat 64 (2048*(241-ds)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  rw [ck_s8 ds hd, e2, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf ckWord topT; congr 1; omega
/-- The r6 field read by the dispatch into group `h` (1..8): bits `8h..8h+7` (h < 7), `112..119` (g7),
`120..127` (g8) (`= T3.r6Shift h`). -/
def r6Pos (h : Nat) : Nat := if h=7 then 112 else if h=8 then 120 else 8*h
theorem cell6_tab (h r : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) :
    cell6 h r = if r6B h then 64*(3327-r)+r6Off h else 64*(3328+r)+r6Off h := by
  unfold cell6; rw [if_neg (by omega)]
theorem r6Off_lt (h : Nat) : r6Off h < 64 := by unfold r6Off; omega
end SigGolfCandidate.T3M.Nonbinary
