import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePass
import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodecC

/-! # DEC at signature level

If the 5,195-byte signature `b` sits at `0x7000` (`SigMem`), DEC's accumulator is the codec's `xOfB b`, the hint it
stores is `(sigDecC b).policyHints`, and its output slots are the inflated layout
`SharedCodec.inflatedRead 0 (SharedCodec.digC b)`. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3 (topZeroBits topZeroAlloc)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The DEC entry memory holds the 5,195-byte signature at `0x7000` (649 full dwords + 3 tail bytes). -/
structure SigMem (M : Word → Word) (b : SharedCodec.CBytes) : Prop where
  word : ∀ j, j < 649 → M (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64
  tail : (M (BitVec.ofNat 64 0x8448)).toNat % 2 ^ 24 = b.toNat / 2 ^ (64 * 649) % 2 ^ 24

theorem cDig_word (b : SharedCodec.CBytes) (c w : Nat) (hw : w < 2) :
    (SharedCodec.cDig b c).extractLsb' (64 * w) 64 = b.extractLsb' (64 * (2 * c + w)) 64 := by
  unfold SharedCodec.cDig
  rw [SharedCodec.extract_digest_word b (128 * c) w hw]
  congr 1
  omega

theorem slot_word {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (c w : Nat) (hc : c < 324)
    (hw : w < 2) : M (slotA c w) = (SharedCodec.cDig b c).extractLsb' (64 * w) 64 := by
  rw [cDig_word b c w hw, ← h.word (2 * c + w) (by omega)]
  unfold slotA
  congr 2
  omega

theorem topBits_cDig (b : SharedCodec.CBytes) (c n : Nat) (hn : n ≤ 64) :
    SharedCodec.topBits n (SharedCodec.cDig b c) = (b.extractLsb' (64 * (2 * c + 1)) 64).toNat / 2 ^ (64 - n) := by
  unfold SharedCodec.topBits SharedCodec.cDig
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  generalize b.toNat = x
  rw [show 64 * (2 * c + 1) = 128 * c + 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ (128 * c) = y
  rw [show 128 - n = 64 + (64 - n) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]

theorem aH_word {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (j : Nat) (hj : j ≤ 10) :
    M (aH j) = b.extractLsb' (64 * (2 * (165 + j) + 1)) 64 := by
  rw [← h.word _ (by omega)]
  unfold aH pH
  congr 2
  omega

theorem xD_xOfB {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    (xD M).toNat = SharedCodec.xOfB b := by
  rw [xD_toNat]
  unfold xN SharedCodec.xOfB
  rw [topBits_cDig b 168 1 (by omega), topBits_cDig b 169 1 (by omega), topBits_cDig b 170 2 (by omega),
    topBits_cDig b 171 3 (by omega), topBits_cDig b 172 4 (by omega), topBits_cDig b 173 5 (by omega),
    topBits_cDig b 174 6 (by omega), topBits_cDig b 175 7 (by omega),
    aH_word h 3 (by omega), aH_word h 4 (by omega), aH_word h 5 (by omega), aH_word h 6 (by omega),
    aH_word h 7 (by omega), aH_word h 8 (by omega), aH_word h 9 (by omega), aH_word h 10 (by omega)]

theorem hint_toNat {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    (xD M >>> 16).toNat = (SharedCodec.sigDecC b).policyHints.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, xD_xOfB h]
  show _ = (BitVec.ofNat 16 (SharedCodec.xOfB b / 2 ^ 16)).toNat
  have := SharedCodec.xOfB_lt b
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem hint_eq {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    xD M >>> 16 = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := ((SharedCodec.sigDecC b).policyHints).isLt
  rw [hint_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem clearTop_lo (t : Nat) (ht : t ≤ 64) (d : SigGolfCandidate.T3.Digest) :
    (SharedCodec.clearTop t d).extractLsb' (64 * 0) 64 = d.extractLsb' (64 * 0) 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold SharedCodec.clearTop
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.shiftRight_zero]
  rw [Nat.mod_eq_of_lt (show d.toNat % 2 ^ (128 - t) < 2 ^ 128 from
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega))),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem clearTop_hi (t : Nat) (ht : t ≤ 64) (d : SigGolfCandidate.T3.Digest) :
    ((SharedCodec.clearTop t d).extractLsb' (64 * 1) 64).toNat = (d.extractLsb' (64 * 1) 64).toNat % 2 ^ (64 - t) := by
  unfold SharedCodec.clearTop
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show d.toNat % 2 ^ (128 - t) < 2 ^ 128 from
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega)))]
  rw [show 128 - t = 64 + (64 - t) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 - t ≤ 64))]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega)))

theorem d1Mem_lo (M : Word → Word) (A : Nat) (hA : A < 0x84c0) (h16 : A % 16 = 0) :
    d1Mem M (BitVec.ofNat 64 A) = M (BitVec.ofNat 64 A) := by
  unfold d1Mem aH pH
  rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega)]

theorem d1Mem_aH (M : Word → Word) (j : Nat) (h3 : 3 ≤ j) (h10 : j ≤ 10) :
    d1Mem M (aH j) = clr (topZeroBits j) (M (aH j)) := by
  interval_cases j <;> simp [d1Mem, aH, pH, topZeroBits, topZeroAlloc]

theorem internalDummy_iff (k : Nat) : SharedCodec.internalDummy k = true ↔ dummySlot k := by
  simp [SharedCodec.internalDummy, dummySlot]

theorem zero_extract (w : Nat) : (0 : SigGolfCandidate.T3.Digest).extractLsb' (64 * w) 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- DEC's output slots are the inflated layout of the decoded signature. -/
theorem decOut_eq {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (k w : Nat) (hk : k < 332)
    (hw : w < 2) :
    decOut M k w = (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k).extractLsb' (64 * w) 64 := by
  by_cases hd : dummySlot k
  · have e : decOut M k w = 0 := by unfold decOut; rw [if_pos hd]
    rw [e, SharedCodec.inflatedRead, if_pos ((internalDummy_iff k).mpr hd), zero_extract]
  have hnd : ¬ (SharedCodec.internalDummy k = true) := fun h => hd ((internalDummy_iff k).mp h)
  rw [SharedCodec.inflatedRead, if_neg hnd]
  by_cases h180 : k = 180
  · have e : decOut M k w = (if w = 0 then M (BitVec.ofNat 64 0x8440)
        else sibHi (M (BitVec.ofNat 64 0x8448)) (xD M)) := by
      unfold decOut; rw [if_neg hd, if_pos h180]
    rw [e, h180, show SharedCodec.externalFullIndex 180 = 176 from rfl]
    have hd176 : SharedCodec.digC b 176 = BitVec.ofNat 128 (b.toNat / 2 ^ (64 * 648) % 2 ^ 88 +
        SharedCodec.xOfB b % 2 ^ 16 * 2 ^ 88) := by
      unfold SharedCodec.digC; rw [if_neg (by omega), if_pos rfl]
    rw [hd176]
    apply BitVec.eq_of_toNat_eq
    have hX := SharedCodec.xOfB_lt b
    have hw648 := h.word 648 (by omega)
    have ht := h.tail
    have hsplit : b.toNat / 2 ^ (64 * 649) = b.toNat / 2 ^ (64 * 648) / 2 ^ 64 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    rw [hsplit] at ht
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · rw [if_pos rfl, show (BitVec.ofNat 64 0x8440 : Word) = BitVec.ofNat 64 (0x7000 + 8 * 648) from rfl, hw648,
        BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow]
      generalize b.toNat / 2 ^ (64 * 648) = T
      generalize SharedCodec.xOfB b = X at hX
      norm_num
      omega
    · rw [if_neg (by omega), sibHi_toNat, ht, xD_xOfB h, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      generalize b.toNat / 2 ^ (64 * 648) = T
      generalize SharedCodec.xOfB b = X at hX
      norm_num
      omega
  have e : decOut M k w = d1Mem M (slotA (srcK k) w) := by unfold decOut; rw [if_neg hd, if_neg h180]
  rw [e]
  have hk' : ¬ (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183) := hd
  by_cases hA : k < 170
  · have he : SharedCodec.externalFullIndex k = srcK k := by
      unfold SharedCodec.externalFullIndex srcK; split_ifs <;> omega
    have hs : srcK k < 166 := by unfold srcK; split_ifs <;> omega
    rw [he]
    have hdig : SharedCodec.digC b (srcK k) = SharedCodec.cDig b (srcK k) := by
      unfold SharedCodec.digC; rw [if_pos (by omega), if_neg (by omega)]
    rw [hdig, ← slot_word h _ w (by omega) hw]
    unfold slotA
    rw [d1Mem_frame _ _ (by omega) (by omega) (by omega)]
  by_cases hB : k < 180
  · have he : SharedCodec.externalFullIndex k = k - 4 := by
      unfold SharedCodec.externalFullIndex; split_ifs <;> omega
    have hs : srcK k = k - 4 := by unfold srcK; split_ifs <;> omega
    rw [he, hs]
    have hdig : SharedCodec.digC b (k - 4) =
        SharedCodec.clearTop (topZeroBits (k - 4 - 165)) (SharedCodec.cDig b (k - 4)) := by
      unfold SharedCodec.digC; rw [if_pos (by omega), if_pos (by omega)]
    rw [hdig]
    have htz : topZeroBits (k - 4 - 165) ≤ 64 := by
      unfold topZeroBits topZeroAlloc
      have : k - 4 - 165 < 11 := by omega
      interval_cases (k - 4 - 165) <;> decide
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · rw [clearTop_lo _ htz, ← slot_word h _ 0 (by omega) (by omega)]
      unfold slotA
      rw [d1Mem_lo _ _ (by omega) (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [clearTop_hi _ htz, ← slot_word h _ 1 (by omega) (by omega)]
      by_cases hj : k < 172
      · have h0 : topZeroBits (k - 4 - 165) = 0 := by
          unfold topZeroBits topZeroAlloc
          have : k - 4 - 165 = 1 ∨ k - 4 - 165 = 2 := by omega
          rcases this with h | h <;> rw [h] <;> rfl
        rw [h0]
        unfold slotA
        rw [d1Mem_frame _ _ (by omega) (by omega) (by omega), Nat.sub_zero,
          Nat.mod_eq_of_lt (BitVec.isLt _)]
      · have ha : slotA (k - 4) 1 = aH (k - 4 - 165) := by
          unfold slotA aH pH; congr 1; omega
        rw [ha, d1Mem_aH _ _ (by omega) (by omega), clr_toNat _ htz]
  · have h184 : 184 ≤ k := by omega
    have he : SharedCodec.externalFullIndex k = k - 7 := by
      unfold SharedCodec.externalFullIndex; split_ifs <;> omega
    have hs : srcK k = k - 8 := by unfold srcK; split_ifs <;> omega
    rw [he, hs]
    have hdig : SharedCodec.digC b (k - 7) = SharedCodec.cDig b (k - 8) := by
      unfold SharedCodec.digC; rw [if_neg (by omega), if_neg (by omega), show k - 7 - 1 = k - 8 by omega]
    rw [hdig, ← slot_word h _ w (by omega) hw]
    unfold slotA
    rw [d1Mem_frame _ _ (by omega) (by omega) (by omega)]

end ClaudeWCT.W9.Machine.Expand.PrePass
