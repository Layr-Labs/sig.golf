import SigGolfCandidate.T3M.Verify.Mem

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem wdc_word_low (w : ClaudeWCT.W9.T3M.WBytes) :
    (wword w 2725).toNat % 2 ^ 32 = (ClaudeWCT.W9.T3M.wdc w).toNat := by
  rw [wword_toNat]
  simp only [ClaudeWCT.W9.T3M.wdc, ClaudeWCT.W9.T3M.wle32, ClaudeWCT.W9.T3M.dcOff,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_mod_of_dvd _ (by norm_num : (2 : Nat) ^ 32 ∣ 2 ^ 64)]

theorem WitDigest.nonce (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (h : WitDigest w s) :
    s.getMem (BitVec.ofNat 64 23864) = dlo (ClaudeWCT.W9.T3M.wrho w) ∧
    s.getMem (BitVec.ofNat 64 23872) = dhi (ClaudeWCT.W9.T3M.wrho w) := by
  constructor
  · exact (h 2727 (by omega) (by omega)).trans (wdig_lo w 2727).symm
  · exact (h 2728 (by omega) (by omega)).trans (wdig_hi w 2727).symm

theorem WitDigest.counter (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (h : WitDigest w s) :
    LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 23848)) 0 =
      BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
  have hword := h 2725 (by omega) (by omega)
  change s.getMem (BitVec.ofNat 64 23848) = wword w 2725 at hword
  rw [hword]
  apply BitVec.eq_of_toNat_eq
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hmod : (wword w 2725).toNat / 2 ^ (0 / 4 * 32) % 2 ^ 32 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [Nat.mod_eq_of_lt hmod]
  simp only [Nat.zero_div, Nat.zero_mul, pow_zero, Nat.div_one]
  rw [wdc_word_low, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ClaudeWCT.W9.T3M.wdc w).isLt (by norm_num))]

theorem store_counter_header (dc : BitVec 32) :
    StoreKind.merge .w (0 : Word) 4 (BitVec.ofNat 64 dc.toNat) =
      BitVec.ofNat 64 (hdr1 0 dc.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [StoreKind.merge, replaceWord32, hdr1, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt dc.isLt]

end SigGolfCandidate.T3M.Verify
