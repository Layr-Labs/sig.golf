import SigGolfCandidate.T3M.Verify.Mem

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem wdc_word_high (w : ClaudeWCT.W9.T3M.WBytes) :
    (wword w 2728).toNat / 2 ^ 32 % 2 ^ 32 = (ClaudeWCT.W9.T3M.wdc w).toNat := by
  rw [wword_toNat]
  simp only [ClaudeWCT.W9.T3M.wdc, ClaudeWCT.W9.T3M.wle32, ClaudeWCT.W9.T3M.dcOff,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by norm_num,
    Nat.mod_mul_right_div_self, Nat.mod_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem WitDigest.nonce (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (h : WitDigest w s) :
    s.getMem (BitVec.ofNat 64 23848) = dlo (ClaudeWCT.W9.T3M.wrho w) ∧
    s.getMem (BitVec.ofNat 64 23856) = dhi (ClaudeWCT.W9.T3M.wrho w) := by
  constructor
  · exact (h 2725 (by omega) (by omega)).trans (wdig_lo w 2725).symm
  · exact (h 2726 (by omega) (by omega)).trans (wdig_hi w 2725).symm

theorem WitDigest.counter (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (h : WitDigest w s) :
    LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 23872)) 4 =
      BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
  have hword := h 2728 (by omega) (by omega)
  change s.getMem (BitVec.ofNat 64 23872) = wword w 2728 at hword
  rw [hword]
  apply BitVec.eq_of_toNat_eq
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hmod : (wword w 2728).toNat / 2 ^ (4 / 4 * 32) % 2 ^ 32 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [Nat.mod_eq_of_lt hmod]
  change (wword w 2728).toNat / 2 ^ 32 % 2 ^ 32 = _
  rw [wdc_word_high, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ClaudeWCT.W9.T3M.wdc w).isLt (by norm_num))]

theorem WitDigest.clear_counter_padding (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState)
    (h : WitDigest w s) :
    StoreKind.merge .w (s.getMem (BitVec.ofNat 64 23872)) 0 0 =
      BitVec.ofNat 64 (hdr1 0 (ClaudeWCT.W9.T3M.wdc w).toNat) := by
  have hword := h 2728 (by omega) (by omega)
  change s.getMem (BitVec.ofNat 64 23872) = wword w 2728 at hword
  rw [hword]
  apply BitVec.eq_of_toNat_eq
  rw [merge_w0_toNat, wdc_word_high]
  have hc := (ClaudeWCT.W9.T3M.wdc w).isLt
  simp only [BitVec.toNat_ofNat, hdr1, Nat.zero_mod, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by nlinarith :
    (ClaudeWCT.W9.T3M.wdc w).toNat * 2 ^ 32 < 2 ^ 64)]
  simp

end SigGolfCandidate.T3M.Verify
