import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge077
import SigGolfCandidate.Merge078.P1

set_option debug.skipKernelTC true
set_option linter.all false

-- ==== merged from T3M_Expand_Layers ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chainCount height)
open SigGolfCandidate.T3M.Search (NODE NOUT ENC)
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option maxHeartbeats 2000000
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open OracleComp SigGolfCandidate.T3
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route chainCount height)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
section step
variable {sk : BitVec 256}
end step
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Expand.BC
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ComposeBack ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
theorem extractByte_toNat_e (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
theorem word_ext_bytes_e {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat_e] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega
theorem extractByte_or8_e (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE_e (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8_e _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
theorem bytesToWordLE_bytes_e {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
theorem bytes_length_e {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
/-- A possibly partial last word (E11: word 648 holds the 6-byte tail). -/
theorem bytesToWordLE_bytes_p {n : Nat} (x : Bytes n) (j : Nat) (_hj : 8 * j < n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  by_cases hin : 8 * j + i < n
  · simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, List.getElem?_range hin, if_pos hi, Option.map_some,
      Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    generalize x.toNat / 2 ^ (64 * j) = y
    interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
  · have hn : (List.range n)[8 * j + i]? = none := by
      rw [List.getElem?_eq_none]; simp; omega
    simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, hn, if_pos hi, Option.map_none, Option.getD_none, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
    have hx := x.isLt
    have hy : x.toNat / 2 ^ (64 * j) < 2 ^ (8 * i) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
      exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h0 : x.toNat / 2 ^ (64 * j) % 2 ^ 64 / 2 ^ (8 * i) = 0 :=
      Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) hy)
    rw [h0]; rfl
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
def w9init (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) : MachineState :=
  (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x65A0) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords (BitVec.ofNat 64 0x7000) (bytes σ))).setReg .x2
    (BitVec.ofNat 64 (dataBase im))
set_option maxRecDepth 100000 in
theorem hdrBankBytes_length : hdrBankBytes.length = 4608 := by decide +kernel
set_option maxRecDepth 100000 in
theorem planBytes_length : planBytes.length = 1024 := by decide +kernel
set_option maxRecDepth 100000 in
theorem lplanBytes_length : lplanBytes.length = 1536 := by decide +kernel
theorem data_length {im : Image} (hd : ExpandDataOK im) : im.data.length = 27648 := by
  rw [hd, List.length_append, List.length_append, List.length_append, List.length_append, lplanBytes_length,
    planBytes_length, ESearch.expCostBytes_length, hdrBankBytes_length, Search.expandLegacyData_length]
theorem dataBase_eq {im : Image} (hd : ExpandDataOK im) : dataBase im = Compact2.LPLAN := by
  unfold dataBase
  rw [data_length hd]
  rfl
theorem data_drop_plan {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 1536 = planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]),
    List.drop_eq_nil_of_le (by rw [lplanBytes_length]), List.nil_append, List.append_assoc, List.append_assoc]
theorem data_drop_cost {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 2560 = expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 2560 = 1536 + 1024 from rfl, ← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]),
    List.drop_eq_nil_of_le (by rw [planBytes_length]), List.nil_append, List.append_assoc]
theorem data_drop_bank {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 18944 = hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 18944 = 2560 + 16384 from rfl, ← List.drop_drop, data_drop_cost hd, List.append_assoc,
    List.drop_append_of_le_length (by rw [ESearch.expCostBytes_length]),
    List.drop_eq_nil_of_le (by rw [ESearch.expCostBytes_length]), List.nil_append]
theorem data_drop_legacy {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 23552 = SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 23552 = 18944 + 4608 from rfl, ← List.drop_drop, data_drop_bank hd,
    List.drop_append_of_le_length (by rw [hdrBankBytes_length]),
    List.drop_eq_nil_of_le (by rw [hdrBankBytes_length]), List.nil_append]
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312)
include hd
theorem w9init_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5312 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x65A0 ≤ A ∧ A < 0x65C0 ∧ (A - 0x65A0) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x65A0)).take 8)
      else if Compact2.LPLAN ≤ A ∧ A < Compact2.LPLAN + 27648 ∧ (A - Compact2.LPLAN) % 8 = 0 then
        bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x65A0 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ Compact2.LPLAN A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9init_data (A : Nat) (h1 : Compact2.LPLAN ≤ A) (h2 : A < Compact2.LPLAN + 27648)
    (h3 : (A - Compact2.LPLAN) % 8 = 0) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) = bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8) := by
  unfold Compact2.LPLAN at h1 h2 h3
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by unfold Compact2.LPLAN; omega)]
omit hd in
theorem w9init_pc : (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl
end init
theorem data_plan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1024) :
    (im.data.drop (1536 + o)).take 8 = (planBytes.drop o).take 8 := by
  rw [← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]; omega),
    List.take_append_of_le_length (by simp [planBytes_length]; omega)]
theorem data_lplan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1536) :
    (im.data.drop o).take 8 = (lplanBytes.drop o).take 8 := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]; omega),
    List.take_append_of_le_length (by simp [lplanBytes_length]; omega)]
theorem w9init_plan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    PlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold PLAN Compact2.LPLAN; omega) (by unfold PLAN Compact2.LPLAN; omega)
      (by unfold PLAN Compact2.LPLAN; omega),
    show PLAN + 8 * k - Compact2.LPLAN = 1536 + 8 * k by unfold PLAN Compact2.LPLAN; omega, data_plan hd _ (by omega)]
theorem w9init_lplan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.LPlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold Compact2.LPLAN; omega) (by unfold Compact2.LPLAN; omega)
      (by unfold Compact2.LPLAN; omega),
    show Compact2.LPLAN + 8 * k - Compact2.LPLAN = 8 * k by omega, data_lplan hd _ (by omega)]
/-- C4 (adapted from b3cc11b's `w9init_toptab`): the two top-path plan tables of the post-pass (legacy data offsets
2944 / 3456 = data offsets 26496 / 27008). -/
theorem w9init_toptab {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.TopTabAt (w9init im m pk σ) := by
  have key : ∀ o : Nat, (im.data.drop (23552 + o)).take 8 =
      (SigGolfCandidate.T3M.Images.expandLegacyData.drop o).take 8 := fun o => by
    rw [← List.drop_drop, data_drop_legacy hd]
  have tk : ∀ (L : List (BitVec 8)) (a k : Nat), 8 * k + 8 ≤ 512 →
      (((L.drop a).take 512).drop (8 * k)).take 8 = (L.drop (a + 8 * k)).take 8 := fun L a k hk => by
    rw [List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPA Compact2.LPLAN; omega)
        (by unfold Compact2.TOPA Compact2.LPLAN; omega) (by unfold Compact2.TOPA Compact2.LPLAN; omega),
      show Compact2.TOPA + 8 * k - Compact2.LPLAN = 23552 + (2944 + 8 * k) by unfold Compact2.TOPA Compact2.LPLAN; omega,
      key]
    unfold Compact2.topABytes
    rw [tk _ _ _ (by omega)]
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPB Compact2.LPLAN; omega)
        (by unfold Compact2.TOPB Compact2.LPLAN; omega) (by unfold Compact2.TOPB Compact2.LPLAN; omega),
      show Compact2.TOPB + 8 * k - Compact2.LPLAN = 23552 + (3456 + 8 * k) by unfold Compact2.TOPB Compact2.LPLAN; omega,
      key]
    unfold Compact2.topBBytes
    rw [tk _ _ _ (by omega)]
-- [h2 lane] removed front_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
-- [h2 lane] removed front_pre30: a fact about the record's original expand word 0 / 342, which H2 replaces
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput Layer LayerSignature height chainCount)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit sideOff height_le)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open SigGolfCandidate.T3M (window window_flatMap_const zeros)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePassInit ====
section

/-! # T51 DEC from the real initial state

E8 (P1): word 0 is `j 60734` (the pre-pass, 185 steps, then `j 54569` = DEC). From `w9init` with the 5,188-byte signature
`b`, the pre-pass rebuilds DEC's T1 layout (`unpackB b`) and DEC writes the expander's inflated slot layout
`SharedCodec.inflatedRead 0 (SharedCodec.digC b)` (332 slots at `0x7000`) and the hint at `0x66000`, zeroes its
temporaries and jumps to word 1 (`dec_init_r6`, at most 2,347 cycles; N7g 2,271). NBZ5R (NB): DEC (NR2) divides
the field `N` by 88 and rejects a non-canonical `N ≥ nCanon = R * 88` at `j 354` (`dec_reject_nc`), which is exactly
a decoded hint `≥ 8464`. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e bytesToWordLE_bytes_e word_ext_bytes_e extractByte_bytesToWordLE_e
  extractByte_toNat_e)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `w9init` memory before the signature write (independent of the signature). -/
def preSig (im : Image) (m : Message) (pk : PublicKey) : MachineState :=
  ((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x65A0) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)

theorem w9_getMem (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (hn : n ≤ 5248) (σ : Bytes n) (A : Nat)
    (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 8 * ((n + 7) / 8) ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else (preSig im m pk).getMem (BitVec.ofNat 64 A) := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; omega) hA,
    bytes_length_e]
  rfl

theorem w9_getReg (im : Image) (m : Message) (pk : PublicKey) {n n' : Nat} (σ : Bytes n) (σ' : Bytes n') (r : Reg) :
    (w9init im m pk σ).getReg r = (w9init im m pk σ').getReg r := by
  unfold w9init
  by_cases h : r = .x2
  · subst h
    rw [MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide)]
  · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]
    simp only [MachineState.getReg_writeBytesAsWords]

theorem w9_getReg_zero (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) (r : Reg)
    (h : r ≠ .x2) : (w9init im m pk σ).getReg r = 0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]
  simp only [MachineState.getReg_writeBytesAsWords]
  cases r <;> rfl

def jalTo0 (w : BitVec 32) (n : Nat) : Option Nat :=
  match decodeInstruction w with
  | some (.base (.JAL .x0 imm)) =>
    let a := (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64
    if 0x1000 ≤ a ∧ a % 4 = 0 then some ((a - 0x1000) / 4) else none
  | _ => none
theorem jalTo0_sound {w : BitVec 32} {n m : Nat} (h : jalTo0 w n = some m) :
    ∃ imm, decodeInstruction w = some (.base (.JAL .x0 imm)) ∧
      (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64 := by
  unfold jalTo0 at h
  split at h
  · rename_i imm hd
    refine ⟨imm, hd, ?_⟩
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
      rw [Nat.mod_eq_of_lt (a := 0x1000 + 4 * _) (by omega)]
      omega
    · cases h
  · cases h

theorem entry_code0 : CodeAt Images.expandImage (pcOf 0) [0x4f83b06f] :=
  codeAt_expand_current_chunk (by decide) (by decide) (by decide +kernel)

theorem w9_pc (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) :
    (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl

theorem entry_step0 (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps Images.expandImage s 1 1 (s.setPC (pcOf 60734)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0x4f83b06f#32) 0 = some 60734 by decide +kernel)
  exact jal_x0_step entry_code0 hd hoff s hpc

/-- E11: word 0 + the pre-pass: from word 0 to DEC's entry 54569 with the T1-layout signature `unpackB b`. -/
theorem pre_entry (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 0) (hsig : SigMemC s0.getMem b) :
    ∃ u, Steps Images.expandImage s0 252 252 u ∧ u.pc = pcOf 54569 ∧
      (∀ r ∈ [Reg.x7, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧ RegsExcept s0 u [.x7, .x28, .x29, .x30, .x31] ∧
      SigMem u.getMem (unpackB b) ∧ Frame s0 u (fun A => 0x7000 ≤ A ∧ A < 0x84c0) := by
  have st0 := entry_step0 s0 hpc
  obtain ⟨u, su, pu, zu, ru, mu⟩ := pre_spec (s0.setPC (pcOf 60734)) rfl
  have e : (s0.setPC (pcOf 60734)).getMem = s0.getMem := funext fun _ => MachineState.getMem_setPC
  have em : u.getMem = preMem s0.getMem := funext fun A => by rw [mu, e]
  refine ⟨u, st0.trans su, pu, zu, fun r hr => (ru r hr).trans MachineState.getReg_setPC, by rw [em]; exact sigMem_pre hsig,
    fun A hA hn => ?_⟩
  rw [em]
  have hn' : A < 0x7000 ∨ 0x84c0 ≤ A := by omega
  apply preMem_other s0.getMem A hA (by omega) (by omega)
  intro c hc he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  unfold hiA at he
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- U16b: the T1-layout read of DEC's slots is the U16b codec's (`digC_unpack`). -/
theorem inflated_unpack (b : SharedCodec.CBytes) (k : Nat) (hk : k < 332) :
    SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (T1C.digC (unpackB b)) k =
      SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k := by
  unfold SharedCodec.inflatedRead
  split_ifs
  · rfl
  · rw [digC_unpack b _ (by unfold SharedCodec.externalFullIndex; split_ifs <;> omega)]

/-- The canonical bound DEC checks (NBZ5R NB, NR2): the field `N = cDig 0 + X / 2^35 * 2^128` must be `< R * 88`. -/
abbrev nCanon : Nat := 654979593471881553734014281973929790456

theorem hints_unpack (b : SharedCodec.CBytes) (hc : SharedCodec.nOfB b < nCanon) :
    T1C.hints (unpackB b) = (SharedCodec.sigDecC b).policyHints := by
  apply BitVec.eq_of_toNat_eq
  rw [SharedCodec.policyHints_sigDecC_toNat]
  unfold T1C.hints SharedCodec.hintOfN
  rw [nOfB_unpack, if_pos (by rw [SharedCodec.R_mul_88]; exact hc)]
  have hl := packH_lt (SharedCodec.nOfB b % 88) (Nat.mod_lt _ (by norm_num))
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show SharedCodec.packH (SharedCodec.nOfB b % 88) < 2 ^ 16 by omega)]

/-- V45: the expand entry memory of the real initial state holds the 5,188-byte signature. -/
theorem w9_sigMemC (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    SigMemC (w9init Images.expandImage m pk b).getMem b := by
  constructor
  intro j hj
  rw [w9_getMem _ _ _ (by decide) b _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_p b j (by omega)

/-- DEC, accepting, from any state at word 0 holding the signature (N7g: word 0 + the pre-pass + DEC, at most 2,271
cycles (NB: 2,347); DEC also rewrites slot 0 with `N / 88`). -/
theorem dec_gen (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 0) (hsig : SigMemC s0.getMem b)
    (hc : SharedCodec.nOfB b < nCanon) :
    ∃ u k c, Steps Images.expandImage s0 k c u ∧ c ≤ 2413 ∧ u.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧
      RegsExcept s0 u [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame s0 u (fun A => A = 417792 ∨ (0x7000 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, st1, p1, z1, r1, hsig1, f1⟩ := pre_entry s0 b hpc hsig
  have hn : nOfM s1.getMem = SharedCodec.nOfB b := by rw [nOfM_eq hsig1, nOfB_unpack]
  obtain ⟨t, k, c, st, hcc, tp, tz, tr, tm, th, tf⟩ := dec_run s1 p1 (by rw [hn]; exact hc)
  refine ⟨t, 252 + k, 252 + c, st1.trans st, by omega, tp, ?_, (r1.trans tr).mono (by decide), ?_,
    by rw [th, hint_eq hsig1, hints_unpack b hc], (f1.trans tf).mono (fun A _ h => ?_)⟩
  · intro r hr
    by_cases hr' : r ∈ [Reg.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30]
    · exact tz r hr'
    · have : r = .x31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'; tauto
      subst this
      rw [tr .x31 (by decide)]; exact z1 .x31 (by decide)
  · intro k hk
    have e0 := (tm k 0 hk (by omega)).trans (decOut_eq hsig1 k 0 hk (by omega))
    have e1 := (tm k 1 hk (by omega)).trans (decOut_eq hsig1 k 1 hk (by omega))
    unfold slotA at e0 e1
    rw [Nat.mul_zero, Nat.add_zero] at e0
    rw [← inflated_unpack b k hk]
    exact ⟨e0, e1⟩
  · rcases h with ⟨h1, h2⟩ | h
    · exact Or.inr ⟨by omega, h2⟩
    · exact h

/-- DEC, accepting (N7g): from the real initial state with a canonical field `N`, word 0 + the pre-pass + DEC reach
word 1 (at most 2,271 cycles) with `w9init`'s registers, the inflated slot layout of the decoded signature at
`0x7000`, the hint at `0x66000`; only the hint word and `[0x7000, 0x84c0)` are written. -/
theorem dec_init_r6 (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) (hc : SharedCodec.nOfB b < nCanon) :
    ∃ u k c, Steps Images.expandImage (w9init Images.expandImage m pk b) k c u ∧ c ≤ 2413 ∧ u.pc = pcOf 1 ∧
      (∀ r, u.getReg r = (w9init Images.expandImage m pk b).getReg r) ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame (w9init Images.expandImage m pk b) u (fun A => A = 417792 ∨ (0x7000 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨u, k, c, su, hcc, up, uz, ur, ui, uh, uf⟩ := dec_gen _ b (w9_pc Images.expandImage m pk b) (w9_sigMemC m pk b) hc
  refine ⟨u, k, c, su, hcc, up, ?_, ui, uh, uf⟩
  intro r
  by_cases hr : r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31]
  · rw [uz r hr, w9_getReg_zero _ _ _ _ _ (by intro e; subst e; simp at hr)]
  · exact ur r hr


/-- DEC, rejecting (N7g): a non-canonical field `N ≥ nCanon` sends the expander to word 354 after 270 steps (word 0,
the pre-pass, then DEC's 84). -/
theorem dec_reject_nc (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) (hc : ¬ SharedCodec.nOfB b < nCanon) :
    ∃ u k, k ≤ 350 ∧ Steps Images.expandImage (w9init Images.expandImage m pk b) k k u ∧ u.pc = pcOf 354 := by
  generalize hs0 : w9init Images.expandImage m pk b = s0
  have hpc : s0.pc = pcOf 0 := by rw [← hs0]; exact w9_pc Images.expandImage m pk b
  have hsig : SigMemC s0.getMem b := by rw [← hs0]; exact w9_sigMemC m pk b
  obtain ⟨s1, st1, p1, -, -, hsig1, -⟩ := pre_entry s0 b hpc hsig
  obtain ⟨t, k, hk, st, tp⟩ := dec_bad s1 p1 (by rw [nOfM_eq hsig1, nOfB_unpack]; exact hc)
  exact ⟨t, 252 + k, by omega, st1.trans st, tp⟩

/-- DEC, rejecting: a hint `≥ 8464` (on N7g exactly a non-canonical field, `policyHints_sigDecC_ge_iff`) sends the
expander to word 354 after 270 steps (word 0, the pre-pass, then DEC's 84). -/
theorem dec_reject (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh : 8464 ≤ (SharedCodec.sigDecC b).policyHints.toNat) :
    ∃ u k, k ≤ 350 ∧ Steps Images.expandImage (w9init Images.expandImage m pk b) k k u ∧ u.pc = pcOf 354 :=
  dec_reject_nc m pk b (by
    rw [SharedCodec.policyHints_sigDecC_ge_iff, SharedCodec.R_mul_88] at hh
    exact Nat.not_lt.mpr hh)

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactLoop ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCoord ====
section

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt planBytes)
open ClaudeWCT.W9.T3M (authBase authRoot)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
end eval
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt child_bits)
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactRun ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PairCopy ====
section

/-! # Pairing stage 1: the lower-chain pair copy block (expand words 48000 .. 48017)

The witness constructor's lower-layer chain copy (`jal ra,48000` at 42241 / 42414 / 42563, with `a0` = the staging
chain area of the layer (43 blocks of 64 bytes, chain 42 first, value at block offset 48) and `a1` = the final paired
chain area) runs

```
48000  addi a2,zero,21
48001  ld t1,48(a0);  sd t1,88(a1)     -- F chain 2p+2's value  -> pair offset 88
       ld t1,56(a0);  sd t1,96(a1)
       ld t1,112(a0); sd t1,16(a1)     -- G chain 2p+1's value  -> pair offset 16
       ld t1,120(a0); sd t1,24(a1)
       addi a0,a0,128; addi a1,a1,104; addi a2,a2,-1; bne a2,zero,48001
48013  ld t1,48(a0); sd t1,48(a1); ld t1,56(a0); sd t1,56(a1)   -- chain 0's value at offset 48 of its F block
       jalr zero,0(ra)
```

It writes only value words; the pair gaps keep the constructor's zero fill. -/

namespace ClaudeWCT.W9.Machine.Expand.PairCopy
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false

section
variable {im : Image} (hc : Code im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
end
