import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePassByte
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_ComposeBack
set_option Elab.async false

/-! # The img-v6 pre-pass from the real initial state

From `w9init` with the 5,239-byte v6 signature `b` (pc moved to the pre-pass entry 43250, i.e. after the word-0
`jal 43250`), the pre-pass reaches `44096` in 84 steps in a state whose registers and whole memory are those of
`w9init` with the old 5,248-byte codec bytes `SharedCodec48.sigBC (SharedCodec.sigDecC b)`. -/

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
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x6620) (bytes m)).writeBytesAsWords
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

/-- The last (7-byte) signature dword of the 5,239-byte signature. -/
theorem tailWord (b : SharedCodec.CBytes) :
    bytesToWordLE (((bytes b).drop (8 * 654)).take 8) = BitVec.ofNat 64 (b.toNat / 2 ^ (64 * 654)) := by
  have hb := b.isLt
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e, BitVec.toNat_ofNat]
  by_cases h7 : i < 7
  · simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, List.getElem?_range (show 8 * 654 + i < 5239 by omega), if_pos hi, Option.map_some,
      Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (8 * 654 + i) = 64 * 654 + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    have : b.toNat / 2 ^ (64 * 654) < 2 ^ 56 := by
      apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add]; exact hb
    generalize b.toNat / 2 ^ (64 * 654) = y at *
    interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
  · obtain rfl : i = 7 := by omega
    simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, List.getElem?_eq_none (show (List.range 5239).length ≤ 8 * 654 + 7 by simp)]
    have : b.toNat / 2 ^ (64 * 654) < 2 ^ 56 := by
      apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add]; exact hb
    generalize b.toNat / 2 ^ (64 * 654) = y at *
    simp
    omega

/-- The pre-pass from the real initial state: registers and the whole memory become those of `w9init` with the
old-codec bytes `SharedCodec48.sigBC (SharedCodec.sigDecC b)`. -/
theorem pre_init (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    ∃ t, Steps Images.expandImage ((w9init Images.expandImage m pk b).setPC (pcOf 43250)) 84 84 t ∧
      t.pc = pcOf 44096 ∧
      (∀ r, t.getReg r = (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))).getReg r) ∧
      Frame (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))) t (fun _ => False) := by
  have hsig : ∀ j, j < 654 → ((w9init Images.expandImage m pk b).setPC (pcOf 43250)).getMem
      (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64 := by
    intro j hj
    rw [MachineState.getMem_setPC, w9_getMem _ m pk (by decide) b _ (by omega), if_pos (by omega),
      show 0x7000 + 8 * j - 0x7000 = 8 * j by omega]
    exact bytesToWordLE_bytes_e b j (by omega)
  have htail : (((w9init Images.expandImage m pk b).setPC (pcOf 43250)).getMem
      (BitVec.ofNat 64 (0x7000 + 8 * 654))).setWidth 56 = b.extractLsb' (64 * 654) 56 := by
    rw [MachineState.getMem_setPC, w9_getMem _ m pk (by decide) b _ (by omega), if_pos (by omega),
      show 0x7000 + 8 * 654 - 0x7000 = 8 * 654 by omega, tailWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    generalize b.toNat / 2 ^ (64 * 654) = y
    omega
  obtain ⟨t, st, tp, t6, t7, t28, t30, rt, mt⟩ := pre_spec ((w9init Images.expandImage m pk b).setPC (pcOf 43250)) rfl
  have hb := pre_bytes _ t b hsig htail mt
  refine ⟨t, st, tp, fun r => ?_, fun A hA _ => ?_⟩
  · by_cases hr : r ∈ [.x6, .x7, .x28, .x30]
    · rw [w9_getReg_zero _ _ _ _ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)]
      simp at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact t6
      · exact t7
      · exact t28
      · exact t30
    · rw [rt r hr, MachineState.getReg_setPC]
      exact w9_getReg _ _ _ _ _ r
  · by_cases hal : 0x7000 ≤ A ∧ A < 0x7000 + 5248 ∧ (A - 0x7000) % 8 = 0
    · obtain ⟨j, rfl⟩ : ∃ j, A = 0x7000 + 8 * j := ⟨(A - 0x7000) / 8, by omega⟩
      rw [hb j (by omega), w9_getMem _ m pk (le_refl _) _ _ hA, if_pos (by omega),
        show 0x7000 + 8 * j - 0x7000 = 8 * j by omega, bytesToWordLE_bytes_e _ j (by omega)]
    · rw [mt, preMem_other _ A hA (by omega) (by omega) (by simp only [pA]; omega), MachineState.getMem_setPC,
        w9_getMem _ m pk (by decide) b _ hA, if_neg (by omega), w9_getMem _ m pk (le_refl _) _ _ hA, if_neg (by omega)]

/-! ### Entry (word 0: `jal 43250`) -/
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

theorem entry_code0 : CodeAt Images.expandImage (pcOf 0) [0x3c82a06f] := by
  apply codeAt_expand_current_chunk
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem w9_pc (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) :
    (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl

theorem entry_step0 (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps Images.expandImage s 1 1 (s.setPC (pcOf 43250)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0x3c82a06f#32) 0 = some 43250 by decide +kernel)
  exact jal_x0_step entry_code0 hd hoff s hpc

/-- Entry jump + pre-pass from the real initial state (85 steps, 85 cycles). -/
theorem prepass_init_exact (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    ∃ u, Steps Images.expandImage (w9init Images.expandImage m pk b) 85 85 u ∧ u.pc = pcOf 44096 ∧
      (∀ r, u.getReg r = (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))).getReg r) ∧
      Frame (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))) u (fun _ => False) := by
  obtain ⟨t, st, tp, tr, tf⟩ := pre_init m pk b
  exact ⟨t, (entry_step0 _ (w9_pc _ _ _ _)).trans st, tp, tr, tf⟩

/-- The shape used by the Link. -/
theorem prepass_init (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    ∃ u c, Steps Images.expandImage (w9init Images.expandImage m pk b) 85 c u ∧ c ≤ 200 ∧ u.pc = pcOf 44096 ∧
      (∀ r, u.getReg r = (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))).getReg r) ∧
      Frame (w9init Images.expandImage m pk (SharedCodec48.sigBC (SharedCodec.sigDecC b))) u (fun _ => False) := by
  obtain ⟨u, su, up, ur, uf⟩ := prepass_init_exact m pk b
  exact ⟨u, 85, su, by decide, up, ur, uf⟩

#print axioms pre_init
#print axioms prepass_init_exact
#print axioms prepass_init
end ClaudeWCT.W9.Machine.Expand.PrePass
