import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePassByte
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_ComposeBack

/-! # T51 DEC from the real initial state

Word 0 is `j 54569` (DEC). From `w9init` with the 5,195-byte signature `b`, DEC writes the expander's inflated slot
layout `SharedCodec.inflatedRead 0 (SharedCodec.digC b)` (332 slots at `0x7000`) and the hint at `0x66000`, rejects a
hint `≥ 7744` at `j 354`, zeroes its temporaries and jumps to word 1 (2,006 steps in all). -/

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

theorem entry_code0 : CodeAt Images.expandImage (pcOf 0) [0x4a43506f] :=
  codeAt_expand_current_chunk (by decide) (by decide) (by decide +kernel)

theorem w9_pc (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) :
    (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl

theorem entry_step0 (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps Images.expandImage s 1 1 (s.setPC (pcOf 54569)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0x4a43506f#32) 0 = some 54569 by decide +kernel)
  exact jal_x0_step entry_code0 hd hoff s hpc

theorem dropTake_getD {α : Type} (l : List α) (d : α) (a i : Nat) (hi : i < 8) :
    ((l.drop a).take 8).getD i d = l.getD (a + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem bytes_getD {n : Nat} (x : Bytes n) (i : Nat) (hi : i < n) :
    (bytes x).getD i 0 = x.extractLsb' (8 * i) 8 := by
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

/-- The DEC entry memory of the real initial state holds the 5,195-byte signature. -/
theorem w9_sigMem (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    SigMem (w9init Images.expandImage m pk b).getMem b := by
  constructor
  · intro j hj
    rw [w9_getMem _ _ _ (by decide) b _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega]
    exact bytesToWordLE_bytes_e b j (by omega)
  · rw [w9_getMem _ _ _ (by decide) b _ (by omega), if_pos (by omega), show 0x8448 - 0x7000 = 5192 by rfl]
    have hbyte : ∀ i, i < 3 → (bytesToWordLE (((bytes b).drop 5192).take 8)).toNat / 2 ^ (8 * i) % 256 =
        b.toNat / 2 ^ (8 * 5192) / 2 ^ (8 * i) % 256 := by
      intro i hi
      rw [← extractByte_toNat_e, extractByte_bytesToWordLE_e _ _ (by omega), dropTake_getD _ _ _ _ (by omega),
        bytes_getD b _ (by omega), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        ← Nat.pow_add, show 8 * 5192 + 8 * i = 8 * (5192 + i) by omega]
    have h0 := hbyte 0 (by omega)
    have h1 := hbyte 1 (by omega)
    have h2 := hbyte 2 (by omega)
    rw [show 64 * 649 = 8 * 5192 by rfl]
    generalize (bytesToWordLE (((bytes b).drop 5192).take 8)).toNat = W at h0 h1 h2
    generalize b.toNat / 2 ^ (8 * 5192) = B at h0 h1 h2
    norm_num at h0 h1 h2 ⊢
    omega

/-- DEC, accepting, from any state at word 0 holding the signature. -/
theorem dec_gen (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 0) (hsig : SigMem s0.getMem b)
    (hh : (SharedCodec.sigDecC b).policyHints.toNat < 7744) :
    ∃ u, Steps Images.expandImage s0 2006 2006 u ∧ u.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], u.getReg r = 0) ∧
      RegsExcept s0 u [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame s0 u (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  have st0 := entry_step0 s0 hpc
  have e : (s0.setPC (pcOf 54569)).getMem = s0.getMem := funext fun _ => MachineState.getMem_setPC
  have hsig1 : SigMem (s0.setPC (pcOf 54569)).getMem b := by rw [e]; exact hsig
  obtain ⟨t, st, tp, tz, tr, tm, th, tf⟩ := dec_run (s0.setPC (pcOf 54569)) rfl (by rw [hint_toNat hsig1]; exact hh)
  refine ⟨t, st0.trans st, tp, tz, fun r hr => (tr r hr).trans MachineState.getReg_setPC, ?_,
    th.trans (hint_eq hsig1), fun A hA hn => (tf A hA hn).trans MachineState.getMem_setPC⟩
  intro k hk
  have e0 := (tm k 0 hk (by omega)).trans (decOut_eq hsig1 k 0 hk (by omega))
  have e1 := (tm k 1 hk (by omega)).trans (decOut_eq hsig1 k 1 hk (by omega))
  unfold slotA at e0 e1
  rw [Nat.mul_zero, Nat.add_zero] at e0
  exact ⟨e0, e1⟩

/-- DEC, accepting: from the real initial state, word 0 + DEC reach word 1 with `w9init`'s registers, the inflated
slot layout of the decoded signature at `0x7000`, the hint at `0x66000`; only the hint word and `[0x70d0, 0x84c0)`
are written. -/
theorem dec_init (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh : (SharedCodec.sigDecC b).policyHints.toNat < 7744) :
    ∃ u, Steps Images.expandImage (w9init Images.expandImage m pk b) 2006 2006 u ∧ u.pc = pcOf 1 ∧
      (∀ r, u.getReg r = (w9init Images.expandImage m pk b).getReg r) ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame (w9init Images.expandImage m pk b) u (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨u, su, up, uz, ur, ui, uh, uf⟩ := dec_gen _ b (w9_pc Images.expandImage m pk b) (w9_sigMem m pk b) hh
  refine ⟨u, su, up, ?_, ui, uh, uf⟩
  intro r
  by_cases hr : r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30]
  · rw [uz r hr, w9_getReg_zero _ _ _ _ _ (by intro e; subst e; simp at hr)]
  · exact ur r hr

/-- DEC, rejecting: a hint `≥ 7744` sends the expander to word 354 (the failure exit) after 80 steps. -/
theorem dec_reject (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh : 7744 ≤ (SharedCodec.sigDecC b).policyHints.toNat) :
    ∃ u, Steps Images.expandImage (w9init Images.expandImage m pk b) 80 80 u ∧ u.pc = pcOf 354 := by
  generalize hs0 : w9init Images.expandImage m pk b = s0
  have hpc : s0.pc = pcOf 0 := by rw [← hs0]; exact w9_pc Images.expandImage m pk b
  have hsig : SigMem s0.getMem b := by rw [← hs0]; exact w9_sigMem m pk b
  have st0 := entry_step0 s0 hpc
  have e : (s0.setPC (pcOf 54569)).getMem = s0.getMem := funext fun _ => MachineState.getMem_setPC
  have hsig1 : SigMem (s0.setPC (pcOf 54569)).getMem b := by rw [e]; exact hsig
  obtain ⟨t, st, tp, -, -, -⟩ := d1_spec (s0.setPC (pcOf 54569)) rfl
  rw [if_neg (by rw [hint_toNat hsig1]; omega)] at tp
  have hc : CodeAt Images.expandImage (pcOf 54647) [0xfadca06f] :=
    codeAt_t51_at 54647 (by decide) (by decide) (by decide)
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0xfadca06f#32) 54647 = some 354 by decide +kernel)
  exact ⟨_, (st0.trans st).trans (jal_x0_step hc hd hoff t tp), rfl⟩

end ClaudeWCT.W9.Machine.Expand.PrePass
