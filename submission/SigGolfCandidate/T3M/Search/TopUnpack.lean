import SigGolfCandidate.T3M.Search.TopSegments
import SigGolfCandidate.T3M.Search.TopWindow

/-! ## R6 top-trial kernel (campaign R6, stream SIGN-A; `sign/kernel/KERNEL-SPEC.txt`)
One kernel for sign and expand (instances `b = 543` sign, `b = 354` expand): `K` (128 words: LOW/HIGH half test and
accept glue) and the digit unpacker `U` (169 words, position independent). Instance parameters: `K_ENTRY` (sign
21667, expand 49226), `U_ENTRY` (1758 / 49626), the 1696-byte packed table block (0xFFF800 / RAM 0xA0000, kernel
register `a0` = block + 160), the credit cell (0x66018 / 0x66040); both reject into `b + 468` (1011 / 822) and use
floor 19 (RC set; `li s5, 16` / `li s5, 19`). The K words of the two instances differ only at offsets 0, 1 (block
address), 116 (credit offset), 118 (`j U_ENTRY`) and 127 (`j b + 468`). -/
section
namespace SigGolfCandidate.T3M.Search.R6
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def kBase (b : Nat) : Nat := if b = 354 then 49226 else 21667
def uBase (b : Nat) : Nat := if b = 354 then 49626 else 1758
def tblBlk (b : Nat) : Nat := if b = 354 then 0xA0000 else 0xFFF800
def creditAddr (b : Nat) : Nat := if b = 354 then 0x66040 else 0x66018
/-- The choice flag cell (0 = LOW, 128 = HIGH); `FLAG` in `Selector`. -/
abbrev FLAGA : Nat := 0x667F8
/-- The kernel's top floor (RC set: 19; the `li s5` immediates are `kFloor - 3` and `kFloor`). -/
def kFloor : Nat := 19
@[simp] theorem kBase_543 : kBase 543 = 21667 := rfl
@[simp] theorem uBase_543 : uBase 543 = 1758 := rfl
@[simp] theorem tblBlk_543 : tblBlk 543 = 0xFFF800 := rfl
@[simp] theorem creditAddr_543 : creditAddr 543 = 0x66018 := rfl
@[simp] theorem kBase_354 : kBase 354 = 49226 := rfl
@[simp] theorem uBase_354 : uBase 354 = 49626 := rfl
@[simp] theorem tblBlk_354 : tblBlk 354 = 0xA0000 := rfl
@[simp] theorem creditAddr_354 : creditAddr 354 = 0x66040 := rfl

def kCodeS : List (BitVec 32) := [0x1000537,0x8a050513,0xa13,0x1000a93,0x1c03c663,0x231e13,0x3fce7e13,0xae0e33,0xf60e6c83,0xccde93,0x4efe93,0x1dc8cb3,0x635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0xe35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x1635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x1e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x3635e13,0x1fce7e13,0xae0e33,0x400e6583,0x3f35f13,0x139e13,0x1cf6f33,0x2f1e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x5f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0xcf5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0x13f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0x1af5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x21f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x28f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x2ff5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x36f5e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0xbc8cb3,0x125d593,0xf5f593,0x16cde13,0x41c88e33,0x8e3e93,0x40e8663,0x8cde93,0x3fefe93,0x1e3f13,0x1ee8eb3,0x8ebe93,0x20e8a63,0xffcfe93,0x40be8eb3,0xffae0f13,0x1f3f13,0x1ee8eb3,0x15ece63,0xa1463,0x3e8e93,0x66f37,0x1df3c23,0x7f4f3c23,0xf14ec06f,0x20a1063,0x3e3de93,0xe8c63,0x8000a13,0x1300a93,0x1063303,0x1863383,0xe19ff06f,0xb45eb06f]
def kCodeE : List (BitVec 32) := [0xa0537,0xa050513,0xa13,0x1000a93,0x1c03c663,0x231e13,0x3fce7e13,0xae0e33,0xf60e6c83,0xccde93,0x4efe93,0x1dc8cb3,0x635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0xe35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x1635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x1e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x3635e13,0x1fce7e13,0xae0e33,0x400e6583,0x3f35f13,0x139e13,0x1cf6f33,0x2f1e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x5f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0xcf5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0x13f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0x1af5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x21f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x28f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x2ff5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x36f5e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0xbc8cb3,0x125d593,0xf5f593,0x16cde13,0x41c88e33,0x8e3e93,0x40e8663,0x8cde93,0x3fefe93,0x1e3f13,0x1ee8eb3,0x8ebe93,0x20e8a63,0xffcfe93,0x40be8eb3,0xffae0f13,0x1f3f13,0x1ee8eb3,0x15ece63,0xa1463,0x3e8e93,0x66f37,0x5df3023,0x7f4f3c23,0x4680006f,0x20a1063,0x3e3de93,0xe8c63,0x8000a13,0x1300a93,0x1063303,0x1863383,0xe19ff06f,0x9b5d006f]
def kCode (b : Nat) : List (BitVec 32) := if b = 354 then kCodeE else kCodeS
def uCode : List (BitVec 32) := [0x20537,0x42050513,0x3c509a3,0x600f13,0x500593,0x3f35c93,0x139e93,0x1dcecb3,0xff37e13,0xfd8e0e13,0x3ee7eb3,0x1d50023,0x3ee5e33,0x3ee7eb3,0x1d500a3,0x3ee5eb3,0x1d50123,0x835e13,0xffe7e13,0x3ee7eb3,0x1d501a3,0x3ee5e33,0x3ee7eb3,0x1d50223,0x3ee5eb3,0x1d502a3,0x1035e13,0xffe7e13,0x3ee7eb3,0x1d50323,0x3ee5e33,0x3ee7eb3,0x1d503a3,0x3ee5eb3,0x1d50423,0x1835e13,0xffe7e13,0x3ee7eb3,0x1d504a3,0x3ee5e33,0x3ee7eb3,0x1d50523,0x3ee5eb3,0x1d505a3,0x2035e13,0xffe7e13,0x3ee7eb3,0x1d50623,0x3ee5e33,0x3ee7eb3,0x1d506a3,0x3ee5eb3,0x1d50723,0x2835e13,0xffe7e13,0x3ee7eb3,0x1d507a3,0x3ee5e33,0x3ee7eb3,0x1d50823,0x3ee5eb3,0x1d508a3,0x3035e13,0xffe7e13,0x3ee7eb3,0x1d50923,0x3ee5e33,0x3ee7eb3,0x1d509a3,0x3ee5eb3,0x1d50a23,0x38cde13,0x3ee7eb3,0x1d50aa3,0x3ee5e33,0x3ee7eb3,0x1d50b23,0x3ee5eb3,0x1d50ba3,0x3835e13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x1d50c23,0x2be5e33,0x2be7eb3,0x1d50ca3,0x2be5eb3,0x1d50d23,0x7fcfe13,0x7fe4e13,0x2be7eb3,0x1d50da3,0x2be5e33,0x2be7eb3,0x1d50e23,0x2be5eb3,0x1d50ea3,0x7cde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x1d50f23,0x2be5e33,0x2be7eb3,0x1d50fa3,0x2be5eb3,0x3d50023,0xecde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d500a3,0x2be5e33,0x2be7eb3,0x3d50123,0x2be5eb3,0x3d501a3,0x15cde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d50223,0x2be5e33,0x2be7eb3,0x3d502a3,0x2be5eb3,0x3d50323,0x1ccde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d503a3,0x2be5e33,0x2be7eb3,0x3d50423,0x2be5eb3,0x3d504a3,0x23cde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d50523,0x2be5e33,0x2be7eb3,0x3d505a3,0x2be5eb3,0x3d50623,0x2acde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d506a3,0x2be5e33,0x2be7eb3,0x3d50723,0x2be5eb3,0x3d507a3,0x31cde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d50823,0x2be5e33,0x2be7eb3,0x3d508a3,0x2be5eb3,0x3d50923,0x8067]
def kA1 : List (BitVec 32) := [0x3e8e93]
def kNS : List (BitVec 32) := [0xb45eb06f]
def kNE : List (BitVec 32) := [0x9b5d006f]
def kN (b : Nat) : List (BitVec 32) := if b = 354 then kNE else kNS
/-- The R6 kernel and unpacker are installed for instance `b`. -/
def R6KAt (image : Image) (b : Nat) : Prop :=
  (b = 354 ∨ b = 543) ∧ CodeAt image (pcOf (kBase b)) (kCode b) ∧ CodeAt image (pcOf (uBase b)) uCode
/-- The packed table block as 212 little-endian doublewords (two 32-bit entries each). -/
def R6TableW (blk : Nat) (s : MachineState) : Prop :=
  ∀ k, k < 212 → s.getMem (BitVec.ofNat 64 (blk + 8 * k)) =
    BitVec.ofNat 64 (r6Entry (2 * k) + 2 ^ 32 * r6Entry (2 * k + 1))
theorem R6TableW.frame {blk : Nat} {s t : MachineState} {W : Nat → Prop} (h : R6TableW blk s)
    (hf : Frame s t W) (hb : blk + 1696 < 2 ^ 64) (hd : ∀ k, k < 212 → ¬ W (blk + 8 * k)) : R6TableW blk t := by
  intro k hk
  rw [hf.get (by omega) (hd k hk)]
  exact h k hk
theorem r6Entry_lt (f : Nat) (hf : f < 424) : r6Entry f < 2 ^ 32 := by
  have h : ∀ f < 424, r6Entry f < 2 ^ 32 := by decide +kernel
  exact h f hf
theorem extractWord32_pair (e0 e1 : Nat) (h0 : e0 < 2 ^ 32) (h1 : e1 < 2 ^ 32) (j : Nat) (hj : j < 2) :
    extractWord32 (BitVec.ofNat 64 (e0 + 2 ^ 32 * e1)) j = BitVec.ofNat 32 (if j = 0 then e0 else e1) := by
  unfold extractWord32
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have hlt : e0 + 2 ^ 32 * e1 < 2 ^ 64 := by
    have : 2 ^ 32 * e1 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
    omega
  rw [Nat.mod_eq_of_lt hlt]
  interval_cases j
  · simp only [Nat.zero_mul, Nat.shiftRight_zero, if_true]
    rw [Nat.mod_eq_of_lt h0]; omega
  · simp only [Nat.one_mul, Nat.shiftRight_eq_div_pow, one_ne_zero, if_false]
    rw [show (e0 + 2 ^ 32 * e1) / 2 ^ 32 = e1 by omega, Nat.mod_eq_of_lt h1]
/-- The 32-bit entry `f` of the packed block (the operand of the kernel's `lwu`). -/
theorem r6_word {blk : Nat} {s : MachineState} (ht : R6TableW blk s) (hblk : blk % 8 = 0)
    (hb : blk + 1696 < 2 ^ 64) (f : Nat) (hf : f < 424) :
    s.getWord32 (BitVec.ofNat 64 (blk + 4 * f)) = BitVec.ofNat 32 (r6Entry f) := by
  have hlt : blk + 4 * f < 2 ^ 64 := by omega
  unfold MachineState.getWord32
  have ha : alignToDword (BitVec.ofNat 64 (blk + 4 * f)) = BitVec.ofNat 64 (blk + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt hlt, toNat_ofNat_lt (by omega)]
    omega
  have hbo : byteOffset (BitVec.ofNat 64 (blk + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt hlt]; omega
  rw [ha, hbo, ht (f / 2) (by omega),
    extractWord32_pair _ _ (r6Entry_lt _ (by omega)) (r6Entry_lt _ (by omega)) _ (Nat.mod_lt _ (by norm_num))]
  rcases Nat.mod_two_eq_zero_or_one f with h0 | h1
  · rw [h0, if_pos rfl, show 2 * (f / 2) = f by omega]
  · rw [h1, if_neg (by norm_num), show 2 * (f / 2) + 1 = f by omega]
/-! ### Lanes of the packed entries -/
/-- Weight lane (`d_0 + d_1 + d_2`; 256 for INVALID). -/
def eW (f : Nat) : Nat := r6Entry f / 2 ^ 22
/-- Penalty lane (r5 entries: digit sum below 3). -/
def eP (f : Nat) : Nat := r6Entry f / 2 ^ 18 % 16
/-- `d_0 = max` lane (r6 entries). -/
def eD (f : Nat) : Nat := r6Entry f / 2 ^ 14 % 16
/-- Zero-digit lane. -/
def eZ (f : Nat) : Nat := r6Entry f / 2 ^ 8 % 64
/-- Score lane (`wc + 4 safe`). -/
def eS (f : Nat) : Nat := r6Entry f % 256
theorem r6Entry_lanes : ∀ f < 424,
    r6Entry f = eW f * 2 ^ 22 + eP f * 2 ^ 18 + eD f * 2 ^ 14 + eZ f * 2 ^ 8 + eS f ∧
      eW f ≤ 256 ∧ eP f ≤ 1 ∧ eD f ≤ 1 ∧ eZ f ≤ 3 ∧ eS f ≤ 8 := by
  decide +kernel
/-! ### Generic single steps (decode facts are `rfl` on concrete words) -/
theorem step_alu {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32} {i : Instruction}
    {rd : Reg} {op : BinOp} {a b : Src} (hc : CodeAt image pc [w]) (hpc : s.pc = pc)
    (hdec : decodeInstruction w = some i) (hcl : classify i = some (.alu rd op a b)) :
    Steps image s 1 (instructionCycles i)
      ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4)) := by
  have hf : fetch image s = some i := (hc.fetch s hpc).trans hdec
  have hs : ordinaryStep s i = some ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]; rfl
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl (by simp)
theorem step_lwu {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32} {i : Instruction}
    {rd rs : Reg} {off : Word} (hc : CodeAt image pc [w]) (hpc : s.pc = pc)
    (hdec : decodeInstruction w = some i) (hcl : classify i = some (.load .wu rd rs off))
    (hv : accessValid (s.getReg rs + off) 4 = true) :
    Steps image s 1 (instructionCycles i)
      ((s.setReg rd ((s.getWord32 (s.getReg rs + off)).zeroExtend 64)).setPC (s.pc + 4)) := by
  have hf : fetch image s = some i := (hc.fetch s hpc).trans hdec
  have hs : ordinaryStep s i =
      some ((s.setReg rd ((s.getWord32 (s.getReg rs + off)).zeroExtend 64)).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, LoadKind.width, hv, if_true, LoadKind.read]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl (by simp)
/-- One table lookup of the half test: `shift t3, src, sh ; andi t3, t3, mask ; add t3, t3, a0 ;
lwu t4, off(t3) ; add acc, acc, t4` (decode facts of the five concrete words are `rfl`). -/
theorem look5 {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3, w4]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    (hv : accessValid (((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10 + off) 4 = true) :
    let base := ((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10
    let ld := (s.getWord32 (base + off)).zeroExtend 64
    ∃ t, Steps image s 5 5 t ∧ t.pc = s.pc + 20 ∧ t.getReg .x28 = base ∧ t.getReg .x29 = ld ∧
      t.getReg acc = s.getReg acc + ld ∧ RegsExcept s t [.x28, .x29, acc] ∧ Frame s t (fun _ => False) := by
  intro base ld
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have spc : ∀ (x : MachineState) (v : Word), (x.setPC v).pc = v := fun _ _ => rfl
  have sreg : ∀ (x : MachineState) (r : Reg) (v : Word), (x.setReg r v).pc = x.pc := by
    intro x r v; cases r <;> rfl
  have w32p : ∀ (x : MachineState) (v a : Word), (x.setPC v).getWord32 a = x.getWord32 a := fun _ _ _ => rfl
  have w32r : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getWord32 a = x.getWord32 a := by
    intro x r v a; cases r <;> rfl
  have memp : ∀ (x : MachineState) (v a : Word), (x.setPC v).getMem a = x.getMem a := fun _ _ _ => rfl
  have memr : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getMem a = x.getMem a := by
    intro x r v a; cases r <;> rfl
  have gp : ∀ (x : MachineState) (v : Word) (r : Reg), (x.setPC v).getReg r = x.getReg r := getReg_setPC'
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have c1 := hc.tail
  have c2 := c1.tail
  have c3 := c2.tail
  have c4 := c3.tail
  have hx28 : (.x28 : Reg) ≠ .x0 := by decide
  have hx29 : (.x29 : Reg) ≠ .x0 := by decide
  have st0 := step_alu (hd hc) hpc hd0 hc0
  generalize hu1 : (s.setReg .x28 (op0.eval ((Src.reg src).eval s) ((Src.imm sh).eval s))).setPC (s.pc + 4) = u1
    at st0
  have p1 : u1.pc = pc + 4 := by rw [← hu1, spc, hpc]
  have r1 : ∀ q, q ≠ .x28 → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, gp, gne _ _ _ _ hq]
  have g1 : u1.getReg .x28 = op0.eval (s.getReg src) sh := by rw [← hu1, gp, geq _ _ _ hx28]; rfl
  have st1 := step_alu (hd c1) p1 hd1 hc1
  generalize hu2 : (u1.setReg .x28 (BinOp.and.eval ((Src.reg .x28).eval u1) ((Src.imm mask).eval u1))).setPC
    (u1.pc + 4) = u2 at st1
  have p2 : u2.pc = pc + 4 + 4 := by rw [← hu2, spc, p1]
  have r2 : ∀ q, q ≠ .x28 → u2.getReg q = s.getReg q := fun q hq => by rw [← hu2, gp, gne _ _ _ _ hq, r1 q hq]
  have g2 : u2.getReg .x28 = op0.eval (s.getReg src) sh &&& mask := by
    rw [← hu2, gp, geq _ _ _ hx28]; show u1.getReg .x28 &&& mask = _; rw [g1]
  have st2 := step_alu (hd c2) p2 hd2 hc2
  generalize hu3 : (u2.setReg .x28 (BinOp.add.eval ((Src.reg .x28).eval u2) ((Src.reg .x10).eval u2))).setPC
    (u2.pc + 4) = u3 at st2
  have p3 : u3.pc = pc + 4 + 4 + 4 := by rw [← hu3, spc, p2]
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = s.getReg q := fun q hq => by rw [← hu3, gp, gne _ _ _ _ hq, r2 q hq]
  have g3 : u3.getReg .x28 = base := by
    rw [← hu3, gp, geq _ _ _ hx28]; show u2.getReg .x28 + u2.getReg .x10 = base; rw [g2, r2 .x10 (by decide)]
  have m3 : ∀ a, u3.getWord32 a = s.getWord32 a := fun a => by
    rw [← hu3, w32p, w32r, ← hu2, w32p, w32r, ← hu1, w32p, w32r]
  have hv3 : accessValid (u3.getReg .x28 + off) 4 = true := by rw [g3]; exact hv
  have st3 := step_lwu (hd c3) p3 hd3 hc3 hv3
  generalize hu4 : (u3.setReg .x29 ((u3.getWord32 (u3.getReg .x28 + off)).zeroExtend 64)).setPC (u3.pc + 4) = u4
    at st3
  have p4 : u4.pc = pc + 4 + 4 + 4 + 4 := by rw [← hu4, spc, p3]
  have g4 : u4.getReg .x29 = ld := by rw [← hu4, gp, geq _ _ _ hx29, g3, m3]
  have g4' : u4.getReg .x28 = base := by rw [← hu4, gp, gne _ _ _ _ (by decide), g3]
  have r4 : ∀ q, q ≠ .x28 → q ≠ .x29 → u4.getReg q = s.getReg q := fun q hq hq' => by
    rw [← hu4, gp, gne _ _ _ _ hq', r3 q hq]
  have st4 := step_alu (hd c4) p4 hd4 hc4
  generalize hu5 : (u4.setReg acc (BinOp.add.eval ((Src.reg acc).eval u4) ((Src.reg .x29).eval u4))).setPC
    (u4.pc + 4) = u5 at st4
  refine ⟨u5, ((((st0.trans st1).trans st2).trans st3).trans st4).of_eq rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcy
  · rw [← hu5, spc, p4, hpc]; bv_omega
  · rw [← hu5, gp, gne _ _ _ _ (Ne.symm hacc.2.1), g4']
  · rw [← hu5, gp, gne _ _ _ _ (Ne.symm hacc.2.2), g4]
  · rw [← hu5, gp, geq _ _ _ hacc.1]; show u4.getReg acc + u4.getReg .x29 = _; rw [g4, r4 acc hacc.2.1 hacc.2.2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hu5, gp, gne _ _ _ _ hr.2.2, r4 r hr.1 hr.2.1]
  · intro A _ _
    rw [← hu5, memp, memr, ← hu4, memp, memr, ← hu3, memp, memr, ← hu2, memp, memr, ← hu1, memp, memr]
/-! ### Field extraction and table addressing -/
theorem shr_and_mul4 (x : Word) (S w : Nat) (h : S + 2 + w ≤ 64) :
    (x >>> S) &&& BitVec.ofNat 64 (4 * (2 ^ w - 1)) = BitVec.ofNat 64 (4 * (x.toNat / 2 ^ (S + 2) % 2 ^ w)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : 4 * (2 ^ w - 1) = (2 ^ w - 1) * 2 ^ 2 := by ring
  have e2 : 4 * (x.toNat / 2 ^ (S + 2) % 2 ^ w) = (x.toNat / 2 ^ (S + 2) % 2 ^ w) * 2 ^ 2 := by ring
  rw [e1, e2]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.testBit_toNat]
  by_cases h2 : 2 ≤ i
  · by_cases hw : i - 2 < w
    · simp only [h2, hw, decide_true, Bool.true_and, Bool.and_true]
      congr 1; omega
    · simp [h2, hw]
  · simp [h2]
theorem shl2_and_mul4 (x : Word) (w : Nat) (h : 2 + w ≤ 64) :
    (x <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ w - 1)) = BitVec.ofNat 64 (4 * (x.toNat % 2 ^ w)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : 4 * (2 ^ w - 1) = (2 ^ w - 1) * 2 ^ 2 := by ring
  have e2 : 4 * (x.toNat % 2 ^ w) = (x.toNat % 2 ^ w) * 2 ^ 2 := by ring
  rw [e1, e2]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, BitVec.testBit_toNat]
  by_cases h2 : 2 ≤ i
  · by_cases hw : i - 2 < w
    · simp only [h2, hw, decide_true, Bool.true_and, Bool.and_true, Bool.not_false]
      simp [show ¬ i < 2 by omega]
    · simp [h2, hw]
  · simp [h2, show i < 2 by omega]
/-- A table lookup with a known field value: the accumulator gains the packed entry `f`. -/
theorem look5_entry {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3, w4]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    {blk r f : Nat} (ht : R6TableW blk s) (hblk : blk % 8 = 0) (hb : blk + 1696 < 2 ^ 24) (hf : f < 424)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = s.pc + 20 ∧ t.getReg .x29 = BitVec.ofNat 64 (r6Entry f) ∧
      t.getReg acc = s.getReg acc + BitVec.ofNat 64 (r6Entry f) ∧ RegsExcept s t [.x28, .x29, acc] ∧
      Frame s t (fun _ => False) := by
  have haddr : (op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off = BitVec.ofNat 64 (blk + 4 * f) := by
    rw [hbase, h10, hoff]
  have hv : accessValid ((op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off) 4 = true := by
    rw [haddr]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show blk + 4 * f < 2 ^ 64 by omega)]
    omega
  obtain ⟨t, st, pt, _, g29, gacc, rt, ft⟩ := look5 hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hd4 hc4 hcy hacc hsrc hv
  have hw : (s.getWord32 (BitVec.ofNat 64 (blk + 4 * f))).zeroExtend 64 = BitVec.ofNat 64 (r6Entry f) := by
    rw [r6_word ht hblk (by omega) f hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
    have := r6Entry_lt f hf
    have h64 : r6Entry f < 2 ^ 64 := by omega
    simp only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h64]
  refine ⟨t, st, pt, ?_, ?_, rt, ft⟩
  · rw [g29, haddr, hw]
  · rw [gacc, haddr, hw]
theorem lo_field (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 0 64).toNat / 2 ^ S % 2 ^ w = v.toNat / 2 ^ S % 2 ^ w := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, show i + S < 64 by omega]
  · simp [hi]
/-! ### Spec fields vs raw half bits -/
theorem topCode_testBit (v : Digest) (j : Nat) :
    (T3.topCode v).testBit j = (v.toNat.testBit j ^^ decide (56 ≤ j ∧ j < 119)) := by
  unfold T3.topCode T3.topFlip T3.topMask
  rw [BitVec.toNat_xor, Nat.testBit_xor, BitVec.toNat_ofNat]
  congr 1
  by_cases hj : j < 128
  · rw [Nat.mod_eq_of_lt (by norm_num), show (2 : Nat) ^ 119 - 2 ^ 56 = (2 ^ 63 - 1) * 2 ^ 56 by norm_num,
      ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : 56 ≤ j
    · simp only [h1, decide_true, Bool.true_and]
      by_cases h2 : j < 119
      · simp [h2, show j - 56 < 63 by omega]
      · simp [h2, show ¬ j - 56 < 63 by omega]
    · simp [h1]
  · have hv : v.toNat.testBit j = false := by
      apply Nat.testBit_eq_false_of_lt
      calc v.toNat < 2 ^ 128 := v.isLt
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt (by norm_num)]
    simp only [show ¬ (56 ≤ j ∧ j < 119) by omega, decide_false]
    apply Nat.testBit_eq_false_of_lt
    calc 2 ^ 119 - 2 ^ 56 < 2 ^ 119 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem r6Raw_eq (v : Digest) (g : Nat) (hg : g ≤ 7) :
    T3.r6Raw v g = v.toNat / 2 ^ T3.r6Shift g % 256 := by
  unfold T3.r6Raw
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 by norm_num]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, topCode_testBit]
  by_cases hi : i < 8
  · have : ¬ (56 ≤ i + T3.r6Shift g ∧ i + T3.r6Shift g < 119) := by
      unfold T3.r6Shift; split_ifs <;> omega
    simp [hi, this]
  · simp [hi]
theorem r5Rank_eq (v : Digest) (q : Nat) (hq : 8 ≤ q ∧ q ≤ 16) :
    T3.r5Rank v q = 127 - v.toNat / 2 ^ (7 * q) % 128 := by
  unfold T3.r5Rank
  have key : T3.topCode v / 2 ^ (7 * q) % 2 ^ 7 = (v.toNat / 2 ^ (7 * q) % 2 ^ 7) ^^^ (2 ^ 7 - 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, topCode_testBit, Nat.testBit_xor,
      Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 7
    · simp [hi, show 56 ≤ i + 7 * q ∧ i + 7 * q < 119 by omega]
    · simp [hi]
  change T3.topCode v / 2 ^ (7 * q) % 2 ^ 7 = 127 - v.toNat / 2 ^ (7 * q) % 2 ^ 7
  rw [key]
  have hlt : v.toNat / 2 ^ (7 * q) % 2 ^ 7 < 128 := Nat.mod_lt _ (by norm_num)
  generalize v.toNat / 2 ^ (7 * q) % 2 ^ 7 = n at hlt ⊢
  have : ∀ n < 128, n ^^^ (2 ^ 7 - 1) = 127 - n := by decide
  exact this n hlt
theorem decode_length {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.length = 52 := by
  unfold WCT9.CanonicalPolicy.decode WCT9.CanonicalPolicy.normalLayer T3.decode at h
  simp only [if_true] at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    subst h
    simp [T3.dataDigits, T3.dataCount]
/-! ### Lanes of valid entries in digit terms -/
/-- r6 entry of rank `r` (`r < 216`): table index `40 + r`. -/
theorem lanes6 : ∀ r < 216,
    eW (40 + r) = r % 6 + r / 6 % 6 + r / 36 ∧ eZ (40 + r) = r6Zeros (r % 6) (r / 6 % 6) (r / 36) ∧
      eS (40 + r) = r6Score 5 (r % 6) (r / 6 % 6) (r / 36) ∧ eD (40 + r) = (if r % 6 = 5 then 1 else 0) ∧
      eP (40 + r) = 0 := by
  decide +kernel
/-- r5 entry of raw field `raw7 ≥ 3` (rank `127 - raw7 < 125`): table index `296 + raw7`. -/
theorem lanes5 : ∀ raw < 128, 3 ≤ raw →
    eW (296 + raw) = (127 - raw) % 5 + (127 - raw) / 5 % 5 + (127 - raw) / 25 ∧
      eZ (296 + raw) = r6Zeros ((127 - raw) % 5) ((127 - raw) / 5 % 5) ((127 - raw) / 25) ∧
      eS (296 + raw) = r6Score 4 ((127 - raw) % 5) ((127 - raw) / 5 % 5) ((127 - raw) / 25) ∧
      eP (296 + raw) = (if (127 - raw) % 5 + (127 - raw) / 5 % 5 + (127 - raw) / 25 < 3 then 1 else 0) ∧
      eD (296 + raw) = 0 := by
  decide +kernel
/-! ### Regrouping the 51 data chains into 17 triples -/
theorem sum_triples (f : Nat → Nat) (n : Nat) :
    ∑ i ∈ Finset.range (3 * n), f i = ∑ g ∈ Finset.range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
theorem length_filter_range' (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
/-- `wordCredit` of a top word as a sum over 17 triples plus the checksum term. -/
theorem wordCredit_top (ds : List Nat) :
    WCT9.wordCredit 0 ds = ∑ g ∈ Finset.range 17,
      ((if ds.getD (3 * g) 0 + 1 = T3.maxDigit 0 (3 * g) then 1 else 0) +
       (if ds.getD (3 * g + 1) 0 + 1 = T3.maxDigit 0 (3 * g + 1) then 1 else 0) +
       (if ds.getD (3 * g + 2) 0 + 1 = T3.maxDigit 0 (3 * g + 2) then 1 else 0)) +
      (if ds.getD 51 0 + 1 = 7 then 1 else 0) := by
  unfold WCT9.wordCredit
  rw [length_filter_range', show T3.chainCount 0 = 3 * 17 + 1 from rfl, Finset.sum_range_succ, sum_triples]
  rfl
theorem safe_top_mid (ds : List Nat) (g : Nat) (j : Nat) (hj : j = 1 ∨ j = 2) :
    WCT9.safeZeroCopy 0 ds (3 * g + j) ↔
      ds.getD (3 * g + j) 0 = T3.maxDigit 0 (3 * g + j) ∧ ds.getD (3 * g + j - 1) 0 = T3.maxDigit 0 (3 * g + j - 1) := by
  unfold WCT9.safeZeroCopy
  constructor
  · rintro ⟨h1, h2 | ⟨h3, _⟩ | ⟨_, _, h4⟩⟩
    · omega
    · exact absurd rfl h3
    · exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, h2⟩)⟩
theorem safe_top_first (ds : List Nat) (g : Nat) :
    WCT9.safeZeroCopy 0 ds (3 * g) ↔ g = 0 ∧ ds.getD 0 0 = 5 := by
  unfold WCT9.safeZeroCopy
  constructor
  · rintro ⟨h1, h2 | ⟨h3, _⟩ | ⟨_, h5, _⟩⟩
    · have hg : g = 0 := by omega
      subst hg; exact ⟨rfl, by simpa [T3.maxDigit] using h1⟩
    · exact absurd rfl h3
    · omega
  · rintro ⟨rfl, h⟩
    exact ⟨by simpa [T3.maxDigit] using h, Or.inl rfl⟩
theorem safe_top_last (ds : List Nat) : ¬ WCT9.safeZeroCopy 0 ds 51 := by
  unfold WCT9.safeZeroCopy
  rintro ⟨_, h2 | ⟨h3, _⟩ | ⟨_, h5, _⟩⟩
  · omega
  · exact h3 rfl
  · omega
/-- `savedCopies` of a top word: the i = 0 copy plus the in-triple copies at offsets 1 and 2. -/
theorem savedCopies_top (ds : List Nat) :
    WCT9.savedCopies 0 ds = (if ds.getD 0 0 = 5 then 1 else 0) + ∑ g ∈ Finset.range 17,
      ((if ds.getD (3 * g) 0 = T3.maxDigit 0 (3 * g) ∧ ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1)
          then 1 else 0) +
       (if ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1) ∧ ds.getD (3 * g + 2) 0 = T3.maxDigit 0 (3 * g + 2)
          then 1 else 0)) := by
  unfold WCT9.savedCopies
  rw [length_filter_range', show T3.chainCount 0 = 3 * 17 + 1 from rfl, Finset.sum_range_succ, sum_triples,
    if_neg (safe_top_last ds), add_zero]
  have h1 : ∀ g, (if WCT9.safeZeroCopy 0 ds (3 * g + 1) then 1 else 0) =
      (if ds.getD (3 * g) 0 = T3.maxDigit 0 (3 * g) ∧ ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1)
        then 1 else 0) := fun g => by
    rw [if_congr ((safe_top_mid ds g 1 (Or.inl rfl)).trans and_comm) rfl rfl]; rfl
  have h2 : ∀ g, (if WCT9.safeZeroCopy 0 ds (3 * g + 2) then 1 else 0) =
      (if ds.getD (3 * g + 1) 0 = T3.maxDigit 0 (3 * g + 1) ∧ ds.getD (3 * g + 2) 0 = T3.maxDigit 0 (3 * g + 2)
        then 1 else 0) := fun g => by
    rw [if_congr ((safe_top_mid ds g 2 (Or.inr rfl)).trans and_comm) rfl rfl]; rfl
  have h0 : ∀ g, (if WCT9.safeZeroCopy 0 ds (3 * g) then 1 else 0) =
      (if g = 0 ∧ ds.getD 0 0 = 5 then 1 else 0) := fun g => if_congr (safe_top_first ds g) rfl rfl
  simp only [h0, h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun g => if g = 0 ∧ ds.getD 0 0 = 5 then 1 else 0)]
  simp only [Nat.succ_ne_zero, false_and, if_false, Finset.sum_const_zero, zero_add, true_and]
  ring
theorem filter_length_sum (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length = ∑ i ∈ Finset.range l.length, if p (l.getD i 0) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.filter_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    by_cases h : p a <;> simp [h, ih] <;> ring
/-- Zero digits of a 52-digit top word: 17 triples plus the checksum. -/
theorem zeros_top (ds : List Nat) (hl : ds.length = 52) :
    (ds.filter (· = 0)).length = ∑ g ∈ Finset.range 17,
      ((if ds.getD (3 * g) 0 = 0 then 1 else 0) + (if ds.getD (3 * g + 1) 0 = 0 then 1 else 0) +
       (if ds.getD (3 * g + 2) 0 = 0 then 1 else 0)) + (if ds.getD 51 0 = 0 then 1 else 0) := by
  rw [filter_length_sum, hl, show (52 : Nat) = 3 * 17 + 1 from rfl, Finset.sum_range_succ, sum_triples]
  simp only [decide_eq_true_eq]
/-- The R6 dispatch penalty: the four penalised r5 rows 8, 10, 11, 12. -/
theorem penalty_top (ds : List Nat) :
    WCT9.topDispatchPenalty ds =
      (if ds.getD 24 0 + ds.getD 25 0 + ds.getD 26 0 < 3 then 1 else 0) +
      (if ds.getD 30 0 + ds.getD 31 0 + ds.getD 32 0 < 3 then 1 else 0) +
      (if ds.getD 33 0 + ds.getD 34 0 + ds.getD 35 0 < 3 then 1 else 0) +
      (if ds.getD 36 0 + ds.getD 37 0 + ds.getD 38 0 < 3 then 1 else 0) := by
  unfold WCT9.topDispatchPenalty
  rw [length_filter_range']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
/-- A decoded top word: its digits are the data digits followed by the checksum. -/
theorem decode_top_eq {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    T3.topRanksValid v = true ∧ (T3.dataDigits 0 v).sum ≤ 153 ∧ 153 - (T3.dataDigits 0 v).sum < 8 ∧
      ds = T3.dataDigits 0 v ++ [153 - (T3.dataDigits 0 v).sum] := by
  unfold WCT9.CanonicalPolicy.decode WCT9.CanonicalPolicy.normalLayer T3.decode at h
  simp only [if_true] at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h
    exact ⟨h2.1, h2.2.1, h2.2.2, h.symm⟩
theorem ds_getD_data {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) (i : Nat)
    (hi : i < 51) : ds.getD i 0 = T3.coreDigit 0 v i := by
  obtain ⟨_, _, _, rfl⟩ := decode_top_eq h
  rw [List.getD_append _ _ _ _ (by simp [T3.dataDigits, T3.dataCount]; omega)]
  simp [T3.dataDigits, T3.dataCount, List.getD_eq_getElem?_getD, hi]
theorem ds_getD_51 {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.getD 51 0 = 153 - (T3.dataDigits 0 v).sum := by
  obtain ⟨_, _, _, rfl⟩ := decode_top_eq h
  rw [List.getD_append_right _ _ _ _ (by simp [T3.dataDigits, T3.dataCount])]
  simp [T3.dataDigits, T3.dataCount]

/-! ### Kernel group indices (table entry read for group `j` of a half `v`) -/
def gIdx (v : Digest) (j : Nat) : Nat :=
  if j = 0 then v.toNat % 256
  else if j < 7 then 40 + v.toNat / 2 ^ (8 * j) % 256
  else if j = 7 then 40 + v.toNat / 2 ^ 119 % 256
  else 296 + v.toNat / 2 ^ (7 * j) % 128
theorem gIdx_lt (v : Digest) (j : Nat) : gIdx v j < 424 := by
  unfold gIdx; split_ifs <;> omega
/-- Per-entry facts over the whole block. -/
theorem e_valid0 : ∀ raw < 256, (eW raw = 256 ↔ raw < 40) := by decide +kernel
theorem e_valid6 : ∀ raw < 256, (eW (40 + raw) = 256 ↔ 216 ≤ raw) := by decide +kernel
theorem e_valid5 : ∀ raw < 128, (eW (296 + raw) = 256 ↔ raw < 3) := by decide +kernel
theorem e_r6P : ∀ f < 296, eP f = 0 := by decide +kernel
theorem e_r5D : ∀ f < 424, 296 ≤ f → eD f = 0 := by decide +kernel
theorem topSpare_eq (v : Digest) : T3.topSpare v = v.toNat / 2 ^ 127 % 2 := by
  unfold T3.topSpare
  have h := topCode_testBit v 127
  simp only [show ¬ (56 ≤ 127 ∧ 127 < 119) by omega, decide_false, Bool.xor_false] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h
  have h1 := Nat.mod_two_eq_zero_or_one (T3.topCode v / 2 ^ 127)
  have h2 := Nat.mod_two_eq_zero_or_one (v.toNat / 2 ^ 127)
  simp only [decide_eq_decide] at h
  omega
/-- Digits of group `j` (chains `3 j + k`). -/
theorem coreDigit_r6g (v : Digest) (j k : Nat) (hj : j < 8) (hk : k < 3) :
    T3.coreDigit 0 v (3 * j + k) = T3.r6Rank v j / 6 ^ k % 6 := by
  unfold T3.coreDigit
  simp only [if_true, show 3 * j + k < 24 by omega, show (3 * j + k) / 3 = j by omega,
    show (3 * j + k) % 3 = k by omega]
theorem coreDigit_r5g (v : Digest) (j k : Nat) (hj : 8 ≤ j ∧ j < 17) (hk : k < 3) :
    T3.coreDigit 0 v (3 * j + k) = T3.r5Rank v j / 5 ^ k % 5 := by
  unfold T3.coreDigit
  simp only [if_true, show ¬ 3 * j + k < 24 by omega, show 3 * j + k < 51 by omega, if_false,
    show (3 * j + k) / 3 = j by omega, show (3 * j + k) % 3 = k by omega]
/-- The kernel index of an r6 group is `40 + rank` and its validity is `rank < 216` (with `rank` the spec rank). -/
theorem gIdx_r6 (v : Digest) (j : Nat) (hj : j < 8) :
    (T3.r6Valid v j = true ↔ eW (gIdx v j) ≠ 256) ∧
      (T3.r6Valid v j = true → gIdx v j = 40 + T3.r6Rank v j ∧ T3.r6Rank v j < 216) := by
  have hr := r6Raw_eq v j (by omega)
  unfold T3.r6Valid T3.r6Rank gIdx
  by_cases h0 : j = 0
  · subst h0
    simp only [if_true, decide_eq_true_eq]
    rw [hr, show T3.r6Shift 0 = 0 from rfl, pow_zero, Nat.div_one]
    have hlt : v.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have := e_valid0 _ hlt
    constructor
    · constructor
      · intro h; rw [Ne, this]; omega
      · intro h; rw [Ne, this] at h; omega
    · intro h; constructor <;> omega
  · have hsh : T3.r6Shift j = if j = 7 then 119 else 8 * j := rfl
    simp only [h0, if_false, decide_eq_true_eq]
    rw [hr, hsh]
    by_cases h7 : j = 7
    · subst h7
      simp only [if_true, show ¬ (7 : Nat) < 7 by omega, if_false]
      have hlt : v.toNat / 2 ^ 119 % 256 < 256 := Nat.mod_lt _ (by norm_num)
      have := e_valid6 _ hlt
      refine ⟨⟨fun h => by rw [Ne, this]; omega, fun h => by rw [Ne, this] at h; omega⟩, fun h => ⟨by simp, h⟩⟩
    · simp only [h7, if_false, show j < 7 by omega, if_true]
      have hlt : v.toNat / 2 ^ (8 * j) % 256 < 256 := Nat.mod_lt _ (by norm_num)
      have := e_valid6 _ hlt
      refine ⟨⟨fun h => by rw [Ne, this]; omega, fun h => by rw [Ne, this] at h; omega⟩, fun h => ⟨by simp, h⟩⟩
theorem gIdx_r5 (v : Digest) (j : Nat) (hj : 8 ≤ j ∧ j < 17) :
    (T3.r5Rank v j < 125 ↔ eW (gIdx v j) ≠ 256) ∧ gIdx v j = 296 + (127 - T3.r5Rank v j) ∧
      T3.r5Rank v j ≤ 127 := by
  have hr := r5Rank_eq v j (by omega)
  have hlt : v.toNat / 2 ^ (7 * j) % 128 < 128 := Nat.mod_lt _ (by norm_num)
  unfold gIdx
  simp only [show j ≠ 0 by omega, show ¬ j < 7 by omega, show j ≠ 7 by omega, if_false]
  have := e_valid5 _ hlt
  rw [hr]
  refine ⟨⟨fun h => by rw [Ne, this]; omega, fun h => by rw [Ne, this] at h; omega⟩, by omega, by omega⟩

theorem valid_groups {v : Digest} (hv : T3.topRanksValid v = true) :
    T3.topSpare v = 0 ∧ (∀ j < 8, T3.r6Valid v j = true) ∧ (∀ j, 8 ≤ j → j < 17 → T3.r5Rank v j < 125) := by
  unfold T3.topRanksValid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := hv
  refine ⟨h1, h2, fun j hj1 hj2 => ?_⟩
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 9 ∧ j = 8 + i := ⟨j - 8, by omega, by omega⟩
  simpa using h3 (8 + i) ⟨i, hi, by ring⟩
theorem maxDigit_r6 (i : Nat) (hi : i < 24) : T3.maxDigit 0 i = 5 := by
  simp [T3.maxDigit, hi]
theorem maxDigit_r5 (i : Nat) (hi : 24 ≤ i ∧ i < 51) : T3.maxDigit 0 i = 4 := by
  simp [T3.maxDigit, show ¬ i < 24 by omega, hi.2]
/-- Lanes of the entry read for group `j` of a valid half, in digit terms. -/
theorem group_lanes {v : Digest} (hv : T3.topRanksValid v = true) (j : Nat) (hj : j < 17) :
    let d := T3.coreDigit 0 v
    let m := T3.maxDigit 0
    eW (gIdx v j) = d (3 * j) + d (3 * j + 1) + d (3 * j + 2) ∧
    eZ (gIdx v j) = (if d (3 * j) = 0 then 1 else 0) + (if d (3 * j + 1) = 0 then 1 else 0) +
      (if d (3 * j + 2) = 0 then 1 else 0) ∧
    eS (gIdx v j) = (if d (3 * j) + 1 = m (3 * j) then 1 else 0) + (if d (3 * j + 1) + 1 = m (3 * j + 1) then 1 else 0) +
      (if d (3 * j + 2) + 1 = m (3 * j + 2) then 1 else 0) +
      4 * ((if d (3 * j) = m (3 * j) ∧ d (3 * j + 1) = m (3 * j + 1) then 1 else 0) +
        (if d (3 * j + 1) = m (3 * j + 1) ∧ d (3 * j + 2) = m (3 * j + 2) then 1 else 0)) ∧
    eP (gIdx v j) = (if 8 ≤ j ∧ d (3 * j) + d (3 * j + 1) + d (3 * j + 2) < 3 then 1 else 0) ∧
    (j = 0 → eD (gIdx v 0) = if d 0 = 5 then 1 else 0) := by
  intro d m
  obtain ⟨_, h6, h5⟩ := valid_groups hv
  by_cases hj8 : j < 8
  · obtain ⟨hidx, hr⟩ := (gIdx_r6 v j hj8).2 (h6 j hj8)
    have c0 := coreDigit_r6g v j 0 hj8 (by norm_num)
    have c1 := coreDigit_r6g v j 1 hj8 (by norm_num)
    have c2 := coreDigit_r6g v j 2 hj8 (by norm_num)
    simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
    have m0 := maxDigit_r6 (3 * j) (by omega)
    have m1 := maxDigit_r6 (3 * j + 1) (by omega)
    have m2 := maxDigit_r6 (3 * j + 2) (by omega)
    generalize T3.r6Rank v j = r at hidx hr c0 c1 c2
    obtain ⟨hW, hZ, hS, hD, hP⟩ := lanes6 r hr
    have e36 : r / 6 ^ 2 % 6 = r / 36 := by norm_num; omega
    refine ⟨?_, ?_, ?_, ?_, fun hj0 => ?_⟩
    all_goals try (simp only [d, m, c0, c1, c2, m0, m1, m2, hidx, hW, hZ, hS, hP, e36, show ¬ 8 ≤ j by omega,
      false_and, if_false] <;> first | trivial | rfl | (unfold r6Score r6Zeros; rfl))
    subst hj0
    have c0' : T3.coreDigit 0 v 0 = r % 6 := by simpa using c0
    have hidx' : gIdx v 0 = 40 + r := by simpa using hidx
    simp only [d, c0', hidx', hD]
  · obtain ⟨hiff, hidx, hle⟩ := gIdx_r5 v j ⟨by omega, hj⟩
    have hr := h5 j (by omega) hj
    have c0 := coreDigit_r5g v j 0 ⟨by omega, hj⟩ (by norm_num)
    have c1 := coreDigit_r5g v j 1 ⟨by omega, hj⟩ (by norm_num)
    have c2 := coreDigit_r5g v j 2 ⟨by omega, hj⟩ (by norm_num)
    simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
    have m0 := maxDigit_r5 (3 * j) (by omega)
    have m1 := maxDigit_r5 (3 * j + 1) (by omega)
    have m2 := maxDigit_r5 (3 * j + 2) (by omega)
    generalize T3.r5Rank v j = r at hidx hr hle c0 c1 c2
    obtain ⟨hW, hZ, hS, hP, hD⟩ := lanes5 (127 - r) (by omega) (by omega)
    have e127 : 127 - (127 - r) = r := by omega
    have e25 : r / 5 ^ 2 % 5 = r / 25 := by norm_num; omega
    rw [e127] at hW hZ hS hP
    refine ⟨?_, ?_, ?_, ?_, fun hj0 => by omega⟩
    all_goals (simp only [d, m, c0, c1, c2, m0, m1, m2, hidx, hW, hZ, hS, hP, e25, show 8 ≤ j by omega,
      true_and] <;> first | trivial | rfl | (unfold r6Score r6Zeros; rfl))
theorem sum_map_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
/-! ### Lane sums over the 17 groups -/
def LW (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eW (gIdx v j)
def LP (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eP (gIdx v j)
def LD (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eD (gIdx v j)
def LZ (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eZ (gIdx v j)
def LS (v : Digest) : Nat := ∑ j ∈ Finset.range 17, eS (gIdx v j)
/-- Penalty lanes of the four penalised r5 groups (the kernel's `a1`). -/
def LPen (v : Digest) : Nat := eP (gIdx v 8) + eP (gIdx v 10) + eP (gIdx v 11) + eP (gIdx v 12)
theorem dataDigits_sum_LW {v : Digest} (hv : T3.topRanksValid v = true) : (T3.dataDigits 0 v).sum = LW v := by
  unfold T3.dataDigits LW
  rw [sum_map_range, show T3.dataCount 0 = 3 * 17 from rfl, sum_triples]
  exact Finset.sum_congr rfl (fun j hj => ((group_lanes hv j (Finset.mem_range.1 hj)).1).symm)

theorem decode_some_iff (v : Digest) (ds : List Nat) :
    WCT9.CanonicalPolicy.decode 0 v = some ds ↔
      T3.topRanksValid v = true ∧ LW v ≤ 153 ∧ 153 - LW v < 8 ∧ ds = T3.dataDigits 0 v ++ [153 - LW v] := by
  constructor
  · intro h
    obtain ⟨hv, h1, h2, rfl⟩ := decode_top_eq h
    rw [dataDigits_sum_LW hv] at h1 h2 ⊢
    exact ⟨hv, h1, h2, rfl⟩
  · rintro ⟨hv, h1, h2, rfl⟩
    unfold WCT9.CanonicalPolicy.decode WCT9.CanonicalPolicy.normalLayer T3.decode
    have hlt : ¬ v.toNat ≥ 2 ^ T3.encodedBits 0 := by
      have := v.isLt; unfold T3.encodedBits; omega
    simp only [if_true, hlt, if_false, dataDigits_sum_LW hv, show T3.target 0 = 153 from rfl]
    rw [if_pos ⟨hv, h1, h2⟩]
theorem invalid_LW {v : Digest} (hs : v.toNat / 2 ^ 127 % 2 = 0) (hv : T3.topRanksValid v = false) :
    256 ≤ LW v := by
  have hex : ∃ j < 17, eW (gIdx v j) = 256 := by
    by_contra hne
    push Not at hne
    have : T3.topRanksValid v = true := by
      unfold T3.topRanksValid
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range']
      refine ⟨⟨by rw [topSpare_eq]; exact hs, fun j hj => ?_⟩, ?_⟩
      · exact (gIdx_r6 v j hj).1.2 (hne j (by omega))
      · rintro q ⟨i, hi, rfl⟩
        exact (gIdx_r5 v (8 + 1 * i) ⟨by omega, by omega⟩).1.2 (hne _ (by omega))
    rw [this] at hv; cases hv
  obtain ⟨j, hj, h⟩ := hex
  unfold LW
  calc 256 = eW (gIdx v j) := h.symm
    _ ≤ ∑ j ∈ Finset.range 17, eW (gIdx v j) :=
      Finset.single_le_sum (f := fun j => eW (gIdx v j)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
theorem zeros_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    (ds.filter (· = 0)).length = LZ v + (if 153 - LW v = 0 then 1 else 0) := by
  obtain ⟨hv, _, _, hds⟩ := (decode_some_iff v ds).1 h
  rw [zeros_top ds (decode_length h), ds_getD_51 h, dataDigits_sum_LW hv]
  have hZ : ∀ j ∈ Finset.range 17, ((if ds.getD (3 * j) 0 = 0 then 1 else 0) +
      (if ds.getD (3 * j + 1) 0 = 0 then 1 else 0) + (if ds.getD (3 * j + 2) 0 = 0 then 1 else 0)) =
      eZ (gIdx v j) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [(group_lanes hv j hj').2.1, ds_getD_data h _ (by omega), ds_getD_data h _ (by omega),
      ds_getD_data h _ (by omega)]
  rw [Finset.sum_congr rfl hZ]
  rfl
theorem reward_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.reward 0 ds = LS v + 4 * eD (gIdx v 0) + (if 153 - LW v = 6 then 1 else 0) := by
  obtain ⟨hv, _, _, _⟩ := (decode_some_iff v ds).1 h
  unfold WCT9.CanonicalPolicy.reward
  rw [wordCredit_top, savedCopies_top, ds_getD_51 h, dataDigits_sum_LW hv]
  have hD := (group_lanes hv 0 (by norm_num)).2.2.2.2 rfl
  rw [hD, ds_getD_data h 0 (by norm_num)]
  unfold LS
  have hS : ∀ j ∈ Finset.range 17, eS (gIdx v j) =
      ((if ds.getD (3 * j) 0 + 1 = T3.maxDigit 0 (3 * j) then 1 else 0) +
       (if ds.getD (3 * j + 1) 0 + 1 = T3.maxDigit 0 (3 * j + 1) then 1 else 0) +
       (if ds.getD (3 * j + 2) 0 + 1 = T3.maxDigit 0 (3 * j + 2) then 1 else 0)) +
      4 * ((if ds.getD (3 * j) 0 = T3.maxDigit 0 (3 * j) ∧ ds.getD (3 * j + 1) 0 = T3.maxDigit 0 (3 * j + 1)
          then 1 else 0) +
       (if ds.getD (3 * j + 1) 0 = T3.maxDigit 0 (3 * j + 1) ∧ ds.getD (3 * j + 2) 0 = T3.maxDigit 0 (3 * j + 2)
          then 1 else 0)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [(group_lanes hv j hj').2.2.1, ds_getD_data h _ (by omega), ds_getD_data h _ (by omega),
      ds_getD_data h _ (by omega)]
  have e7 : (if 153 - LW v + 1 = 7 then 1 else 0) = (if 153 - LW v = 6 then 1 else 0) := by
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hS, e7]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem penalty_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.dispatchPenalty 0 ds = LPen v := by
  obtain ⟨hv, _, _, _⟩ := (decode_some_iff v ds).1 h
  unfold WCT9.dispatchPenalty LPen
  rw [if_pos rfl, penalty_top]
  have p8 := (group_lanes hv 8 (by norm_num)).2.2.2.1
  have p10 := (group_lanes hv 10 (by norm_num)).2.2.2.1
  have p11 := (group_lanes hv 11 (by norm_num)).2.2.2.1
  have p12 := (group_lanes hv 12 (by norm_num)).2.2.2.1
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff, true_and] at p8 p10 p11 p12
  rw [p8, p10, p11, p12]
  simp only [ds_getD_data h _ (show 24 < 51 by norm_num), ds_getD_data h _ (show 25 < 51 by norm_num),
    ds_getD_data h _ (show 26 < 51 by norm_num), ds_getD_data h _ (show 30 < 51 by norm_num),
    ds_getD_data h _ (show 31 < 51 by norm_num), ds_getD_data h _ (show 32 < 51 by norm_num),
    ds_getD_data h _ (show 33 < 51 by norm_num), ds_getD_data h _ (show 34 < 51 by norm_num),
    ds_getD_data h _ (show 35 < 51 by norm_num), ds_getD_data h _ (show 36 < 51 by norm_num),
    ds_getD_data h _ (show 37 < 51 by norm_num), ds_getD_data h _ (show 38 < 51 by norm_num)]
/-- The kernel's acceptance test of a half `v` at threshold `thr` (Nat form of the machine checks). -/
def kAcc (v : Digest) (thr : Nat) : Prop :=
  v.toNat / 2 ^ 127 % 2 = 0 ∧ LW v ≤ 153 ∧ 153 - LW v < 8 ∧ LZ v + (if 153 - LW v = 0 then 1 else 0) ≤ 7 ∧
    thr + LPen v ≤ LS v + 4 * eD (gIdx v 0) + (if 153 - LW v = 6 then 1 else 0)
theorem kAcc_decode {v : Digest} {thr : Nat} (h : kAcc v thr) :
    WCT9.CanonicalPolicy.decode 0 v = some (T3.dataDigits 0 v ++ [153 - LW v]) := by
  obtain ⟨hs, h1, h2, _, _⟩ := h
  have hv : T3.topRanksValid v = true := by
    cases hc : T3.topRanksValid v
    · have := invalid_LW hs hc; omega
    · rfl
  exact (decode_some_iff v _).2 ⟨hv, h1, h2, rfl⟩
/-- The canonical top producer predicate is the kernel test at threshold `f - 3 [low]`. -/
theorem producer_some (v : Digest) (f : Nat) (low : Bool) (hf : 3 ≤ f) (ds : List Nat) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 f low v = some ds ↔
      kAcc v (f - if low then 3 else 0) ∧ WCT9.CanonicalPolicy.decode 0 v = some ds := by
  unfold WCT9.CanonicalPolicy.producerDecodeAt
  cases hd : WCT9.CanonicalPolicy.decode 0 v with
  | none => simp
  | some ds' =>
    obtain ⟨hv, h1, h2, _⟩ := (decode_some_iff v ds').1 hd
    have hs : v.toNat / 2 ^ 127 % 2 = 0 := by
      have := (valid_groups hv).1; rwa [topSpare_eq] at this
    simp only [Option.some.injEq]
    rw [WCT9.CanonicalPolicy.pathReward_top, reward_lanes hd, penalty_lanes hd]
    have hz : WCT9.producerZeroBound 0 ds' ↔ LZ v + (if 153 - LW v = 0 then 1 else 0) ≤ 7 := by
      unfold WCT9.producerZeroBound WCT9.producerZeroMax; rw [zeros_lanes hd]; simp
    have hrb : WCT9.producerRankBound 0 v := Or.inl rfl
    unfold kAcc
    obtain ⟨cl, hcl, hfl⟩ : ∃ cl, (if low = true then 3 else 0) = cl ∧ cl ≤ 3 := ⟨_, rfl, by split_ifs <;> omega⟩
    rw [hcl]
    generalize (if 153 - LW v = 6 then 1 else 0) = c6
    generalize (if 153 - LW v = 0 then 1 else 0) = c0 at hz
    constructor
    · intro hh
      split_ifs at hh with hc
      simp only [Option.some.injEq] at hh
      exact ⟨⟨hs, h1, h2, hz.1 hc.2.1, by omega⟩, hh⟩
    · rintro ⟨⟨_, _, _, hzz, hr⟩, rfl⟩
      rw [if_pos ⟨by omega, hz.2 hzz, hrb⟩]
abbrev kRegs : List Reg := [.x6, .x7, .x10, .x11, .x20, .x21, .x25, .x28, .x29, .x30]
abbrev uRegs : List Reg := [.x10, .x11, .x25, .x28, .x29, .x30]
/-- RC constants: the kernel floor is the canonical top floor (19). -/
theorem topFloor_rc : ClaudeWCT.WCT9.CanonicalPolicy.topFloor = kFloor := rfl
/-- An accepted producer answer meets its floor on the path-aware credit. -/
theorem producerDecodeOut_floor {f : Nat} {a : BitVec 256} {ds : List Nat} {low : Bool}
    (h : WCT9.CanonicalPolicy.producerDecodeOut 0 f a = some (ds, low)) :
    f ≤ WCT9.CanonicalPolicy.credit 0 low ds := by
  unfold WCT9.CanonicalPolicy.producerDecodeOut at h
  cases hp : WCT9.CanonicalPolicy.producerDecodeAt 0 f (WCT9.lowSelected 0 a) (WCT9.encodingAnswer 0 a) with
  | none => rw [hp] at h; cases h
  | some ds' =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold WCT9.CanonicalPolicy.producerDecodeAt at hp
    split at hp
    · split_ifs at hp with hc
      · simp only [Option.some.injEq] at hp
        subst hp
        unfold WCT9.CanonicalPolicy.credit
        omega
    · cases hp

/-! ### BitVec value helpers -/
theorem bv_and_mask (x : Word) (w : Nat) (hw : w ≤ 64) :
    x &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ w - 1 < 2 ^ 64 by
      have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
      have : 0 < 2 ^ w := by positivity
      omega), Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  have : x.toNat % 2 ^ w < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  rw [Nat.mod_eq_of_lt this]
theorem bv_shr (a k : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) :=
  ofNat_shr a k ha
theorem bv_ult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
theorem bv_sub (a b : Nat) (hab : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  omega
theorem bv_and_ofNat (a m : Nat) (ha : a < 2 ^ 64) (hm : m < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 m = BitVec.ofNat 64 (a &&& m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt ha, toNat_ofNat_lt hm,
    toNat_ofNat_lt (lt_of_le_of_lt Nat.and_le_left ha)]
theorem e_d0 : ∀ f < 424, r6Entry f / 2 ^ 12 &&& 4 = 4 * eD f := by decide +kernel
/-! ### Generic single-instruction pieces (branch / jump), via a pc-generic symbolic run -/
theorem br_spec {image : Image} {w : BitVec 32} {pc off : Word} {op : CmpOp} {x y : E}
    (hrun : symRun { noAlias := true } [w] pc 10 =
      some ⟨SymState.init, .ite op x y (.c (pc + off)) (.c (pc + 4)), .branch, 1, 1⟩)
    (hc : CodeAt image pc [w]) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if op.eval (x.eval s) (y.eval s) then pc + off else pc + 4) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp] <;> split <;> rfl
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
theorem jal_spec {image : Image} {w : BitVec 32} {pc off : Word}
    (hrun : symRun { noAlias := true } [w] pc 10 = some ⟨SymState.init, .c (pc + off), .jump, 1, 1⟩)
    (hc : CodeAt image pc [w]) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + off ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp]
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
/-! ### Kernel pieces (words of `kCode`; both instances unless noted) -/
def kBlt : List (BitVec 32) := [0x1c03c663]
theorem run_blt (pc : Word) : symRun { noAlias := true } kBlt pc 10 =
    some ⟨SymState.init, .ite .lt (.reg .x7) (.c 0) (.c (pc + BitVec.ofNat 64 460)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kG0b : List (BitVec 32) := [0xccde93,0x4efe93,0x1dc8cb3]
sym_block g0bRun := symRun { noAlias := true } kG0b 0 10
theorem run_g0b (pc : Word) : symRun { noAlias := true } kG0b pc 10 =
    some ⟨g0bRun.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem g0b_spec {image : Image} {pc : Word} (hc : CodeAt image pc kG0b) (s : MachineState) (hpc : s.pc = pc)
    {f : Nat} (hf : f < 424) (h25 : s.getReg .x25 = BitVec.ofNat 64 (r6Entry f)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x25 = BitVec.ofNat 64 (r6Entry f + 4 * eD f) ∧
      RegsExcept s t [.x25, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_g0b pc) hc s hpc (by simp [g0bRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [g0bRun.res, rv_simp]
  · have he := r6Entry_lt f hf
    simp only [rv_simp, g0bRun.res, h25, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ (by omega), bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num),
      e_d0 f hf, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [g0bRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [g0bRun.res, rv_simp]
theorem land_mask (n w : Nat) : n &&& (2 ^ w - 1) = n % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod n w
theorem t5_val (v : Digest) :
    (v.extractLsb' 0 64 >>> 63) ||| (v.extractLsb' 64 64 <<< 1) = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
  simp only [BitVec.getLsbD, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hi, decide_true, Bool.true_and]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · simp only [show ¬ 63 + i < 64 by omega, show ¬ i < 1 by omega, show i - 1 < 64 by omega, decide_false,
      decide_true, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and]
    rw [show 64 + (i - 1) = i + 63 by omega]
def kT5 : List (BitVec 32) := [0x3f35f13,0x139e13,0x1cf6f33]
sym_block t5Run := symRun { noAlias := true } kT5 0 10
theorem run_t5 (pc : Word) : symRun { noAlias := true } kT5 pc 10 =
    some ⟨t5Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem t5_spec {image : Image} {pc : Word} (hc : CodeAt image pc kT5) (s : MachineState) (hpc : s.pc = pc)
    (v : Digest) (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x30 = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_t5 pc) hc s hpc (by simp [t5Run.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [t5Run.res, rv_simp]
  · simp only [rv_simp, t5Run.res, h6, h7, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact t5_val v
  · intro r hr; simp at hr; cases r <;> simp_all [t5Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [t5Run.res, rv_simp]
def kTot : List (BitVec 32) := [0xbc8cb3,0x125d593,0xf5f593,0x16cde13,0x41c88e33,0x8e3e93]
sym_block totRun := symRun { noAlias := true } kTot 0 10
theorem run_tot (pc : Word) : symRun { noAlias := true } kTot pc 10 =
    some ⟨totRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4 + 4), .endOfCode, 6, 6⟩ := by
  rfl
theorem tot_spec {image : Image} {pc : Word} (hc : CodeAt image pc kTot) (s : MachineState) (hpc : s.pc = pc)
    {S A : Nat} (hSA : S + A < 2 ^ 64) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 A) (h17 : s.getReg .x17 = BitVec.ofNat 64 153) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x25 = BitVec.ofNat 64 (S + A) ∧ t.getReg .x11 = BitVec.ofNat 64 (A / 2 ^ 18 % 16) ∧
      t.getReg .x28 = BitVec.ofNat 64 153 - BitVec.ofNat 64 ((S + A) / 2 ^ 22) ∧
      t.getReg .x29 = (if (BitVec.ofNat 64 153 - BitVec.ofNat 64 ((S + A) / 2 ^ 22)).ult (BitVec.ofNat 64 8)
        then 1 else 0) ∧
      RegsExcept s t [.x11, .x25, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hA : A < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_tot pc) hc s hpc (by simp [totRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [totRun.res, rv_simp]
  · simp only [rv_simp, totRun.res, h25, h11, ofNat_add_ofNat]
  · simp only [rv_simp, totRun.res, h11, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ hA, bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) hA) (by norm_num),
      show (15 : Nat) = 2 ^ 4 - 1 from rfl, land_mask]
    norm_num
  · simp only [rv_simp, totRun.res, h25, h11, h17, ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [bv_shr _ _ hSA]
    norm_num
  · simp only [rv_simp, totRun.res, h25, h11, h17, ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [bv_shr _ _ hSA]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [totRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [totRun.res, rv_simp]
def kH2a : List (BitVec 32) := [0x8cde93,0x3fefe93,0x1e3f13,0x1ee8eb3,0x8ebe93]
sym_block h2aRun := symRun { noAlias := true } kH2a 0 10
theorem run_h2a (pc : Word) : symRun { noAlias := true } kH2a pc 10 =
    some ⟨h2aRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by
  rfl
theorem h2a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kH2a) (s : MachineState) (hpc : s.pc = pc)
    {S d : Nat} (hS : S < 2 ^ 64) (hd : d < 2 ^ 64) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x29 = (if S / 2 ^ 8 % 64 + (if d = 0 then 1 else 0) < 8 then 1 else 0) ∧
      RegsExcept s t [.x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h2a pc) hc s hpc (by simp [h2aRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [h2aRun.res, rv_simp]
  · simp only [rv_simp, h2aRun.res, h25, h28, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [bv_shr _ _ hS, bv_and_ofNat _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) hS) (by norm_num),
      show (63 : Nat) = 2 ^ 6 - 1 from rfl, land_mask, bv_ult _ _ hd (by norm_num)]
    by_cases h0 : d = 0
    · simp only [h0, show (0 : Nat) < 1 by norm_num, decide_true, if_true, ofNat_add_ofNat]
      rw [bv_ult _ _ (by omega) (by norm_num)]
      simp
    · simp only [h0, show ¬ d < 1 by omega, decide_false, if_false, Bool.false_eq_true, BitVec.add_zero]
      rw [bv_ult _ _ (by omega) (by norm_num)]
      simp
  · intro r hr; simp at hr; cases r <;> simp_all [h2aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [h2aRun.res, rv_simp]
theorem bv_eq6 (d : Nat) (hd : d < 2 ^ 63) :
    (BitVec.ofNat 64 d - 6#64).ult 1#64 = decide (d = 6) := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]
  by_cases h : d = 6
  · subst h; decide
  · simp only [h, decide_false, decide_eq_false_iff_not]
    omega
def kH3a : List (BitVec 32) := [0xffcfe93,0x40be8eb3,0xffae0f13,0x1f3f13,0x1ee8eb3]
sym_block h3aRun := symRun { noAlias := true } kH3a 0 10
theorem run_h3a (pc : Word) : symRun { noAlias := true } kH3a pc 10 =
    some ⟨h3aRun.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by
  rfl
theorem h3a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kH3a) (s : MachineState) (hpc : s.pc = pc)
    {S P d : Nat} (hS : S < 2 ^ 64) (hd : d < 2 ^ 63) (h25 : s.getReg .x25 = BitVec.ofNat 64 S)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 P) (h28 : s.getReg .x28 = BitVec.ofNat 64 d) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧
      t.getReg .x29 = BitVec.ofNat 64 (S % 256 + (if d = 6 then 1 else 0)) - BitVec.ofNat 64 P ∧
      RegsExcept s t [.x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h3a pc) hc s hpc (by simp [h3aRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [h3aRun.res, rv_simp]
  · simp only [rv_simp, h3aRun.res, h25, h11, h28]
    rw [show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl, bv_and_mask _ 8 (by norm_num),
      toNat_ofNat_lt hS, bv_eq6 d hd]
    by_cases h6 : d = 6
    · simp only [h6, decide_true, if_true]
      rw [show S % 256 + 1 = S % 2 ^ 8 + 1 by norm_num, ← ofNat_add_ofNat (S % 2 ^ 8) 1]
      ring
    · simp only [h6, decide_false, if_false, Bool.false_eq_true]
      simp
  · intro r hr; simp at hr; cases r <;> simp_all [h3aRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [h3aRun.res, rv_simp]
theorem run_a1 (pc : Word) : symRun { noAlias := true } kA1 pc 10 =
    some ⟨⟨{ RegFile.init with r29 := .bin .add (.reg .x29) (.c 3) }, [], []⟩, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
def kF1a : List (BitVec 32) := [0x3e3de93]
theorem run_f1a (pc : Word) : symRun { noAlias := true } kF1a pc 10 =
    some ⟨⟨{ RegFile.init with r29 := .bin .srl (.reg .x7) (.c 62) }, [], []⟩, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
def kBr100 : List (BitVec 32) := [0x40e8663]
theorem run_br100 (pc : Word) : symRun { noAlias := true } kBr100 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 76)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kBr106 : List (BitVec 32) := [0x20e8a63]
theorem run_br106 (pc : Word) : symRun { noAlias := true } kBr106 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 52)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kBr112 : List (BitVec 32) := [0x15ece63]
theorem run_br112 (pc : Word) : symRun { noAlias := true } kBr112 pc 10 =
    some ⟨SymState.init, .ite .lt (.reg .x29) (.reg .x21) (.c (pc + BitVec.ofNat 64 28)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kBrA0 : List (BitVec 32) := [0xa1463]
theorem run_brA0 (pc : Word) : symRun { noAlias := true } kBrA0 pc 10 =
    some ⟨SymState.init, .ite .ne (.reg .x20) (.c 0) (.c (pc + BitVec.ofNat 64 8)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kBrF0 : List (BitVec 32) := [0x20a1063]
theorem run_brF0 (pc : Word) : symRun { noAlias := true } kBrF0 pc 10 =
    some ⟨SymState.init, .ite .ne (.reg .x20) (.c 0) (.c (pc + BitVec.ofNat 64 32)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kBr121 : List (BitVec 32) := [0xe8c63]
theorem run_br121 (pc : Word) : symRun { noAlias := true } kBr121 pc 10 =
    some ⟨SymState.init, .ite .eq (.reg .x29) (.c 0) (.c (pc + BitVec.ofNat 64 24)) (.c (pc + 4)), .branch, 1, 1⟩ := by
  rfl
def kJ118S : List (BitVec 32) := [0xf14ec06f]
theorem run_j118S (pc : Word) : symRun { noAlias := true } kJ118S pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 18446744073709471508), .jump, 1, 1⟩ := by
  rfl
def kJ118E : List (BitVec 32) := [0x4680006f]
theorem run_j118E (pc : Word) : symRun { noAlias := true } kJ118E pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 1128), .jump, 1, 1⟩ := by
  rfl
def kJ126 : List (BitVec 32) := [0xe19ff06f]
theorem run_j126 (pc : Word) : symRun { noAlias := true } kJ126 pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 18446744073709551128), .jump, 1, 1⟩ := by
  rfl
theorem run_jNS (pc : Word) : symRun { noAlias := true } kNS pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 18446744073709468484), .jump, 1, 1⟩ := by
  rfl
theorem run_jNE (pc : Word) : symRun { noAlias := true } kNE pc 10 =
    some ⟨SymState.init, .c (pc + BitVec.ofNat 64 18446744073709357492), .jump, 1, 1⟩ := by
  rfl
def kE0S : List (BitVec 32) := [0x1000537,0x8a050513,0xa13,0x1000a93]
def kE0E : List (BitVec 32) := [0xa0537,0xa050513,0xa13,0x1000a93]
sym_block e0sRun := symRun { noAlias := true } kE0S 0 10
sym_block e0eRun := symRun { noAlias := true } kE0E 0 10
theorem run_e0s (pc : Word) : symRun { noAlias := true } kE0S pc 10 =
    some ⟨e0sRun.res.st, .c (pc + 4 + 4 + 4 + 4), .endOfCode, 4, 4⟩ := by
  rfl
theorem run_e0e (pc : Word) : symRun { noAlias := true } kE0E pc 10 =
    some ⟨e0eRun.res.st, .c (pc + 4 + 4 + 4 + 4), .endOfCode, 4, 4⟩ := by
  rfl
def kA2aS : List (BitVec 32) := [0x66f37,0x1df3c23,0x7f4f3c23]
def kA2aE : List (BitVec 32) := [0x66f37,0x5df3023,0x7f4f3c23]
sym_block a2sBlk := symRun { noAlias := true } kA2aS (pcOf (21667 + 115)) 10
sym_block a2eBlk := symRun { noAlias := true } kA2aE (pcOf (49226 + 115)) 10
def kF2a : List (BitVec 32) := [0x8000a13,0x1300a93,0x1063303,0x1863383]
sym_block f2sBlk := symRun { noAlias := true } kF2a (pcOf (21667 + 122)) 10
sym_block f2eBlk := symRun { noAlias := true } kF2a (pcOf (49226 + 122)) 10
/-! ### pc arithmetic -/
theorem pcOf_plus (k n : Nat) (h : 0x1000 + 4 * (k + n) < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 (4 * n) = pcOf (k + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
theorem pcOf_minus (k n : Nat) (hn : n ≤ k) (h : 0x1000 + 4 * k < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 (2 ^ 64 - 4 * n) = pcOf (k - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
theorem pcOf_4 (k : Nat) : pcOf k + 4 = pcOf (k + 1) := pcOf_add4 k
theorem pcOf_4' (k : Nat) : pcOf k + 4#64 = pcOf (k + 1) := pcOf_add4 k
/-! ### Remaining pieces -/
theorem e0_spec {image : Image} {b : Nat} (hb : b = 354 ∨ b = 543)
    (hc : CodeAt image (pcOf (kBase b)) (if b = 354 then kE0E else kE0S)) (s : MachineState)
    (hpc : s.pc = pcOf (kBase b)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (kBase b + 4) ∧ t.getReg .x10 = BitVec.ofNat 64 (tblBlk b + 160) ∧
      t.getReg .x20 = 0 ∧ t.getReg .x21 = BitVec.ofNat 64 16 ∧ RegsExcept s t [.x10, .x20, .x21] ∧
      Frame s t (fun _ => False) := by
  rcases hb with rfl | rfl
  · refine ⟨_, symRun_sound (run_e0e _) hc s hpc (by simp [e0eRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, pcOf_4, pcOf_4']
    · simp only [rv_simp, e0eRun.res] <;> rfl
    · simp only [rv_simp, e0eRun.res] <;> rfl
    · simp only [rv_simp, e0eRun.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [e0eRun.res, rv_simp] <;> rfl
    · intro A _ _; simp [e0eRun.res, rv_simp]
  · refine ⟨_, symRun_sound (run_e0s _) hc s hpc (by simp [e0sRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, pcOf_4, pcOf_4']
    · simp only [rv_simp, e0sRun.res] <;> rfl
    · simp only [rv_simp, e0sRun.res] <;> rfl
    · simp only [rv_simp, e0sRun.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [e0sRun.res, rv_simp] <;> rfl
    · intro A _ _; simp [e0sRun.res, rv_simp]
theorem a1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kA1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = s.getReg .x29 + 3 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_a1 pc) hc s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [rv_simp, RegFile.init] <;> rfl
  · intro A _ _; simp [rv_simp]
theorem f1a_spec {image : Image} {pc : Word} (hc : CodeAt image pc kF1a) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = s.getReg .x7 >>> 62 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_f1a pc) hc s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [rv_simp]
  · simp only [rv_simp] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [rv_simp, RegFile.init] <;> rfl
  · intro A _ _; simp [rv_simp]
def kA2a (b : Nat) : List (BitVec 32) := if b = 354 then kA2aE else kA2aS
theorem a2a_spec {image : Image} {b : Nat} (hb : b = 354 ∨ b = 543)
    (hc : CodeAt image (pcOf (kBase b + 115)) (kA2a b)) (s : MachineState) (hpc : s.pc = pcOf (kBase b + 115)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (kBase b + 118) ∧
      t.getMem (BitVec.ofNat 64 (creditAddr b)) = s.getReg .x29 ∧ t.getMem (BitVec.ofNat 64 FLAGA) = s.getReg .x20 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = creditAddr b ∨ A = FLAGA) := by
  rcases hb with rfl | rfl
  · refine ⟨_, symRun_sound a2eBlk hc s hpc (by simp [a2eBlk.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, a2eBlk.res] <;> rfl
    · simp only [rv_simp, a2eBlk.res] <;> rfl
    · simp only [rv_simp, a2eBlk.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [a2eBlk.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [rv_simp, a2eBlk.res]
      have h1 : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 FLAGA := fun h => hn (Or.inr ((ofNat_inj hA (by norm_num)).1 h))
      have h2 : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (creditAddr _) :=
        fun h => hn (Or.inl ((ofNat_inj hA (by simp [creditAddr])).1 h))
      simp only [FLAGA, creditAddr_354, creditAddr_543] at h1 h2
      simp [h1, h2]
  · refine ⟨_, symRun_sound a2sBlk hc s hpc (by simp [a2sBlk.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, a2sBlk.res] <;> rfl
    · simp only [rv_simp, a2sBlk.res] <;> rfl
    · simp only [rv_simp, a2sBlk.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [a2sBlk.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [rv_simp, a2sBlk.res]
      have h1 : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 FLAGA := fun h => hn (Or.inr ((ofNat_inj hA (by norm_num)).1 h))
      have h2 : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (creditAddr _) :=
        fun h => hn (Or.inl ((ofNat_inj hA (by simp [creditAddr])).1 h))
      simp only [FLAGA, creditAddr_354, creditAddr_543] at h1 h2
      simp [h1, h2]
theorem f2a_spec {image : Image} {b : Nat} (hb : b = 354 ∨ b = 543)
    (hc : CodeAt image (pcOf (kBase b + 122)) kF2a) (s : MachineState) (hpc : s.pc = pcOf (kBase b + 122))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 EOUT) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (kBase b + 126) ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 (EOUT + 16)) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 (EOUT + 24)) ∧
      t.getReg .x20 = BitVec.ofNat 64 128 ∧ t.getReg .x21 = BitVec.ofNat 64 kFloor ∧
      RegsExcept s t [.x6, .x7, .x20, .x21] ∧ Frame s t (fun _ => False) := by
  rcases hb with rfl | rfl
  · refine ⟨_, symRun_sound f2eBlk hc s hpc (by simp only [rv_simp, f2eBlk.res, h12, EOUT, accessValid_iff, MEMORY_BYTES]; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, f2eBlk.res] <;> rfl
    · simp only [rv_simp, f2eBlk.res, h12] <;> rfl
    · simp only [rv_simp, f2eBlk.res, h12] <;> rfl
    · simp only [rv_simp, f2eBlk.res] <;> rfl
    · simp only [rv_simp, f2eBlk.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [f2eBlk.res, rv_simp] <;> rfl
    · intro A _ _; simp [f2eBlk.res, rv_simp]
  · refine ⟨_, symRun_sound f2sBlk hc s hpc (by simp only [rv_simp, f2sBlk.res, h12, EOUT, accessValid_iff, MEMORY_BYTES]; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rv_simp, f2sBlk.res] <;> rfl
    · simp only [rv_simp, f2sBlk.res, h12] <;> rfl
    · simp only [rv_simp, f2sBlk.res, h12] <;> rfl
    · simp only [rv_simp, f2sBlk.res] <;> rfl
    · simp only [rv_simp, f2sBlk.res] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [f2sBlk.res, rv_simp] <;> rfl
    · intro A _ _; simp [f2sBlk.res, rv_simp]
/-! ### Table lookups -/
/-- Four-instruction lookup (`shift t3, src, sh ; andi t3, t3, mask ; add t3, t3, a0 ; lwu rd, off(t3)`). -/
theorem look4 {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    (hv : accessValid (((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10 + off) 4 = true) :
    let base := ((op0.eval (s.getReg src) sh) &&& mask) + s.getReg .x10
    let ld := (s.getWord32 (base + off)).zeroExtend 64
    ∃ t, Steps image s 4 4 t ∧ t.pc = s.pc + 16 ∧ t.getReg rd = ld ∧
      RegsExcept s t [.x28, rd] ∧ Frame s t (fun _ => False) := by
  intro base ld
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have spc : ∀ (x : MachineState) (v : Word), (x.setPC v).pc = v := fun _ _ => rfl
  have w32p : ∀ (x : MachineState) (v a : Word), (x.setPC v).getWord32 a = x.getWord32 a := fun _ _ _ => rfl
  have w32r : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getWord32 a = x.getWord32 a := by
    intro x r v a; cases r <;> rfl
  have memp : ∀ (x : MachineState) (v a : Word), (x.setPC v).getMem a = x.getMem a := fun _ _ _ => rfl
  have memr : ∀ (x : MachineState) (r : Reg) (v a : Word), (x.setReg r v).getMem a = x.getMem a := by
    intro x r v a; cases r <;> rfl
  have gp : ∀ (x : MachineState) (v : Word) (r : Reg), (x.setPC v).getReg r = x.getReg r := getReg_setPC'
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have c1 := hc.tail
  have c2 := c1.tail
  have c3 := c2.tail
  have hx28 : (.x28 : Reg) ≠ .x0 := by decide
  have st0 := step_alu (hd hc) hpc hd0 hc0
  generalize hu1 : (s.setReg .x28 (op0.eval ((Src.reg src).eval s) ((Src.imm sh).eval s))).setPC (s.pc + 4) = u1
    at st0
  have p1 : u1.pc = pc + 4 := by rw [← hu1, spc, hpc]
  have r1 : ∀ q, q ≠ .x28 → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, gp, gne _ _ _ _ hq]
  have g1 : u1.getReg .x28 = op0.eval (s.getReg src) sh := by rw [← hu1, gp, geq _ _ _ hx28]; rfl
  have st1 := step_alu (hd c1) p1 hd1 hc1
  generalize hu2 : (u1.setReg .x28 (BinOp.and.eval ((Src.reg .x28).eval u1) ((Src.imm mask).eval u1))).setPC
    (u1.pc + 4) = u2 at st1
  have p2 : u2.pc = pc + 4 + 4 := by rw [← hu2, spc, p1]
  have r2 : ∀ q, q ≠ .x28 → u2.getReg q = s.getReg q := fun q hq => by rw [← hu2, gp, gne _ _ _ _ hq, r1 q hq]
  have g2 : u2.getReg .x28 = op0.eval (s.getReg src) sh &&& mask := by
    rw [← hu2, gp, geq _ _ _ hx28]; show u1.getReg .x28 &&& mask = _; rw [g1]
  have st2 := step_alu (hd c2) p2 hd2 hc2
  generalize hu3 : (u2.setReg .x28 (BinOp.add.eval ((Src.reg .x28).eval u2) ((Src.reg .x10).eval u2))).setPC
    (u2.pc + 4) = u3 at st2
  have p3 : u3.pc = pc + 4 + 4 + 4 := by rw [← hu3, spc, p2]
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = s.getReg q := fun q hq => by rw [← hu3, gp, gne _ _ _ _ hq, r2 q hq]
  have g3 : u3.getReg .x28 = base := by
    rw [← hu3, gp, geq _ _ _ hx28]; show u2.getReg .x28 + u2.getReg .x10 = base; rw [g2, r2 .x10 (by decide)]
  have m3 : ∀ a, u3.getWord32 a = s.getWord32 a := fun a => by
    rw [← hu3, w32p, w32r, ← hu2, w32p, w32r, ← hu1, w32p, w32r]
  have hv3 : accessValid (u3.getReg .x28 + off) 4 = true := by rw [g3]; exact hv
  have st3 := step_lwu (hd c3) p3 hd3 hc3 hv3
  generalize hu4 : (u3.setReg rd ((u3.getWord32 (u3.getReg .x28 + off)).zeroExtend 64)).setPC (u3.pc + 4) = u4
    at st3
  refine ⟨u4, (((st0.trans st1).trans st2).trans st3).of_eq rfl ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcy
  · rw [← hu4, spc, p3, hpc]; bv_omega
  · rw [← hu4, gp, geq _ _ _ hrd.1, g3, m3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [← hu4, gp, gne _ _ _ _ hr.2, r3 r hr.1]
  · intro A _ _
    rw [← hu4, memp, memr, ← hu3, memp, memr, ← hu2, memp, memr, ← hu1, memp, memr]
theorem look4_entry {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image pc [w0, w1, w2, w3]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    {blk r f : Nat} (ht : R6TableW blk s) (hblk : blk % 8 = 0) (hb : blk + 1696 < 2 ^ 24) (hf : f < 424)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = s.pc + 16 ∧ t.getReg rd = BitVec.ofNat 64 (r6Entry f) ∧
      RegsExcept s t [.x28, rd] ∧ Frame s t (fun _ => False) := by
  have haddr : (op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off = BitVec.ofNat 64 (blk + 4 * f) := by
    rw [hbase, h10, hoff]
  have hv : accessValid ((op0.eval (s.getReg src) sh &&& mask) + s.getReg .x10 + off) 4 = true := by
    rw [haddr]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show blk + 4 * f < 2 ^ 64 by omega)]
    omega
  obtain ⟨t, st, pt, grd, rt, ft⟩ := look4 hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hcy hrd hsrc hv
  have hw : (s.getWord32 (BitVec.ofNat 64 (blk + 4 * f))).zeroExtend 64 = BitVec.ofNat 64 (r6Entry f) := by
    rw [r6_word ht hblk (by omega) f hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
    have := r6Entry_lt f hf
    have h64 : r6Entry f < 2 ^ 64 := by omega
    simp only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h64]
  refine ⟨t, st, pt, ?_, rt, ft⟩
  rw [grd]; simp only [haddr, hw]
/-- Five-instruction lookup with accumulation, relative to the half-test start state `s0`. -/
theorem lookR {image : Image} {s0 s : MachineState} {k : Nat} {w0 w1 w2 w3 w4 : BitVec 32}
    {i0 i1 i2 i3 i4 : Instruction} {src acc : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image (pcOf k) [w0, w1, w2, w3, w4]) (hpc : s.pc = pcOf k) (hk : 0x1000 + 4 * (k + 5) < 2 ^ 64)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu .x29 .x28 off))
    (hd4 : decodeInstruction w4 = some i4) (hc4 : classify i4 = some (.alu acc .add (.reg acc) (.reg .x29)))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 +
      (instructionCycles i4 + 0)))) = 5)
    (hacc : acc ≠ .x0 ∧ acc ≠ .x28 ∧ acc ≠ .x29) (hsrc : src ≠ .x0)
    {L : List Reg} (hL : .x28 ∈ L ∧ .x29 ∈ L ∧ acc ∈ L) (h10L : .x10 ∉ L)
    (hR : RegsExcept s0 s L) (hF : Frame s0 s (fun _ => False))
    {blk r f n : Nat} (ht : R6TableW blk s0) (hblk : blk % 8 = 0) (hb : blk + 1696 < 2 ^ 24) (hf : f < 424)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f))
    (hn : s.getReg acc = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (k + 5) ∧ RegsExcept s0 t L ∧ Frame s0 t (fun _ => False) ∧
      t.getReg acc = BitVec.ofNat 64 (n + r6Entry f) ∧ RegsExcept s t [.x28, .x29, acc] := by
  have ht' : R6TableW blk s := ht.frame hF (by omega) (fun _ _ h => h)
  have h10' : s.getReg .x10 = BitVec.ofNat 64 (blk + 160) := (hR .x10 h10L).trans h10
  obtain ⟨t, st, pt, _, gacc, rt, ft⟩ :=
    look5_entry hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hd4 hc4 hcy hacc hsrc ht' hblk hb hf h10' hbase hoff
  refine ⟨t, st, ?_, ?_, ?_, ?_, rt⟩
  · rw [pt, hpc, show (20 : Word) = BitVec.ofNat 64 (4 * 5) from rfl, pcOf_plus _ _ hk]
  · refine (hR.trans rt).mono ?_
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq
    · exact hq
    · exact hq ▸ hL.1
    · exact hq ▸ hL.2.1
    · exact hq ▸ hL.2.2
  · exact (hF.trans ft).mono (fun _ _ h => by simpa using h)
  · rw [gacc, hn, ofNat_add_ofNat]
/-- Four-instruction lookup (the accumulator is loaded), relative to the half-test start state `s0`. -/
theorem lookW {image : Image} {s0 s : MachineState} {k : Nat} {w0 w1 w2 w3 : BitVec 32}
    {i0 i1 i2 i3 : Instruction} {src rd : Reg} {op0 : BinOp} {sh mask off : Word}
    (hc : CodeAt image (pcOf k) [w0, w1, w2, w3]) (hpc : s.pc = pcOf k) (hk : 0x1000 + 4 * (k + 4) < 2 ^ 64)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu .x28 op0 (.reg src) (.imm sh)))
    (hd1 : decodeInstruction w1 = some i1) (hc1 : classify i1 = some (.alu .x28 .and (.reg .x28) (.imm mask)))
    (hd2 : decodeInstruction w2 = some i2) (hc2 : classify i2 = some (.alu .x28 .add (.reg .x28) (.reg .x10)))
    (hd3 : decodeInstruction w3 = some i3) (hc3 : classify i3 = some (.load .wu rd .x28 off))
    (hcy : instructionCycles i0 + (instructionCycles i1 + (instructionCycles i2 + (instructionCycles i3 + 0))) = 4)
    (hrd : rd ≠ .x0 ∧ rd ≠ .x28) (hsrc : src ≠ .x0)
    {L : List Reg} (hL : .x28 ∈ L ∧ rd ∈ L) (h10L : .x10 ∉ L)
    (hR : RegsExcept s0 s L) (hF : Frame s0 s (fun _ => False))
    {blk r f : Nat} (ht : R6TableW blk s0) (hblk : blk % 8 = 0) (hb : blk + 1696 < 2 ^ 24) (hf : f < 424)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (blk + 160))
    (hbase : op0.eval (s.getReg src) sh &&& mask = BitVec.ofNat 64 (4 * r))
    (hoff : BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + off = BitVec.ofNat 64 (blk + 4 * f)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (k + 4) ∧ RegsExcept s0 t L ∧ Frame s0 t (fun _ => False) ∧
      t.getReg rd = BitVec.ofNat 64 (r6Entry f) ∧ RegsExcept s t [.x28, rd] := by
  have ht' : R6TableW blk s := ht.frame hF (by omega) (fun _ _ h => h)
  have h10' : s.getReg .x10 = BitVec.ofNat 64 (blk + 160) := (hR .x10 h10L).trans h10
  obtain ⟨t, st, pt, grd, rt, ft⟩ :=
    look4_entry hc hpc hd0 hc0 hd1 hc1 hd2 hc2 hd3 hc3 hcy hrd hsrc ht' hblk hb hf h10' hbase hoff
  refine ⟨t, st, ?_, ?_, ?_, grd, rt⟩
  · rw [pt, hpc, show (16 : Word) = BitVec.ofNat 64 (4 * 4) from rfl, pcOf_plus _ _ hk]
  · refine (hR.trans rt).mono ?_
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq
    · exact hq
    · exact hq ▸ hL.1
    · exact hq ▸ hL.2
  · exact (hF.trans ft).mono (fun _ _ h => by simpa using h)
def kG0a : List (BitVec 32) := [0x231e13,0x3fce7e13,0xae0e33,0xf60e6c83]
def kLk1 : List (BitVec 32) := [0x635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk2 : List (BitVec 32) := [0xe35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk3 : List (BitVec 32) := [0x1635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk4 : List (BitVec 32) := [0x1e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk5 : List (BitVec 32) := [0x2635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kLk6 : List (BitVec 32) := [0x2e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
def kQ8 : List (BitVec 32) := [0x3635e13,0x1fce7e13,0xae0e33,0x400e6583]
def kLk9 : List (BitVec 32) := [0x2f1e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kLk10 : List (BitVec 32) := [0x5f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3]
def kLk11 : List (BitVec 32) := [0xcf5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3]
def kLk12 : List (BitVec 32) := [0x13f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3]
def kLk13 : List (BitVec 32) := [0x1af5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kLk14 : List (BitVec 32) := [0x21f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kLk15 : List (BitVec 32) := [0x28f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kLk16 : List (BitVec 32) := [0x2ff5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3]
def kLk7 : List (BitVec 32) := [0x36f5e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3]
/-- Fine layout of the kernel (every lookup and every branch its own segment). -/
def kLF (b : Nat) : Rv.Layout := [(0, if b = 354 then kE0E else kE0S), (4, kBlt), (5, kG0a), (9, kG0b), (12, kLk1), (17, kLk2), (22, kLk3), (27, kLk4), (32, kLk5), (37, kLk6), (42, kQ8), (46, kT5), (49, kLk9), (54, kLk10), (59, kLk11), (64, kLk12), (69, kLk13), (74, kLk14), (79, kLk15), (84, kLk16), (89, kLk7), (94, kTot), (100, kBr100), (101, kH2a), (106, kBr106), (107, kH3a), (112, kBr112), (113, kBrA0), (114, kA1), (115, kA2a b), (118, if b = 354 then kJ118E else kJ118S), (119, kBrF0), (120, kF1a), (121, kBr121), (122, kF2a), (126, kJ126), (127, kN b)]
theorem kLF_ok {b : Nat} (hb : b = 354 ∨ b = 543) : layoutOk 0 (kLF b) = true := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem kLF_code {b : Nat} (hb : b = 354 ∨ b = 543) : kCode b = layoutCode (kLF b) := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem codeAt_kf {image : Image} {b : Nat} (h : R6KAt image b) (i : Nat) {o : Nat} {seg : List (BitVec 32)}
    (hi : (kLF b)[i]? = some (o, seg)) : CodeAt image (pcOf (kBase b + o)) seg := by
  have hc := h.2.1
  rw [kLF_code h.1] at hc
  exact codeAt_sublayout hc (kLF_ok h.1) hi

/-- Kernel value of `s9` before the penalty merge (machine order) and of `a1` (penalty groups). -/
def kS9 (v : Digest) : Nat :=
  r6Entry (gIdx v 0) + 4 * eD (gIdx v 0) + r6Entry (gIdx v 1) + r6Entry (gIdx v 2) + r6Entry (gIdx v 3) +
    r6Entry (gIdx v 4) + r6Entry (gIdx v 5) + r6Entry (gIdx v 6) + r6Entry (gIdx v 9) + r6Entry (gIdx v 13) +
    r6Entry (gIdx v 14) + r6Entry (gIdx v 15) + r6Entry (gIdx v 16) + r6Entry (gIdx v 7)
def kPen (v : Digest) : Nat := r6Entry (gIdx v 8) + r6Entry (gIdx v 10) + r6Entry (gIdx v 11) + r6Entry (gIdx v 12)
theorem hoff_eq {blk r f O : Nat} (h : (4 * r + (blk + 160) + O) % 2 ^ 64 = blk + 4 * f) :
    BitVec.ofNat 64 (4 * r) + BitVec.ofNat 64 (blk + 160) + BitVec.ofNat 64 O = BitVec.ofNat 64 (blk + 4 * f) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, h]
  have : blk + 4 * f < 2 ^ 64 := by rw [← h]; exact Nat.mod_lt _ (by norm_num)
  omega
theorem lo_mod (v : Digest) (w : Nat) (h : w ≤ 64) : (v.extractLsb' 0 64).toNat % 2 ^ w = v.toNat % 2 ^ w := by
  have := lo_field v 0 w (by omega)
  simpa using this
theorem t5_field (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    v.toNat / 2 ^ 63 % 2 ^ 64 / 2 ^ S % 2 ^ w = v.toNat / 2 ^ (63 + S) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, show i + S < 64 by omega]
    congr 1; omega
  · simp [hi]
theorem t5_mod (v : Digest) (w : Nat) (h : w ≤ 64) :
    v.toNat / 2 ^ 63 % 2 ^ 64 % 2 ^ w = v.toNat / 2 ^ 63 % 2 ^ w :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)
theorem t5_lt (v : Digest) : v.toNat / 2 ^ 63 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
theorem pcOf_3 (k : Nat) : pcOf k + 4 + 4 + 4 = pcOf (k + 3) := by
  rw [pcOf_4, pcOf_4, pcOf_4]
/-- The 17 table lookups of the half test (kernel offsets 5..93). -/
theorem h1_run {image : Image} {b : Nat} (hR : R6KAt image b) (s0 s : MachineState)
    (hpc : s.pc = pcOf (kBase b + 5)) (v : Digest)
    (h6 : s0.getReg .x6 = v.extractLsb' 0 64) (h7 : s0.getReg .x7 = v.extractLsb' 64 64)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (tblBlk b + 160)) (ht : R6TableW (tblBlk b) s0)
    (hR0 : RegsExcept s0 s [.x11, .x25, .x28, .x29, .x30]) (hF0 : Frame s0 s (fun _ => False)) :
    ∃ t, Steps image s 89 89 t ∧ t.pc = pcOf (kBase b + 94) ∧
      t.getReg .x25 = BitVec.ofNat 64 (kS9 v) ∧ t.getReg .x11 = BitVec.ofNat 64 (kPen v) ∧
      RegsExcept s0 t [.x11, .x25, .x28, .x29, .x30] ∧ Frame s0 t (fun _ => False) := by
  have hb := hR.1
  have hblk : tblBlk b % 8 = 0 := by rcases hb with rfl | rfl <;> rfl
  have hbb : tblBlk b + 1696 < 2 ^ 24 := by rcases hb with rfl | rfl <;> simp [tblBlk]
  have hkb : kBase b < 2 ^ 20 := by rcases hb with rfl | rfl <;> simp [kBase]
  have hvl : v.toNat < 2 ^ 128 := v.isLt
  have hm : ∀ q ∈ ([.x11, .x25, .x28, .x29, .x30] : List Reg), q ∈ ([.x11, .x25, .x28, .x29, .x30] : List Reg) := fun _ h => h
  obtain ⟨t1, s1, p1, R1, F1, a25_1, x1⟩ := lookW (s0 := s0) (k := kBase b + 5) (src := .x6) (rd := .x25) (codeAt_kf hR 2 rfl) hpc (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) hR0 hF0 ht hblk hbb
    (r := v.toNat % 256) (f := gIdx v 0) (gIdx_lt v 0) h10
    (by change (s.getReg .x6 <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [(hR0 .x6 (by decide)).trans h6, shl2_and_mul4 _ 8 (by norm_num), lo_mod v 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 18446744073709551456 = BitVec.ofNat 64 (tblBlk b + 4 * (v.toNat % 256))
        exact hoff_eq (by omega))
  obtain ⟨t2, s2, p2, a25_2, x2, f2⟩ := g0b_spec (codeAt_kf hR 3 rfl) t1 (by rw [p1]) (gIdx_lt v 0) a25_1
  have R2 : RegsExcept s0 t2 [.x11, .x25, .x28, .x29, .x30] := (R1.trans x2).mono (by decide)
  have F2 : Frame s0 t2 (fun _ => False) := (F1.trans f2).mono (fun _ _ h => by simpa using h)
  have p2' : t2.pc = pcOf (kBase b + 12) := by rw [p2, pcOf_3]
  obtain ⟨t3, s3, p3, R3, F3, g3, x3⟩ := lookR (s0 := s0) (k := kBase b + 12) (src := .x6) (acc := .x25) (codeAt_kf hR 4 rfl) p2' (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R2 F2 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 1) % 256) (f := gIdx v 1) (gIdx_lt v 1) h10
    (by change (t2.getReg .x6 >>> 6) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R2 .x6 (by decide)).trans h6), shr_and_mul4 _ 6 8 (by norm_num), lo_field v (6 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 1) % 256))
        exact hoff_eq (by omega))
    a25_2
  obtain ⟨t4, s4, p4, R4, F4, g4, x4⟩ := lookR (s0 := s0) (k := kBase b + 17) (src := .x6) (acc := .x25) (codeAt_kf hR 5 rfl) p3 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R3 F3 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 2) % 256) (f := gIdx v 2) (gIdx_lt v 2) h10
    (by change (t3.getReg .x6 >>> 14) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R3 .x6 (by decide)).trans h6), shr_and_mul4 _ 14 8 (by norm_num), lo_field v (14 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 2) % 256))
        exact hoff_eq (by omega))
    g3
  obtain ⟨t5, s5, p5, R5, F5, g5, x5⟩ := lookR (s0 := s0) (k := kBase b + 22) (src := .x6) (acc := .x25) (codeAt_kf hR 6 rfl) p4 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R4 F4 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 3) % 256) (f := gIdx v 3) (gIdx_lt v 3) h10
    (by change (t4.getReg .x6 >>> 22) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R4 .x6 (by decide)).trans h6), shr_and_mul4 _ 22 8 (by norm_num), lo_field v (22 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 3) % 256))
        exact hoff_eq (by omega))
    g4
  obtain ⟨t6, s6, p6, R6, F6, g6, x6⟩ := lookR (s0 := s0) (k := kBase b + 27) (src := .x6) (acc := .x25) (codeAt_kf hR 7 rfl) p5 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R5 F5 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 4) % 256) (f := gIdx v 4) (gIdx_lt v 4) h10
    (by change (t5.getReg .x6 >>> 30) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R5 .x6 (by decide)).trans h6), shr_and_mul4 _ 30 8 (by norm_num), lo_field v (30 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 4) % 256))
        exact hoff_eq (by omega))
    g5
  obtain ⟨t7, s7, p7, R7, F7, g7, x7⟩ := lookR (s0 := s0) (k := kBase b + 32) (src := .x6) (acc := .x25) (codeAt_kf hR 8 rfl) p6 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R6 F6 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 5) % 256) (f := gIdx v 5) (gIdx_lt v 5) h10
    (by change (t6.getReg .x6 >>> 38) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R6 .x6 (by decide)).trans h6), shr_and_mul4 _ 38 8 (by norm_num), lo_field v (38 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 5) % 256))
        exact hoff_eq (by omega))
    g6
  obtain ⟨t8, s8, p8, R8, F8, g8, x8⟩ := lookR (s0 := s0) (k := kBase b + 37) (src := .x6) (acc := .x25) (codeAt_kf hR 9 rfl) p7 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R7 F7 ht hblk hbb
    (r := v.toNat / 2 ^ (8 * 6) % 256) (f := gIdx v 6) (gIdx_lt v 6) h10
    (by change (t7.getReg .x6 >>> 46) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [((R7 .x6 (by decide)).trans h6), shr_and_mul4 _ 46 8 (by norm_num), lo_field v (46 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ (8 * 6) % 256))
        exact hoff_eq (by omega))
    g7
  obtain ⟨t9, s9, p9, R9, F9, a11_9, x9⟩ := lookW (s0 := s0) (k := kBase b + 42) (src := .x6) (rd := .x11) (codeAt_kf hR 10 rfl) p8 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R8 F8 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 8) % 128) (f := gIdx v 8) (gIdx_lt v 8) h10
    (by change (t8.getReg .x6 >>> 54) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [((R8 .x6 (by decide)).trans h6), shr_and_mul4 _ 54 7 (by norm_num), lo_field v (54 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 8) % 128))
        exact hoff_eq (by omega))
  have a25_9 : t9.getReg .x25 = _ := (x9 .x25 (by decide)).trans g8
  obtain ⟨t10, s10, p10, a30_10, x10, f10⟩ := t5_spec (codeAt_kf hR 11 rfl) t9 (by rw [p9]) v
    ((R9 .x6 (by decide)).trans h6) ((R9 .x7 (by decide)).trans h7)
  have R10 : RegsExcept s0 t10 [.x11, .x25, .x28, .x29, .x30] := (R9.trans x10).mono (by decide)
  have F10 : Frame s0 t10 (fun _ => False) := (F9.trans f10).mono (fun _ _ h => by simpa using h)
  have p10' : t10.pc = pcOf (kBase b + 49) := by rw [p10, pcOf_3]
  have a25_10 : t10.getReg .x25 = _ := (x10 .x25 (by decide)).trans a25_9
  have a11_10 : t10.getReg .x11 = _ := (x10 .x11 (by decide)).trans a11_9
  obtain ⟨t11, s11, p11, R11, F11, g11, x11⟩ := lookR (s0 := s0) (k := kBase b + 49) (src := .x30) (acc := .x25) (codeAt_kf hR 12 rfl) p10' (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R10 F10 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 9) % 128) (f := gIdx v 9) (gIdx_lt v 9) h10
    (by change (t10.getReg .x30 <<< 2) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_10, shl2_and_mul4 _ 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_mod v 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 9) % 128))
        exact hoff_eq (by omega))
    a25_10
  have a11_11 : t11.getReg .x11 = _ := (x11 .x11 (by decide)).trans a11_10
  have a30_11 : t11.getReg .x30 = _ := (x11 .x30 (by decide)).trans a30_10
  obtain ⟨t12, s12, p12, R12, F12, g12, x12⟩ := lookR (s0 := s0) (k := kBase b + 54) (src := .x30) (acc := .x11) (codeAt_kf hR 13 rfl) p11 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R11 F11 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 10) % 128) (f := gIdx v 10) (gIdx_lt v 10) h10
    (by change (t11.getReg .x30 >>> 5) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_11, shr_and_mul4 _ 5 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (5 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 10) % 128))
        exact hoff_eq (by omega))
    a11_11
  have a25_12 : t12.getReg .x25 = _ := (x12 .x25 (by decide)).trans g11
  have a30_12 : t12.getReg .x30 = _ := (x12 .x30 (by decide)).trans a30_11
  obtain ⟨t13, s13, p13, R13, F13, g13, x13⟩ := lookR (s0 := s0) (k := kBase b + 59) (src := .x30) (acc := .x11) (codeAt_kf hR 14 rfl) p12 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R12 F12 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 11) % 128) (f := gIdx v 11) (gIdx_lt v 11) h10
    (by change (t12.getReg .x30 >>> 12) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_12, shr_and_mul4 _ 12 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (12 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 11) % 128))
        exact hoff_eq (by omega))
    g12
  have a25_13 : t13.getReg .x25 = _ := (x13 .x25 (by decide)).trans a25_12
  have a30_13 : t13.getReg .x30 = _ := (x13 .x30 (by decide)).trans a30_12
  obtain ⟨t14, s14, p14, R14, F14, g14, x14⟩ := lookR (s0 := s0) (k := kBase b + 64) (src := .x30) (acc := .x11) (codeAt_kf hR 15 rfl) p13 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R13 F13 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 12) % 128) (f := gIdx v 12) (gIdx_lt v 12) h10
    (by change (t13.getReg .x30 >>> 19) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_13, shr_and_mul4 _ 19 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (19 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 12) % 128))
        exact hoff_eq (by omega))
    g13
  have a25_14 : t14.getReg .x25 = _ := (x14 .x25 (by decide)).trans a25_13
  have a30_14 : t14.getReg .x30 = _ := (x14 .x30 (by decide)).trans a30_13
  obtain ⟨t15, s15, p15, R15, F15, g15, x15⟩ := lookR (s0 := s0) (k := kBase b + 69) (src := .x30) (acc := .x25) (codeAt_kf hR 16 rfl) p14 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R14 F14 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 13) % 128) (f := gIdx v 13) (gIdx_lt v 13) h10
    (by change (t14.getReg .x30 >>> 26) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_14, shr_and_mul4 _ 26 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (26 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 13) % 128))
        exact hoff_eq (by omega))
    a25_14
  have a11_15 : t15.getReg .x11 = _ := (x15 .x11 (by decide)).trans g14
  have a30_15 : t15.getReg .x30 = _ := (x15 .x30 (by decide)).trans a30_14
  obtain ⟨t16, s16, p16, R16, F16, g16, x16⟩ := lookR (s0 := s0) (k := kBase b + 74) (src := .x30) (acc := .x25) (codeAt_kf hR 17 rfl) p15 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R15 F15 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 14) % 128) (f := gIdx v 14) (gIdx_lt v 14) h10
    (by change (t15.getReg .x30 >>> 33) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_15, shr_and_mul4 _ 33 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (33 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 14) % 128))
        exact hoff_eq (by omega))
    g15
  have a11_16 : t16.getReg .x11 = _ := (x16 .x11 (by decide)).trans a11_15
  have a30_16 : t16.getReg .x30 = _ := (x16 .x30 (by decide)).trans a30_15
  obtain ⟨t17, s17, p17, R17, F17, g17, x17⟩ := lookR (s0 := s0) (k := kBase b + 79) (src := .x30) (acc := .x25) (codeAt_kf hR 18 rfl) p16 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R16 F16 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 15) % 128) (f := gIdx v 15) (gIdx_lt v 15) h10
    (by change (t16.getReg .x30 >>> 40) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_16, shr_and_mul4 _ 40 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (40 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 15) % 128))
        exact hoff_eq (by omega))
    g16
  have a11_17 : t17.getReg .x11 = _ := (x17 .x11 (by decide)).trans a11_16
  have a30_17 : t17.getReg .x30 = _ := (x17 .x30 (by decide)).trans a30_16
  obtain ⟨t18, s18, p18, R18, F18, g18, x18⟩ := lookR (s0 := s0) (k := kBase b + 84) (src := .x30) (acc := .x25) (codeAt_kf hR 19 rfl) p17 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R17 F17 ht hblk hbb
    (r := v.toNat / 2 ^ (7 * 16) % 128) (f := gIdx v 16) (gIdx_lt v 16) h10
    (by change (t17.getReg .x30 >>> 47) &&& BitVec.ofNat 64 (4 * (2 ^ 7 - 1)) = _
        rw [a30_17, shr_and_mul4 _ 47 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (47 + 2) 7 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 1024 = BitVec.ofNat 64 (tblBlk b + 4 * (296 + v.toNat / 2 ^ (7 * 16) % 128))
        exact hoff_eq (by omega))
    g17
  have a11_18 : t18.getReg .x11 = _ := (x18 .x11 (by decide)).trans a11_17
  have a30_18 : t18.getReg .x30 = _ := (x18 .x30 (by decide)).trans a30_17
  obtain ⟨t19, s19, p19, R19, F19, g19, x19⟩ := lookR (s0 := s0) (k := kBase b + 89) (src := .x30) (acc := .x25) (codeAt_kf hR 20 rfl) p18 (by omega)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) R18 F18 ht hblk hbb
    (r := v.toNat / 2 ^ 119 % 256) (f := gIdx v 7) (gIdx_lt v 7) h10
    (by change (t18.getReg .x30 >>> 54) &&& BitVec.ofNat 64 (4 * (2 ^ 8 - 1)) = _
        rw [a30_18, shr_and_mul4 _ 54 8 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_field v (54 + 2) 8 (by norm_num)] <;> norm_num)
    (by change _ + _ + BitVec.ofNat 64 0 = BitVec.ofNat 64 (tblBlk b + 4 * (40 + v.toNat / 2 ^ 119 % 256))
        exact hoff_eq (by omega))
    g18
  have a11_19 : t19.getReg .x11 = _ := (x19 .x11 (by decide)).trans a11_18
  refine ⟨t19, ?_, p19, g19, a11_19, R19, F19⟩
  exact Steps.of_eq ((((((((((((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).trans s10).trans s11).trans s12).trans s13).trans s14).trans s15).trans s16).trans s17).trans s18).trans s19) rfl rfl

/-! ### Lane extraction for the kernel sums -/
theorem gIdx_r6lt (v : Digest) (j : Nat) (hj : j < 8) : gIdx v j < 296 := by
  unfold gIdx; split_ifs <;> omega
theorem gIdx_r5ge (v : Digest) (j : Nat) (hj : 8 ≤ j) : 296 ≤ gIdx v j := by
  unfold gIdx; split_ifs <;> omega
theorem kLanes (v : Digest) :
    kS9 v + kPen v = LW v * 2 ^ 22 + LP v * 2 ^ 18 + LD v * 2 ^ 14 + LZ v * 2 ^ 8 + (LS v + 4 * eD (gIdx v 0)) ∧
      LP v ≤ 9 ∧ LD v ≤ 8 ∧ LZ v ≤ 51 ∧ LS v + 4 * eD (gIdx v 0) ≤ 140 ∧ LW v ≤ 4352 ∧
      kPen v / 2 ^ 18 % 16 = LPen v := by
  -- split by conjunct so that each `omega` sees only the lane facts it needs (one omega over all 102 lane atoms
  -- with the div/mod goal took ~30 s)
  have H : ∀ j < 17, r6Entry (gIdx v j) = eW (gIdx v j) * 2 ^ 22 + eP (gIdx v j) * 2 ^ 18 +
      eD (gIdx v j) * 2 ^ 14 + eZ (gIdx v j) * 2 ^ 8 + eS (gIdx v j) ∧ eW (gIdx v j) ≤ 256 ∧ eP (gIdx v j) ≤ 1 ∧
      eD (gIdx v j) ≤ 1 ∧ eZ (gIdx v j) ≤ 3 ∧ eS (gIdx v j) ≤ 8 := fun j _ => r6Entry_lanes _ (gIdx_lt v j)
  have P6 : ∀ j < 8, eP (gIdx v j) = 0 := fun j hj => e_r6P _ (gIdx_r6lt v j hj)
  have D5 : ∀ j, 8 ≤ j → eD (gIdx v j) = 0 := fun j hj => e_r5D _ (gIdx_lt v j) (gIdx_r5ge v j hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [kS9, kPen, LW, LP, LD, LZ, LS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [(H 0 (by norm_num)).1, (H 1 (by norm_num)).1, (H 2 (by norm_num)).1, (H 3 (by norm_num)).1, (H 4 (by norm_num)).1, (H 5 (by norm_num)).1, (H 6 (by norm_num)).1, (H 7 (by norm_num)).1, (H 8 (by norm_num)).1, (H 9 (by norm_num)).1, (H 10 (by norm_num)).1, (H 11 (by norm_num)).1, (H 12 (by norm_num)).1, (H 13 (by norm_num)).1, (H 14 (by norm_num)).1, (H 15 (by norm_num)).1, (H 16 (by norm_num)).1]
    ring
  · simp only [LP, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := P6 0 (by norm_num); have := P6 1 (by norm_num); have := P6 2 (by norm_num); have := P6 3 (by norm_num); have := P6 4 (by norm_num); have := P6 5 (by norm_num); have := P6 6 (by norm_num); have := P6 7 (by norm_num)
    have := (H 8 (by norm_num)).2.2.1; have := (H 9 (by norm_num)).2.2.1; have := (H 10 (by norm_num)).2.2.1; have := (H 11 (by norm_num)).2.2.1; have := (H 12 (by norm_num)).2.2.1; have := (H 13 (by norm_num)).2.2.1; have := (H 14 (by norm_num)).2.2.1; have := (H 15 (by norm_num)).2.2.1; have := (H 16 (by norm_num)).2.2.1
    omega
  · simp only [LD, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := D5 8 (by norm_num); have := D5 9 (by norm_num); have := D5 10 (by norm_num); have := D5 11 (by norm_num); have := D5 12 (by norm_num); have := D5 13 (by norm_num); have := D5 14 (by norm_num); have := D5 15 (by norm_num); have := D5 16 (by norm_num)
    have := (H 0 (by norm_num)).2.2.2.1; have := (H 1 (by norm_num)).2.2.2.1; have := (H 2 (by norm_num)).2.2.2.1; have := (H 3 (by norm_num)).2.2.2.1; have := (H 4 (by norm_num)).2.2.2.1; have := (H 5 (by norm_num)).2.2.2.1; have := (H 6 (by norm_num)).2.2.2.1; have := (H 7 (by norm_num)).2.2.2.1
    omega
  · simp only [LZ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.2.2.2.1; have := (H 1 (by norm_num)).2.2.2.2.1; have := (H 2 (by norm_num)).2.2.2.2.1; have := (H 3 (by norm_num)).2.2.2.2.1; have := (H 4 (by norm_num)).2.2.2.2.1; have := (H 5 (by norm_num)).2.2.2.2.1; have := (H 6 (by norm_num)).2.2.2.2.1; have := (H 7 (by norm_num)).2.2.2.2.1; have := (H 8 (by norm_num)).2.2.2.2.1; have := (H 9 (by norm_num)).2.2.2.2.1; have := (H 10 (by norm_num)).2.2.2.2.1; have := (H 11 (by norm_num)).2.2.2.2.1; have := (H 12 (by norm_num)).2.2.2.2.1; have := (H 13 (by norm_num)).2.2.2.2.1; have := (H 14 (by norm_num)).2.2.2.2.1; have := (H 15 (by norm_num)).2.2.2.2.1; have := (H 16 (by norm_num)).2.2.2.2.1
    omega
  · simp only [LS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.2.2.1
    have := (H 0 (by norm_num)).2.2.2.2.2; have := (H 1 (by norm_num)).2.2.2.2.2; have := (H 2 (by norm_num)).2.2.2.2.2; have := (H 3 (by norm_num)).2.2.2.2.2; have := (H 4 (by norm_num)).2.2.2.2.2; have := (H 5 (by norm_num)).2.2.2.2.2; have := (H 6 (by norm_num)).2.2.2.2.2; have := (H 7 (by norm_num)).2.2.2.2.2; have := (H 8 (by norm_num)).2.2.2.2.2; have := (H 9 (by norm_num)).2.2.2.2.2; have := (H 10 (by norm_num)).2.2.2.2.2; have := (H 11 (by norm_num)).2.2.2.2.2; have := (H 12 (by norm_num)).2.2.2.2.2; have := (H 13 (by norm_num)).2.2.2.2.2; have := (H 14 (by norm_num)).2.2.2.2.2; have := (H 15 (by norm_num)).2.2.2.2.2; have := (H 16 (by norm_num)).2.2.2.2.2
    omega
  · simp only [LW, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := (H 0 (by norm_num)).2.1; have := (H 1 (by norm_num)).2.1; have := (H 2 (by norm_num)).2.1; have := (H 3 (by norm_num)).2.1; have := (H 4 (by norm_num)).2.1; have := (H 5 (by norm_num)).2.1; have := (H 6 (by norm_num)).2.1; have := (H 7 (by norm_num)).2.1; have := (H 8 (by norm_num)).2.1; have := (H 9 (by norm_num)).2.1; have := (H 10 (by norm_num)).2.1; have := (H 11 (by norm_num)).2.1; have := (H 12 (by norm_num)).2.1; have := (H 13 (by norm_num)).2.1; have := (H 14 (by norm_num)).2.1; have := (H 15 (by norm_num)).2.1; have := (H 16 (by norm_num)).2.1
    omega
  · unfold kPen LPen
    rw [(H 8 (by norm_num)).1, (H 10 (by norm_num)).1, (H 11 (by norm_num)).1, (H 12 (by norm_num)).1]
    obtain ⟨_, _, p8, _, z8, s8⟩ := H 8 (by norm_num); have d8 := D5 8 (by norm_num)
    obtain ⟨_, _, p10, _, z10, s10⟩ := H 10 (by norm_num); have d10 := D5 10 (by norm_num)
    obtain ⟨_, _, p11, _, z11, s11⟩ := H 11 (by norm_num); have d11 := D5 11 (by norm_num)
    obtain ⟨_, _, p12, _, z12, s12⟩ := H 12 (by norm_num); have d12 := D5 12 (by norm_num)
    omega
theorem kSum_lt (v : Digest) : kS9 v + kPen v < 2 ^ 62 := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v; omega
theorem kSum_W (v : Digest) : (kS9 v + kPen v) / 2 ^ 22 = LW v := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v; omega
theorem kSum_Z (v : Digest) : (kS9 v + kPen v) / 2 ^ 8 % 64 = LZ v := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v; omega
theorem kSum_S (v : Digest) : (kS9 v + kPen v) % 256 = LS v + 4 * eD (gIdx v 0) := by
  obtain ⟨h, h1, h2, h3, h4, h5, _⟩ := kLanes v; omega
theorem LW_le (v : Digest) : LW v ≤ 4352 := (kLanes v).2.2.2.2.2.1
theorem LPen_le (v : Digest) : LPen v ≤ 4 := by
  unfold LPen
  have a := (r6Entry_lanes _ (gIdx_lt v 8)).2.2.1; have b := (r6Entry_lanes _ (gIdx_lt v 10)).2.2.1
  have c := (r6Entry_lanes _ (gIdx_lt v 11)).2.2.1; have d := (r6Entry_lanes _ (gIdx_lt v 12)).2.2.1
  omega
theorem LSD_le (v : Digest) : LS v + 4 * eD (gIdx v 0) ≤ 140 := (kLanes v).2.2.2.2.1
/-! ### Branch-condition arithmetic -/
theorem window_bv (W : Nat) (hW : W < 2 ^ 62) :
    (BitVec.ofNat 64 153 - BitVec.ofNat 64 W).ult (BitVec.ofNat 64 8) = decide (W ≤ 153 ∧ 153 - W < 8) := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega)]
  by_cases h : W ≤ 153
  · simp only [h, true_and]
    rw [show 2 ^ 64 - W + 153 % 2 ^ 64 = 153 - W + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show 153 - W < 2 ^ 64 by omega)]
  · simp only [h, false_and, decide_false, decide_eq_false_iff_not]
    omega
theorem slt_sub (R P thr : Nat) (hR : R < 2 ^ 62) (hP : P < 2 ^ 62) (ht : thr < 2 ^ 62) :
    (BitVec.ofNat 64 R - BitVec.ofNat 64 P).slt (BitVec.ofNat 64 thr) = decide (R < P + thr) := by
  by_cases h : P ≤ R
  · rw [bv_sub R P h (by omega), ofNat_slt _ _ (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  · have hneg : (BitVec.ofNat 64 R - BitVec.ofNat 64 P).toInt < 0 := by
      rw [BitVec.toInt_eq_toNat_cond]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show R < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show P < 2 ^ 64 by omega)]
      split_ifs with h1 <;> omega
    have htp : (BitVec.ofNat 64 thr).toInt = thr := by
      rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
      rw [BitVec.msb_eq_decide]; simp; omega
    rw [BitVec.slt, htp]
    simp only [decide_eq_decide]
    constructor
    · intro _; omega
    · intro _; omega
theorem hi_slt (v : Digest) : (v.extractLsb' 64 64).slt 0 = decide (v.toNat / 2 ^ 127 % 2 = 1) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  simp only [decide_eq_decide]
  omega
/-! ### The half test -/
abbrev KL : List Reg := [.x11, .x25, .x28, .x29, .x30]
theorem pcOf_n (k n m : Nat) (hm : m = 4 * n) (h : 0x1000 + 4 * (k + n) < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 m = pcOf (k + n) := by
  subst hm; exact pcOf_plus k n h
theorem half_run {image : Image} {b : Nat} (hR : R6KAt image b) (s0 : MachineState)
    (hpc : s0.pc = pcOf (kBase b + 4)) (v : Digest)
    (h6 : s0.getReg .x6 = v.extractLsb' 0 64) (h7 : s0.getReg .x7 = v.extractLsb' 64 64)
    (h10 : s0.getReg .x10 = BitVec.ofNat 64 (tblBlk b + 160)) (h17 : s0.getReg .x17 = BitVec.ofNat 64 153)
    {thr : Nat} (hthr : thr < 2 ^ 62) (h21 : s0.getReg .x21 = BitVec.ofNat 64 thr) (ht : R6TableW (tblBlk b) s0) :
    ∃ k t, Steps image s0 k k t ∧ k ≤ 109 ∧ RegsExcept s0 t KL ∧ Frame s0 t (fun _ => False) ∧
      ((kAcc v thr ∧ k = 109 ∧ t.pc = pcOf (kBase b + 113) ∧
        t.getReg .x29 = BitVec.ofNat 64 (LS v + 4 * eD (gIdx v 0) + (if 153 - LW v = 6 then 1 else 0) - LPen v) ∧
        t.getReg .x28 = BitVec.ofNat 64 (153 - LW v)) ∨
       (¬ kAcc v thr ∧ t.pc = pcOf (kBase b + 119))) := by
  have hb := hR.1
  have hkb : kBase b < 2 ^ 20 := by rcases hb with rfl | rfl <;> simp [kBase]
  have hFm : ∀ {x y z : MachineState}, Frame x y (fun _ => False) → Frame y z (fun _ => False) →
      Frame x z (fun _ => False) := fun h1 h2 => (h1.trans h2).mono (fun _ _ h => by simpa using h)
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_blt _) (codeAt_kf hR 1 rfl) s0 hpc
  simp only [E.eval, CmpOp.eval, h7, hi_slt] at p1
  by_cases hsp : v.toNat / 2 ^ 127 % 2 = 1
  · refine ⟨1, u1, s1, by norm_num, r1.mono (by decide), f1, Or.inr ⟨fun h => by unfold kAcc at h; omega, ?_⟩⟩
    rw [p1, if_pos (decide_eq_true hsp), pcOf_n _ 115 _ rfl (by omega)]
  have p1' : u1.pc = pcOf (kBase b + 5) := by rw [p1, if_neg (by rw [decide_eq_true_eq]; exact hsp), pcOf_4]
  obtain ⟨u2, s2, p2, a25, a11, r2, f2⟩ := h1_run hR s0 u1 p1' v h6 h7 h10 ht (r1.mono (by decide)) f1
  have x17 : u2.getReg .x17 = BitVec.ofNat 64 153 := (r2 .x17 (by decide)).trans h17
  have hK := kSum_lt v
  obtain ⟨u3, s3, p3, b25, b11, b28, b29, r3, f3⟩ :=
    tot_spec (codeAt_kf hR 21 rfl) u2 p2 (by omega) a25 a11 x17
  rw [kSum_W v] at b28 b29
  rw [window_bv _ (by have := LW_le v; omega)] at b29
  rw [(kLanes v).2.2.2.2.2.2] at b11
  have r3' : RegsExcept s0 u3 KL := (r2.trans r3).mono (by decide)
  have f3' := hFm f2 f3
  have p3' : u3.pc = pcOf (kBase b + 100) := by rw [p3]; simp only [pcOf_4]
  obtain ⟨u4, s4, p4, r4, f4⟩ := br_spec (run_br100 _) (codeAt_kf hR 22 rfl) u3 p3'
  simp only [E.eval, CmpOp.eval, b29] at p4
  have r4' : RegsExcept s0 u4 KL := (r3'.trans r4).mono (by decide)
  have f4' := hFm f3' f4
  by_cases hw : LW v ≤ 153 ∧ 153 - LW v < 8
  swap
  · refine ⟨97, u4, ((((s1.trans s2).trans s3).trans s4)).of_eq rfl rfl, by norm_num, r4', f4',
      Or.inr ⟨fun h => hw ⟨h.2.1, h.2.2.1⟩, ?_⟩⟩
    rw [p4]
    simp only [hw, decide_false, Bool.false_eq_true, if_false]
    rw [if_pos (by decide), pcOf_n _ 19 _ rfl (by omega)]
  have p4' : u4.pc = pcOf (kBase b + 101) := by
    rw [p4]; simp only [hw, and_self, decide_true, if_true]; rw [if_neg (by decide), pcOf_4]
  have hd : 153 - LW v < 8 := hw.2
  have c28 : u4.getReg .x28 = BitVec.ofNat 64 (153 - LW v) := by
    rw [r4 .x28 (by decide), b28, bv_sub _ _ hw.1 (by norm_num)]
  have c25 : u4.getReg .x25 = BitVec.ofNat 64 (kS9 v + kPen v) := by rw [r4 .x25 (by decide), b25]
  have c11 : u4.getReg .x11 = BitVec.ofNat 64 (LPen v) := by rw [r4 .x11 (by decide), b11]
  obtain ⟨u5, s5, p5, d29, r5, f5⟩ := h2a_spec (codeAt_kf hR 23 rfl) u4 p4' (by omega) (by omega) c25 c28
  rw [kSum_Z] at d29
  have p5' : u5.pc = pcOf (kBase b + 106) := by rw [p5]; simp only [pcOf_4]
  obtain ⟨u6, s6, p6, r6, f6⟩ := br_spec (run_br106 _) (codeAt_kf hR 24 rfl) u5 p5'
  simp only [E.eval, CmpOp.eval, d29] at p6
  have r6' : RegsExcept s0 u6 KL := ((r4'.trans r5).trans r6).mono (by decide)
  have f6' := hFm (hFm f4' f5) f6
  by_cases hz : LZ v + (if 153 - LW v = 0 then 1 else 0) < 8
  swap
  · refine ⟨103, u6, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6)).of_eq rfl rfl, by norm_num,
      r6', f6', Or.inr ⟨fun h => hz (by have := h.2.2.2.1; omega), ?_⟩⟩
    rw [p6, if_neg hz, if_pos (by decide), pcOf_n _ 13 _ rfl (by omega)]
  have p6' : u6.pc = pcOf (kBase b + 107) := by rw [p6, if_pos hz, if_neg (by decide), pcOf_4]
  have e25 : u6.getReg .x25 = BitVec.ofNat 64 (kS9 v + kPen v) := by
    rw [r6 .x25 (by decide), r5 .x25 (by decide), c25]
  have e11 : u6.getReg .x11 = BitVec.ofNat 64 (LPen v) := by rw [r6 .x11 (by decide), r5 .x11 (by decide), c11]
  have e28 : u6.getReg .x28 = BitVec.ofNat 64 (153 - LW v) := by rw [r6 .x28 (by decide), r5 .x28 (by decide), c28]
  obtain ⟨u7, s7, p7, g29, r7, f7⟩ := h3a_spec (codeAt_kf hR 25 rfl) u6 p6' (by omega) (by omega) e25 e11 e28
  rw [kSum_S] at g29
  have p7' : u7.pc = pcOf (kBase b + 112) := by rw [p7]; simp only [pcOf_4]
  obtain ⟨u8, s8, p8, r8, f8⟩ := br_spec (run_br112 _) (codeAt_kf hR 26 rfl) u7 p7'
  have x21 : u7.getReg .x21 = BitVec.ofNat 64 thr := by
    rw [r7 .x21 (by decide), r6' .x21 (by decide), h21]
  have hSD := LSD_le v
  have hPl := LPen_le v
  simp only [E.eval, CmpOp.eval, g29, x21] at p8
  rw [slt_sub _ _ _ (by split_ifs <;> omega) (by omega) hthr] at p8
  have r8' : RegsExcept s0 u8 KL := ((r6'.trans r7).trans r8).mono (by decide)
  have f8' := hFm (hFm f6' f7) f8
  have hsteps : Steps image s0 109 109 u8 :=
    ((((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8)).of_eq rfl rfl
  by_cases hr : LS v + 4 * eD (gIdx v 0) + (if 153 - LW v = 6 then 1 else 0) < LPen v + thr
  · refine ⟨109, u8, hsteps, le_refl _, r8', f8', Or.inr ⟨fun h => by have := h.2.2.2.2; omega, ?_⟩⟩
    rw [p8, if_pos (by simp [hr]), pcOf_n _ 7 _ rfl (by omega)]
  · refine ⟨109, u8, hsteps, le_refl _, r8', f8', Or.inl ⟨⟨by omega, hw.1, hw.2, by omega, by omega⟩, rfl, ?_, ?_, ?_⟩⟩
    · rw [p8, if_neg (by simp [hr]), pcOf_4]
    · rw [r8 .x29 (by decide), g29, bv_sub _ _ (by omega) (by split_ifs <;> omega)]
    · rw [r8 .x28 (by decide), r7 .x28 (by decide), e28]
/-! ### Accept / reject tails -/
theorem pcOf_m (k n m : Nat) (hm : m = 2 ^ 64 - 4 * n) (hn : n ≤ k) (h : 0x1000 + 4 * k < 2 ^ 64) :
    pcOf k + BitVec.ofNat 64 m = pcOf (k - n) := by
  subst hm; exact pcOf_minus k n hn h
theorem j118_spec {image : Image} {b : Nat} (hR : R6KAt image b) (w : MachineState)
    (hpc : w.pc = pcOf (kBase b + 118)) :
    ∃ t, Steps image w 1 1 t ∧ t.pc = pcOf (uBase b) ∧ RegsExcept w t [] ∧ Frame w t (fun _ => False) := by
  have hc := codeAt_kf hR 30 rfl
  rcases hR.1 with rfl | rfl
  · obtain ⟨t, st, pt, rt, ft⟩ := jal_spec (run_j118E _) hc w hpc
    exact ⟨t, st, by rw [pt, pcOf_n _ 282 _ rfl (by norm_num)]; rfl, rt, ft⟩
  · obtain ⟨t, st, pt, rt, ft⟩ := jal_spec (run_j118S _) hc w hpc
    exact ⟨t, st, by rw [pt, pcOf_m _ 20027 18446744073709471508 (by norm_num) (by norm_num) (by norm_num)]; rfl, rt, ft⟩
theorem jN_spec {image : Image} {b : Nat} (hR : R6KAt image b) (w : MachineState)
    (hpc : w.pc = pcOf (kBase b + 127)) :
    ∃ t, Steps image w 1 1 t ∧ t.pc = pcOf (b + 468) ∧ RegsExcept w t [] ∧ Frame w t (fun _ => False) := by
  have hc := codeAt_kf hR 36 rfl
  rcases hR.1 with rfl | rfl
  · obtain ⟨t, st, pt, rt, ft⟩ := jal_spec (run_jNE _) hc w hpc
    exact ⟨t, st, by rw [pt, pcOf_m _ 48531 18446744073709357492 (by norm_num) (by norm_num) (by norm_num)]; rfl, rt, ft⟩
  · obtain ⟨t, st, pt, rt, ft⟩ := jal_spec (run_jNS _) hc w hpc
    exact ⟨t, st, by rw [pt, pcOf_m _ 20783 18446744073709468484 (by norm_num) (by norm_num) (by norm_num)]; rfl, rt, ft⟩
/-- Accept with the flag `x20` (0 = LOW: `+3` path bonus; 128 = HIGH). -/
theorem accept_tail {image : Image} {b : Nat} (hR : R6KAt image b) (w : MachineState)
    (hpc : w.pc = pcOf (kBase b + 113)) (low : Bool) (h20 : w.getReg .x20 = BitVec.ofNat 64 (if low then 0 else 128)) :
    ∃ k t, Steps image w k k t ∧ k ≤ 6 ∧ t.pc = pcOf (uBase b) ∧
      t.getMem (BitVec.ofNat 64 (creditAddr b)) = w.getReg .x29 + BitVec.ofNat 64 (if low then 3 else 0) ∧
      t.getMem (BitVec.ofNat 64 FLAGA) = w.getReg .x20 ∧
      RegsExcept w t [.x29, .x30] ∧ Frame w t (fun A => A = creditAddr b ∨ A = FLAGA) := by
  have hkb : kBase b < 2 ^ 20 := by rcases hR.1 with rfl | rfl <;> simp [kBase]
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brA0 _) (codeAt_kf hR 27 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  cases low
  · have p1' : u1.pc = pcOf (kBase b + 115) := by
      rw [p1, if_pos (by decide), pcOf_n _ 2 _ rfl (by omega)]
    obtain ⟨u2, s2, p2, m1, m2, r2, f2⟩ := a2a_spec hR.1 (codeAt_kf hR 29 rfl) u1 p1'
    obtain ⟨u3, s3, p3, r3, f3⟩ := j118_spec hR u2 p2
    refine ⟨5, u3, ((s1.trans s2).trans s3).of_eq rfl rfl, by norm_num, p3, ?_, ?_, ?_, ?_⟩
    · rw [f3.get (by simp [creditAddr]; split_ifs <;> norm_num) (fun h => h), m1, r1 .x29 (by decide)]
      simp
    · rw [f3.get (by norm_num) (fun h => h), m2, r1 .x20 (by decide)]
    · exact ((r1.trans r2).trans r3).mono (by decide)
    · exact ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h; exact h)
  · have p1' : u1.pc = pcOf (kBase b + 114) := by
      rw [p1, if_neg (by decide), pcOf_4]
    obtain ⟨u2, s2, p2, x29, r2, f2⟩ := a1_spec (codeAt_kf hR 28 rfl) u1 p1'
    have p2' : u2.pc = pcOf (kBase b + 115) := by rw [p2, pcOf_4]
    obtain ⟨u3, s3, p3, m1, m2, r3, f3⟩ := a2a_spec hR.1 (codeAt_kf hR 29 rfl) u2 p2'
    obtain ⟨u4, s4, p4, r4, f4⟩ := j118_spec hR u3 p3
    refine ⟨6, u4, (((s1.trans s2).trans s3).trans s4).of_eq rfl rfl, le_refl _, p4, ?_, ?_, ?_, ?_⟩
    · rw [f4.get (by simp [creditAddr]; split_ifs <;> norm_num) (fun h => h), m1, x29, r1 .x29 (by decide)]
      rfl
    · rw [f4.get (by norm_num) (fun h => h), m2, r2 .x20 (by decide), r1 .x20 (by decide)]
    · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
    · exact (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h; tauto)
theorem reject_high {image : Image} {b : Nat} (hR : R6KAt image b) (w : MachineState)
    (hpc : w.pc = pcOf (kBase b + 119)) (h20 : w.getReg .x20 = BitVec.ofNat 64 128) :
    ∃ t, Steps image w 2 2 t ∧ t.pc = pcOf (b + 468) ∧ RegsExcept w t [] ∧ Frame w t (fun _ => False) := by
  have hkb : kBase b < 2 ^ 20 := by rcases hR.1 with rfl | rfl <;> simp [kBase]
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brF0 _) (codeAt_kf hR 31 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  have p1' : u1.pc = pcOf (kBase b + 127) := by rw [p1, if_pos (by decide), pcOf_n _ 8 _ rfl (by omega)]
  obtain ⟨u2, s2, p2, r2, f2⟩ := jN_spec hR u1 p1'
  exact ⟨u2, (s1.trans s2).of_eq rfl rfl, p2, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (fun _ _ h => by simp at h)⟩
theorem blocked_bv (v : Digest) :
    (v.extractLsb' 64 64 >>> 62 == (0 : Word)) = decide (v.toNat < 2 ^ 126) := by
  have hv := v.isLt
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, h0] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, h0]
    omega
theorem reject_low {image : Image} {b : Nat} (hR : R6KAt image b) (w : MachineState)
    (hpc : w.pc = pcOf (kBase b + 119)) (h20 : w.getReg .x20 = 0) (v : Digest)
    (h7 : w.getReg .x7 = v.extractLsb' 64 64) (h12 : w.getReg .x12 = BitVec.ofNat 64 EOUT) :
    (v.toNat < 2 ^ 126 → ∃ t, Steps image w 4 4 t ∧ t.pc = pcOf (b + 468) ∧ RegsExcept w t [.x29] ∧
      Frame w t (fun _ => False)) ∧
    (¬ v.toNat < 2 ^ 126 → ∃ t, Steps image w 8 8 t ∧ t.pc = pcOf (kBase b + 4) ∧
      t.getReg .x6 = w.getMem (BitVec.ofNat 64 (EOUT + 16)) ∧ t.getReg .x7 = w.getMem (BitVec.ofNat 64 (EOUT + 24)) ∧
      t.getReg .x20 = BitVec.ofNat 64 128 ∧ t.getReg .x21 = BitVec.ofNat 64 kFloor ∧
      RegsExcept w t [.x6, .x7, .x20, .x21, .x29] ∧ Frame w t (fun _ => False)) := by
  have hkb : kBase b < 2 ^ 20 := by rcases hR.1 with rfl | rfl <;> simp [kBase]
  obtain ⟨u1, s1, p1, r1, f1⟩ := br_spec (run_brF0 _) (codeAt_kf hR 31 rfl) w hpc
  simp only [E.eval, CmpOp.eval, h20] at p1
  have p1' : u1.pc = pcOf (kBase b + 120) := by rw [p1, if_neg (by decide), pcOf_4]
  obtain ⟨u2, s2, p2, x29, r2, f2⟩ := f1a_spec (codeAt_kf hR 32 rfl) u1 p1'
  rw [r1 .x7 (by decide), h7] at x29
  have p2' : u2.pc = pcOf (kBase b + 121) := by rw [p2, pcOf_4]
  obtain ⟨u3, s3, p3, r3, f3⟩ := br_spec (run_br121 _) (codeAt_kf hR 33 rfl) u2 p2'
  simp only [E.eval, CmpOp.eval, x29, blocked_bv] at p3
  constructor
  · intro hbl
    have p3' : u3.pc = pcOf (kBase b + 127) := by
      rw [p3, if_pos (decide_eq_true hbl), pcOf_n _ 6 _ rfl (by omega)]
    obtain ⟨u4, s4, p4, r4, f4⟩ := jN_spec hR u3 p3'
    exact ⟨u4, (((s1.trans s2).trans s3).trans s4).of_eq rfl rfl, p4,
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h)⟩
  · intro hbl
    have p3' : u3.pc = pcOf (kBase b + 122) := by
      rw [p3, if_neg (by rw [decide_eq_true_eq]; exact hbl), pcOf_4]
    have x12 : u3.getReg .x12 = BitVec.ofNat 64 EOUT := by
      rw [r3 .x12 (by decide), r2 .x12 (by decide), r1 .x12 (by decide), h12]
    obtain ⟨u4, s4, p4, y6, y7, y20, y21, r4, f4⟩ := f2a_spec hR.1 (codeAt_kf hR 34 rfl) u3 p3' x12
    obtain ⟨u5, s5, p5, r5, f5⟩ := jal_spec (run_j126 _) (codeAt_kf hR 35 rfl) u4 p4
    have hF : Frame w u3 (fun _ => False) := ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h)
    refine ⟨u5, ((((s1.trans s2).trans s3).trans s4).trans s5).of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [p5, pcOf_m _ 122 18446744073709551128 (by norm_num) (by omega) (by omega)]; congr 1
    · rw [r5 .x6 (by decide), y6, hF.get (by norm_num) (fun h => h)]
    · rw [r5 .x7 (by decide), y7, hF.get (by norm_num) (fun h => h)]
    · rw [r5 .x20 (by decide), y20]
    · rw [r5 .x21 (by decide), y21]
    · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
    · exact ((hF.trans f4).trans f5).mono (fun _ _ h => by simp at h)
/-! ### Spec side of the trial -/
theorem credit_lanes {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) (low : Bool) :
    WCT9.CanonicalPolicy.credit 0 low ds =
      LS v + 4 * eD (gIdx v 0) + (if 153 - LW v = 6 then 1 else 0) + (if low then 3 else 0) - LPen v := by
  rw [WCT9.CanonicalPolicy.credit_top, reward_lanes h, penalty_lanes h]
theorem producerDecodeAt_kAcc (v : Digest) (low : Bool) :
    (WCT9.CanonicalPolicy.producerDecodeAt 0 kFloor low v).isSome = true ↔
      kAcc v (if low then 16 else 19) := by
  constructor
  · intro h
    obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.1 h
    have := ((producer_some v kFloor low (by norm_num [kFloor]) ds).1 hds).1
    cases low <;> simpa [kFloor] using this
  · intro h
    have hk : kAcc v (kFloor - if low then 3 else 0) := by cases low <;> simpa [kFloor] using h
    rw [(producer_some v kFloor low (by norm_num [kFloor]) _).2 ⟨hk, kAcc_decode hk⟩]
    rfl
theorem producerDecodeAt_some {v : Digest} {low : Bool} (h : kAcc v (if low then 16 else 19)) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 kFloor low v = some (T3.dataDigits 0 v ++ [153 - LW v]) := by
  have hk : kAcc v (kFloor - if low then 3 else 0) := by cases low <;> simpa [kFloor] using h
  exact (producer_some v kFloor low (by norm_num [kFloor]) _).2 ⟨hk, kAcc_decode hk⟩
theorem producerDecodeAt_none {v : Digest} {low : Bool} (h : ¬ kAcc v (if low then 16 else 19)) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 kFloor low v = none := by
  cases hp : WCT9.CanonicalPolicy.producerDecodeAt 0 kFloor low v with
  | none => rfl
  | some ds => exact absurd ((producerDecodeAt_kAcc v low).1 (by rw [hp]; rfl)) h
theorem topGood_iff (hfl : WCT9.CanonicalPolicy.topFloor = kFloor) (w : Digest) : WCT9.topGood w ↔ kAcc w 16 := by
  unfold WCT9.topGood
  rw [hfl]
  exact producerDecodeAt_kAcc w true
theorem ds_getD51_of {v : Digest} {ds : List Nat} (h : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.getD 51 0 = 153 - LW v := by
  rw [ds_getD_51 h, dataDigits_sum_LW (decode_top_eq h).1]
/-- One R6 top trial from `K_ENTRY` on the 256-bit answer `a` (LOW half in `x6`, `x7`; `x12` = EOUT holds `a`):
accept exactly the canonical producer answer (`producerDecodeOut 0 kFloor`), storing the credit and the choice flag
and entering `U_ENTRY` with the selected word and its checksum digit, or reject into `b + 468` without a store.
Needs `topFloor = kFloor` (the restricted choice reads `topGood` at `topFloor`; RC constants). -/
theorem trial {image : Image} {b : Nat} (hR : R6KAt image b)
    (hfl : WCT9.CanonicalPolicy.topFloor = kFloor) (u : MachineState) (hpc : u.pc = pcOf (kBase b))
    (a : BitVec 256) (h6 : u.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : u.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64) (h12 : u.getReg .x12 = BitVec.ofNat 64 EOUT)
    (hH0 : u.getMem (BitVec.ofNat 64 (EOUT + 16)) = (a.extractLsb' 128 128).extractLsb' 0 64)
    (hH8 : u.getMem (BitVec.ofNat 64 (EOUT + 24)) = (a.extractLsb' 128 128).extractLsb' 64 64)
    (h17 : u.getReg .x17 = BitVec.ofNat 64 (T3.target 0)) (ht : R6TableW (tblBlk b) u) :
    (∀ ds low, WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a = some (ds, low) →
      ∃ k t, Steps image u k k t ∧ k ≤ 240 ∧ t.pc = pcOf (uBase b) ∧
        t.getReg .x6 = (WCT9.encodingAnswer 0 a).extractLsb' 0 64 ∧
        t.getReg .x7 = (WCT9.encodingAnswer 0 a).extractLsb' 64 64 ∧
        WCT9.CanonicalPolicy.decode 0 (WCT9.encodingAnswer 0 a) = some ds ∧
        t.getReg .x28 = BitVec.ofNat 64 (ds.getD 51 0) ∧
        t.getMem (BitVec.ofNat 64 (creditAddr b)) = BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit 0 low ds) ∧
        t.getMem (BitVec.ofNat 64 FLAGA) = BitVec.ofNat 64 (if low then 0 else 128) ∧
        RegsExcept u t kRegs ∧ Frame u t (fun A => A = creditAddr b ∨ A = FLAGA)) ∧
    (WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a = none →
      ∃ k t, Steps image u k k t ∧ k ≤ 240 ∧ t.pc = pcOf (b + 468) ∧ RegsExcept u t kRegs ∧
        Frame u t (fun _ => False)) := by
  have hb := hR.1
  have hbb : tblBlk b + 1696 < 2 ^ 64 := by rcases hb with rfl | rfl <;> simp [tblBlk]
  have hFm : ∀ {x y z : MachineState}, Frame x y (fun _ => False) → Frame y z (fun _ => False) →
      Frame x z (fun _ => False) := fun h1 h2 => (h1.trans h2).mono (fun _ _ h => by simpa using h)
  have hEA : WCT9.encodingAnswer 0 a =
      if WCT9.topChooseLow a then a.extractLsb' 0 128 else a.extractLsb' 128 128 := WCT9.encodingAnswer_top_eq a
  have hPDO : WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a =
      (WCT9.CanonicalPolicy.producerDecodeAt 0 kFloor (WCT9.topChooseLow a) (WCT9.encodingAnswer 0 a)).map
        (fun d => (d, WCT9.topChooseLow a)) := rfl
  obtain ⟨w1, s1, p1, e10, e20, e21, r1, f1⟩ := e0_spec hb (codeAt_kf hR 0 rfl) u hpc
  have ht1 : R6TableW (tblBlk b) w1 := ht.frame f1 hbb (fun _ _ h => h)
  have w6 : w1.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64 := (r1 .x6 (by decide)).trans h6
  have w7 : w1.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := (r1 .x7 (by decide)).trans h7
  have w17 : w1.getReg .x17 = BitVec.ofNat 64 153 := (r1 .x17 (by decide)).trans h17
  obtain ⟨k2, w2, s2, hk2, r2, f2, hres⟩ :=
    half_run hR w1 p1 (a.extractLsb' 0 128) w6 w7 e10 w17 (thr := 16) (by norm_num) e21 ht1
  rcases hres with ⟨hacc, _, p2, x29, x28⟩ | ⟨hrej, p2⟩
  · -- LOW accepted
    have hTC : WCT9.topChooseLow a = true :=
      decide_eq_true (Or.inl ((topGood_iff hfl _).2 hacc))
    have hdec := kAcc_decode hacc
    have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a =
        some (T3.dataDigits 0 (a.extractLsb' 0 128) ++ [153 - LW (a.extractLsb' 0 128)], true) := by
      rw [hPDO, hTC, hEA, hTC, if_pos rfl, producerDecodeAt_some (low := true) hacc]; rfl
    have hea : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by rw [hEA, hTC, if_pos rfl]
    have w20 : w2.getReg .x20 = BitVec.ofNat 64 (if true then 0 else 128) := by rw [r2 .x20 (by decide), e20]; rfl
    obtain ⟨k3, w3, s3, hk3, p3, m1, m2, r3, f3⟩ := accept_tail hR w2 p2 true w20
    refine ⟨fun ds low h => ?_, fun h => (by rw [hpdo] at h; cases h)⟩
    rw [hpdo] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨4 + k2 + k3, w3, (s1.trans s2).trans s3, by omega, p3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r3 .x6 (by decide), r2 .x6 (by decide), w6, hea]
    · rw [r3 .x7 (by decide), r2 .x7 (by decide), w7, hea]
    · rw [hea]; exact hdec
    · rw [r3 .x28 (by decide), x28, ds_getD51_of hdec]
    · rw [m1, x29, credit_lanes hdec true, ofNat_add_ofNat]
      have := hacc.2.2.2.2
      apply congrArg (BitVec.ofNat 64)
      simp only [if_true]
      omega
    · rw [m2, r2 .x20 (by decide), e20]; rfl
    · exact ((r1.trans r2).trans r3).mono (by decide)
    · exact ((hFm f1 f2).trans f3).mono (fun _ _ h => by simpa using h)
  · -- LOW rejected
    have w20 : w2.getReg .x20 = 0 := by rw [r2 .x20 (by decide), e20]
    have w7' : w2.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := (r2 .x7 (by decide)).trans w7
    have w12 : w2.getReg .x12 = BitVec.ofNat 64 EOUT := by
      rw [r2 .x12 (by decide), r1 .x12 (by decide), h12]
    obtain ⟨hblk, hnblk⟩ := reject_low hR w2 p2 w20 (a.extractLsb' 0 128) w7' w12
    by_cases hbl : (a.extractLsb' 0 128).toNat < 2 ^ 126
    · obtain ⟨w3, s3, p3, r3, f3⟩ := hblk hbl
      have hTC : WCT9.topChooseLow a = true := decide_eq_true (Or.inr hbl)
      have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a = none := by
        rw [hPDO, hTC, hEA, hTC, if_pos rfl, producerDecodeAt_none (low := true) hrej]; rfl
      refine ⟨fun ds low h => (by rw [hpdo] at h; cases h), fun _ => ⟨4 + k2 + 4, w3, (s1.trans s2).trans s3,
        by omega, p3, ((r1.trans r2).trans r3).mono (by decide), hFm (hFm f1 f2) f3⟩⟩
    · obtain ⟨w3, s3, p3, y6, y7, y20, y21, r3, f3⟩ := hnblk hbl
      have hTC : WCT9.topChooseLow a = false := by
        unfold WCT9.topChooseLow
        exact decide_eq_false (by rintro (h | h); exact hrej ((topGood_iff hfl _).1 h); exact hbl h)
      have hea : WCT9.encodingAnswer 0 a = a.extractLsb' 128 128 := by rw [hEA, hTC]; rfl
      have hF2 : Frame u w2 (fun _ => False) := hFm f1 f2
      have hF3 : Frame u w3 (fun _ => False) := hFm hF2 f3
      have v6 : w3.getReg .x6 = (a.extractLsb' 128 128).extractLsb' 0 64 := by
        rw [y6, hF2.get (by norm_num) (fun h => h), hH0]
      have v7 : w3.getReg .x7 = (a.extractLsb' 128 128).extractLsb' 64 64 := by
        rw [y7, hF2.get (by norm_num) (fun h => h), hH8]
      have v10 : w3.getReg .x10 = BitVec.ofNat 64 (tblBlk b + 160) := by
        rw [r3 .x10 (by decide), r2 .x10 (by decide), e10]
      have v17 : w3.getReg .x17 = BitVec.ofNat 64 153 := by rw [r3 .x17 (by decide), r2 .x17 (by decide), w17]
      have ht3 : R6TableW (tblBlk b) w3 := ht.frame hF3 hbb (fun _ _ h => h)
      obtain ⟨k4, w4, s4, hk4, r4, f4, hres2⟩ :=
        half_run hR w3 p3 (a.extractLsb' 128 128) v6 v7 v10 v17 (thr := 19) (by norm_num) y21 ht3
      have w20' : w4.getReg .x20 = BitVec.ofNat 64 128 := by rw [r4 .x20 (by decide), y20]
      rcases hres2 with ⟨hacc2, _, p4, x29, x28⟩ | ⟨hrej2, p4⟩
      · have hdec := kAcc_decode hacc2
        have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a =
            some (T3.dataDigits 0 (a.extractLsb' 128 128) ++ [153 - LW (a.extractLsb' 128 128)], false) := by
          rw [hPDO, hTC, hea, producerDecodeAt_some (low := false) hacc2]; rfl
        obtain ⟨k5, w5, s5, hk5, p5, m1, m2, r5, f5⟩ := accept_tail hR w4 p4 false (by rw [w20']; rfl)
        refine ⟨fun ds low h => ?_, fun h => (by rw [hpdo] at h; cases h)⟩
        rw [hpdo] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨4 + k2 + 8 + k4 + k5, w5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [r5 .x6 (by decide), r4 .x6 (by decide), v6, hea]
        · rw [r5 .x7 (by decide), r4 .x7 (by decide), v7, hea]
        · rw [hea]; exact hdec
        · rw [r5 .x28 (by decide), x28, ds_getD51_of hdec]
        · rw [m1, x29, credit_lanes hdec false, ofNat_add_ofNat]
          have := hacc2.2.2.2.2
          apply congrArg (BitVec.ofNat 64)
          simp only [Bool.false_eq_true, if_false]
          omega
        · rw [m2, w20']; rfl
        · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
        · exact ((hFm hF3 f4).trans f5).mono (fun _ _ h => by simpa using h)
      · have hpdo : WCT9.CanonicalPolicy.producerDecodeOut 0 kFloor a = none := by
          rw [hPDO, hTC, hea, producerDecodeAt_none (low := false) hrej2]; rfl
        obtain ⟨w5, s5, p5, r5, f5⟩ := reject_high hR w4 p4 w20'
        refine ⟨fun ds low h => (by rw [hpdo] at h; cases h), fun _ => ⟨4 + k2 + 8 + k4 + 2, w5,
          (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
          ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide), hFm (hFm hF3 f4) f5⟩⟩

/-! ### Unpacker -/
theorem bv_remu (n r : Nat) (hn : n < 2 ^ 64) (hr : 0 < r) (hr' : r < 2 ^ 64) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 r) = BitVec.ofNat 64 (n % r) := by
  unfold rv64_remu
  have h0 : (BitVec.ofNat 64 r == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [h0]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, toNat_ofNat_lt hn, toNat_ofNat_lt hr', toNat_ofNat_lt (by
    exact lt_of_le_of_lt (Nat.mod_le _ _) hn)]
theorem bv_divu (n r : Nat) (hn : n < 2 ^ 64) (hr : 0 < r) (hr' : r < 2 ^ 64) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 r) = BitVec.ofNat 64 (n / r) := by
  unfold rv64_divu
  have h0 : (BitVec.ofNat 64 r == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [h0]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofNat_lt hn, toNat_ofNat_lt hr', toNat_ofNat_lt (by
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
theorem trunc8 (x : Nat) : (BitVec.ofNat 64 x).truncate 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
/-- The 7-instruction digit split `remu t4,t3,R ; sb t4,o(a0) ; divu t3,t3,R ; remu t4,t3,R ; sb t4,o+1(a0) ;
divu t4,t3,R ; sb t4,o+2(a0)` (radix `r` in register `R`). -/
theorem split7 {image : Image} {s : MachineState} {pc : Word} {w0 w1 w2 w3 w4 w5 w6 : BitVec 32} {R : Reg}
    {f1 f2 f3 : BitVec 12} {o r n : Nat}
    (hc : CodeAt image pc [w0, w1, w2, w3, w4, w5, w6]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some (.base (.REMU .x29 .x28 R)))
    (hd1 : decodeInstruction w1 = some (.base (.SB .x10 .x29 f1)))
    (hd2 : decodeInstruction w2 = some (.base (.DIVU .x28 .x28 R)))
    (hd3 : decodeInstruction w3 = some (.base (.REMU .x29 .x28 R)))
    (hd4 : decodeInstruction w4 = some (.base (.SB .x10 .x29 f2)))
    (hd5 : decodeInstruction w5 = some (.base (.DIVU .x29 .x28 R)))
    (hd6 : decodeInstruction w6 = some (.base (.SB .x10 .x29 f3)))
    (hR : R ≠ .x0 ∧ R ≠ .x28 ∧ R ≠ .x29)
    (ho1 : signExtend12 f1 = BitVec.ofNat 64 o) (ho2 : signExtend12 f2 = BitVec.ofNat 64 (o + 1))
    (ho3 : signExtend12 f3 = BitVec.ofNat 64 (o + 2)) (ho : o + 2 < 64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 DIGITS) (hRv : s.getReg R = BitVec.ofNat 64 r) (hr : 0 < r ∧ r < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ t, Steps image s 7 19 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + o)) = BitVec.ofNat 8 (n % r) ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + (o + 1))) = BitVec.ofNat 8 (n / r % r) ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + (o + 2))) = BitVec.ofNat 8 (n / r / r) ∧
      (∀ B, B < 2 ^ 64 → ¬ (DIGITS + o ≤ B ∧ B < DIGITS + o + 3) →
        t.getByte (BitVec.ofNat 64 B) = s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
  have hD : DIGITS = 0x20420 := rfl
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have c1 := hc.tail
  have c2 := c1.tail
  have c3 := c2.tail
  have c4 := c3.tail
  have c5 := c4.tail
  have c6 := c5.tail
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have hnr : n % r < 2 ^ 64 := by have := Nat.mod_lt n hr.1; omega
  have hn1 : n / r < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have hn1r : n / r % r < 2 ^ 64 := by have := Nat.mod_lt (n / r) hr.1; omega
  have hn2 : n / r / r < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn1
  have hR' : r < 2 ^ 64 := by omega
  have hA : ∀ k, k < 3 → accessValid (BitVec.ofNat 64 DIGITS + BitVec.ofNat 64 (o + k)) 1 = true := by
    intro k hk
    rw [ofNat_add_ofNat]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show DIGITS + (o + k) < 2 ^ 64 by omega)]
    omega
  -- step 0: remu t4, t3, R
  have st0 := step_alu (hd hc) hpc hd0 rfl
  generalize hu1 : (s.setReg .x29 (BinOp.remu.eval ((Src.reg .x28).eval s) ((Src.reg R).eval s))).setPC
    (s.pc + 4) = u1 at st0
  have g1_29 : u1.getReg .x29 = BitVec.ofNat 64 (n % r) := by
    rw [← hu1, getReg_setPC', geq _ _ _ (by decide)]
    show rv64_remu (s.getReg .x28) (s.getReg R) = _
    rw [h28, hRv, bv_remu _ _ hn hr.1 hR']
  have g1 : ∀ q, q ≠ .x29 → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, getReg_setPC', gne _ _ _ _ hq]
  have p1 : u1.pc = pc + 4 := by rw [← hu1]; show s.pc + 4 = _; rw [hpc]
  have b1 : ∀ a, u1.getByte a = s.getByte a := fun a => by rw [← hu1, getByte_setPC, getByte_setReg]
  have m1 : ∀ a, u1.getMem a = s.getMem a := fun a => by rw [← hu1, getMem_setPC']; cases (Reg.x29 : Reg) <;> rfl
  -- step 1: sb t4, o(a0)
  have v1 : accessValid (u1.getReg .x10 + signExtend12 f1) 1 = true := by
    rw [g1 .x10 (by decide), h10, ho1, show o = o + 0 by omega]; exact hA 0 (by norm_num)
  have st1 := steps_sb (hd c1) p1 hd1 v1
  generalize hu2 : (u1.setByte (u1.getReg .x10 + signExtend12 f1) ((u1.getReg .x29).truncate 8)).setPC
    (u1.pc + 4) = u2 at st1
  have a1 : u1.getReg .x10 + signExtend12 f1 = BitVec.ofNat 64 (DIGITS + o) := by
    rw [g1 .x10 (by decide), h10, ho1, ofNat_add_ofNat]
  have g2 : ∀ q, u2.getReg q = u1.getReg q := fun q => by rw [← hu2, getReg_setPC', getReg_setByte]
  have p2 : u2.pc = pc + 4 + 4 := by rw [← hu2]; show u1.pc + 4 = _; rw [p1]
  have b2 : ∀ B, B < 2 ^ 64 → u2.getByte (BitVec.ofNat 64 B) =
      if B = DIGITS + o then BitVec.ofNat 8 (n % r) else u1.getByte (BitVec.ofNat 64 B) := fun B hB => by
    rw [← hu2, getByte_setPC, a1, g1_29, trunc8, getByte_setByte _ _ _ (by omega) hB]
  have m2 : ∀ A, A < 2 ^ 64 → ¬ (DIGITS ≤ A ∧ A < DIGITS + 64) → u2.getMem (BitVec.ofNat 64 A) =
      u1.getMem (BitVec.ofNat 64 A) := fun A hA hn => by
    rw [← hu2, getMem_setPC', a1, getMem_setByte _ _ _ (by omega) hA _ (by omega)]
  -- step 2: divu t3, t3, R
  have st2 := step_alu (hd c2) p2 hd2 rfl
  generalize hu3 : (u2.setReg .x28 (BinOp.divu.eval ((Src.reg .x28).eval u2) ((Src.reg R).eval u2))).setPC
    (u2.pc + 4) = u3 at st2
  have g3_28 : u3.getReg .x28 = BitVec.ofNat 64 (n / r) := by
    rw [← hu3, getReg_setPC', geq _ _ _ (by decide)]
    show rv64_divu (u2.getReg .x28) (u2.getReg R) = _
    rw [g2, g2, g1 .x28 (by decide), g1 R hR.2.2, h28, hRv, bv_divu _ _ hn hr.1 hR']
  have g3 : ∀ q, q ≠ .x28 → u3.getReg q = u2.getReg q := fun q hq => by rw [← hu3, getReg_setPC', gne _ _ _ _ hq]
  have p3 : u3.pc = pc + 4 + 4 + 4 := by rw [← hu3]; show u2.pc + 4 = _; rw [p2]
  have b3 : ∀ a, u3.getByte a = u2.getByte a := fun a => by rw [← hu3, getByte_setPC, getByte_setReg]
  have m3 : ∀ a, u3.getMem a = u2.getMem a := fun a => by rw [← hu3, getMem_setPC']; cases (Reg.x28 : Reg) <;> rfl
  -- step 3: remu t4, t3, R
  have st3 := step_alu (hd c3) p3 hd3 rfl
  generalize hu4 : (u3.setReg .x29 (BinOp.remu.eval ((Src.reg .x28).eval u3) ((Src.reg R).eval u3))).setPC
    (u3.pc + 4) = u4 at st3
  have hRu3 : u3.getReg R = BitVec.ofNat 64 r := by rw [g3 R hR.2.1, g2, g1 R hR.2.2, hRv]
  have g4_29 : u4.getReg .x29 = BitVec.ofNat 64 (n / r % r) := by
    rw [← hu4, getReg_setPC', geq _ _ _ (by decide)]
    show rv64_remu (u3.getReg .x28) (u3.getReg R) = _
    rw [g3_28, hRu3, bv_remu _ _ hn1 hr.1 hR']
  have g4 : ∀ q, q ≠ .x29 → u4.getReg q = u3.getReg q := fun q hq => by rw [← hu4, getReg_setPC', gne _ _ _ _ hq]
  have p4 : u4.pc = pc + 4 + 4 + 4 + 4 := by rw [← hu4]; show u3.pc + 4 = _; rw [p3]
  have b4 : ∀ a, u4.getByte a = u3.getByte a := fun a => by rw [← hu4, getByte_setPC, getByte_setReg]
  have m4 : ∀ a, u4.getMem a = u3.getMem a := fun a => by rw [← hu4, getMem_setPC']; cases (Reg.x29 : Reg) <;> rfl
  -- step 4: sb t4, o+1(a0)
  have h10u4 : u4.getReg .x10 = BitVec.ofNat 64 DIGITS := by
    rw [g4 .x10 (by decide), g3 .x10 (by decide), g2, g1 .x10 (by decide), h10]
  have v4 : accessValid (u4.getReg .x10 + signExtend12 f2) 1 = true := by
    rw [h10u4, ho2]; exact hA 1 (by norm_num)
  have st4 := steps_sb (hd c4) p4 hd4 v4
  generalize hu5 : (u4.setByte (u4.getReg .x10 + signExtend12 f2) ((u4.getReg .x29).truncate 8)).setPC
    (u4.pc + 4) = u5 at st4
  have a4 : u4.getReg .x10 + signExtend12 f2 = BitVec.ofNat 64 (DIGITS + (o + 1)) := by
    rw [h10u4, ho2, ofNat_add_ofNat]
  have g5 : ∀ q, u5.getReg q = u4.getReg q := fun q => by rw [← hu5, getReg_setPC', getReg_setByte]
  have p5 : u5.pc = pc + 4 + 4 + 4 + 4 + 4 := by rw [← hu5]; show u4.pc + 4 = _; rw [p4]
  have b5 : ∀ B, B < 2 ^ 64 → u5.getByte (BitVec.ofNat 64 B) =
      if B = DIGITS + (o + 1) then BitVec.ofNat 8 (n / r % r) else u4.getByte (BitVec.ofNat 64 B) := fun B hB => by
    rw [← hu5, getByte_setPC, a4, g4_29, trunc8, getByte_setByte _ _ _ (by omega) hB]
  have m5 : ∀ A, A < 2 ^ 64 → ¬ (DIGITS ≤ A ∧ A < DIGITS + 64) → u5.getMem (BitVec.ofNat 64 A) =
      u4.getMem (BitVec.ofNat 64 A) := fun A hA hn => by
    rw [← hu5, getMem_setPC', a4, getMem_setByte _ _ _ (by omega) hA _ (by omega)]
  -- step 5: divu t4, t3, R
  have st5 := step_alu (hd c5) p5 hd5 rfl
  generalize hu6 : (u5.setReg .x29 (BinOp.divu.eval ((Src.reg .x28).eval u5) ((Src.reg R).eval u5))).setPC
    (u5.pc + 4) = u6 at st5
  have g6_29 : u6.getReg .x29 = BitVec.ofNat 64 (n / r / r) := by
    rw [← hu6, getReg_setPC', geq _ _ _ (by decide)]
    show rv64_divu (u5.getReg .x28) (u5.getReg R) = _
    rw [g5, g5, g4 .x28 (by decide), g4 R hR.2.2, g3_28, hRu3, bv_divu _ _ hn1 hr.1 hR']
  have g6 : ∀ q, q ≠ .x29 → u6.getReg q = u5.getReg q := fun q hq => by rw [← hu6, getReg_setPC', gne _ _ _ _ hq]
  have p6 : u6.pc = pc + 4 + 4 + 4 + 4 + 4 + 4 := by rw [← hu6]; show u5.pc + 4 = _; rw [p5]
  have b6 : ∀ a, u6.getByte a = u5.getByte a := fun a => by rw [← hu6, getByte_setPC, getByte_setReg]
  have m6 : ∀ a, u6.getMem a = u5.getMem a := fun a => by rw [← hu6, getMem_setPC']; cases (Reg.x29 : Reg) <;> rfl
  -- step 6: sb t4, o+2(a0)
  have h10u6 : u6.getReg .x10 = BitVec.ofNat 64 DIGITS := by rw [g6 .x10 (by decide), g5, h10u4]
  have v6 : accessValid (u6.getReg .x10 + signExtend12 f3) 1 = true := by
    rw [h10u6, ho3]; exact hA 2 (by norm_num)
  have st6 := steps_sb (hd c6) p6 hd6 v6
  generalize hu7 : (u6.setByte (u6.getReg .x10 + signExtend12 f3) ((u6.getReg .x29).truncate 8)).setPC
    (u6.pc + 4) = u7 at st6
  have a6 : u6.getReg .x10 + signExtend12 f3 = BitVec.ofNat 64 (DIGITS + (o + 2)) := by
    rw [h10u6, ho3, ofNat_add_ofNat]
  have g7 : ∀ q, u7.getReg q = u6.getReg q := fun q => by rw [← hu7, getReg_setPC', getReg_setByte]
  have b7 : ∀ B, B < 2 ^ 64 → u7.getByte (BitVec.ofNat 64 B) =
      if B = DIGITS + (o + 2) then BitVec.ofNat 8 (n / r / r) else u6.getByte (BitVec.ofNat 64 B) := fun B hB => by
    rw [← hu7, getByte_setPC, a6, g6_29, trunc8, getByte_setByte _ _ _ (by omega) hB]
  have m7 : ∀ A, A < 2 ^ 64 → ¬ (DIGITS ≤ A ∧ A < DIGITS + 64) → u7.getMem (BitVec.ofNat 64 A) =
      u6.getMem (BitVec.ofNat 64 A) := fun A hA hn => by
    rw [← hu7, getMem_setPC', a6, getMem_setByte _ _ _ (by omega) hA _ (by omega)]
  have hall : ∀ B, B < 2 ^ 64 → u7.getByte (BitVec.ofNat 64 B) =
      if B = DIGITS + (o + 2) then BitVec.ofNat 8 (n / r / r) else
      if B = DIGITS + (o + 1) then BitVec.ofNat 8 (n / r % r) else
      if B = DIGITS + o then BitVec.ofNat 8 (n % r) else s.getByte (BitVec.ofNat 64 B) := by
    intro B hB
    rw [b7 B hB, b6, b5 B hB, b4, b3, b2 B hB, b1]
  refine ⟨u7, (((((((st0.trans st1).trans st2).trans st3).trans st4).trans st5).trans st6)).of_eq rfl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu7]; show u6.pc + 4 = _; rw [p6]
  · rw [hall _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [hall _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hall _ (by omega), if_pos rfl]
  · intro B hB hn
    rw [hall B hB, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [g7, g6 q hq.2, g5, g4 q hq.2, g3 q hq.1, g2, g1 q hq.2]
  · intro A hA hn
    rw [m7 A hA hn, m6, m5 A hA hn, m4, m3, m2 A hA hn, m1]
def kUp1 : List (BitVec 32) := [0x20537,0x42050513]
def kUsb : List (BitVec 32) := [0x3c509a3]
def kUp2 : List (BitVec 32) := [0x600f13,0x500593,0x3f35c93,0x139e93,0x1dcecb3]
def kUg0 : List (BitVec 32) := [0xff37e13,0xfd8e0e13]
def kUs0 : List (BitVec 32) := [0x3ee7eb3,0x1d50023,0x3ee5e33,0x3ee7eb3,0x1d500a3,0x3ee5eb3,0x1d50123]
def kUg1 : List (BitVec 32) := [0x835e13,0xffe7e13]
def kUs1 : List (BitVec 32) := [0x3ee7eb3,0x1d501a3,0x3ee5e33,0x3ee7eb3,0x1d50223,0x3ee5eb3,0x1d502a3]
def kUg2 : List (BitVec 32) := [0x1035e13,0xffe7e13]
def kUs2 : List (BitVec 32) := [0x3ee7eb3,0x1d50323,0x3ee5e33,0x3ee7eb3,0x1d503a3,0x3ee5eb3,0x1d50423]
def kUg3 : List (BitVec 32) := [0x1835e13,0xffe7e13]
def kUs3 : List (BitVec 32) := [0x3ee7eb3,0x1d504a3,0x3ee5e33,0x3ee7eb3,0x1d50523,0x3ee5eb3,0x1d505a3]
def kUg4 : List (BitVec 32) := [0x2035e13,0xffe7e13]
def kUs4 : List (BitVec 32) := [0x3ee7eb3,0x1d50623,0x3ee5e33,0x3ee7eb3,0x1d506a3,0x3ee5eb3,0x1d50723]
def kUg5 : List (BitVec 32) := [0x2835e13,0xffe7e13]
def kUs5 : List (BitVec 32) := [0x3ee7eb3,0x1d507a3,0x3ee5e33,0x3ee7eb3,0x1d50823,0x3ee5eb3,0x1d508a3]
def kUg6 : List (BitVec 32) := [0x3035e13,0xffe7e13]
def kUs6 : List (BitVec 32) := [0x3ee7eb3,0x1d50923,0x3ee5e33,0x3ee7eb3,0x1d509a3,0x3ee5eb3,0x1d50a23]
def kUg7 : List (BitVec 32) := [0x38cde13]
def kUs7 : List (BitVec 32) := [0x3ee7eb3,0x1d50aa3,0x3ee5e33,0x3ee7eb3,0x1d50b23,0x3ee5eb3,0x1d50ba3]
def kUg8 : List (BitVec 32) := [0x3835e13,0x7fe7e13,0x7fe4e13]
def kUs8 : List (BitVec 32) := [0x2be7eb3,0x1d50c23,0x2be5e33,0x2be7eb3,0x1d50ca3,0x2be5eb3,0x1d50d23]
def kUg9 : List (BitVec 32) := [0x7fcfe13,0x7fe4e13]
def kUs9 : List (BitVec 32) := [0x2be7eb3,0x1d50da3,0x2be5e33,0x2be7eb3,0x1d50e23,0x2be5eb3,0x1d50ea3]
def kUg10 : List (BitVec 32) := [0x7cde13,0x7fe7e13,0x7fe4e13]
def kUs10 : List (BitVec 32) := [0x2be7eb3,0x1d50f23,0x2be5e33,0x2be7eb3,0x1d50fa3,0x2be5eb3,0x3d50023]
def kUg11 : List (BitVec 32) := [0xecde13,0x7fe7e13,0x7fe4e13]
def kUs11 : List (BitVec 32) := [0x2be7eb3,0x3d500a3,0x2be5e33,0x2be7eb3,0x3d50123,0x2be5eb3,0x3d501a3]
def kUg12 : List (BitVec 32) := [0x15cde13,0x7fe7e13,0x7fe4e13]
def kUs12 : List (BitVec 32) := [0x2be7eb3,0x3d50223,0x2be5e33,0x2be7eb3,0x3d502a3,0x2be5eb3,0x3d50323]
def kUg13 : List (BitVec 32) := [0x1ccde13,0x7fe7e13,0x7fe4e13]
def kUs13 : List (BitVec 32) := [0x2be7eb3,0x3d503a3,0x2be5e33,0x2be7eb3,0x3d50423,0x2be5eb3,0x3d504a3]
def kUg14 : List (BitVec 32) := [0x23cde13,0x7fe7e13,0x7fe4e13]
def kUs14 : List (BitVec 32) := [0x2be7eb3,0x3d50523,0x2be5e33,0x2be7eb3,0x3d505a3,0x2be5eb3,0x3d50623]
def kUg15 : List (BitVec 32) := [0x2acde13,0x7fe7e13,0x7fe4e13]
def kUs15 : List (BitVec 32) := [0x2be7eb3,0x3d506a3,0x2be5e33,0x2be7eb3,0x3d50723,0x2be5eb3,0x3d507a3]
def kUg16 : List (BitVec 32) := [0x31cde13,0x7fe7e13,0x7fe4e13]
def kUs16 : List (BitVec 32) := [0x2be7eb3,0x3d50823,0x2be5e33,0x2be7eb3,0x3d508a3,0x2be5eb3,0x3d50923]
def kUret : List (BitVec 32) := [0x8067]
def uLF : Rv.Layout := [(0, kUp1), (2, kUsb), (3, kUp2), (8, kUg0), (10, kUs0), (17, kUg1), (19, kUs1), (26, kUg2), (28, kUs2), (35, kUg3), (37, kUs3), (44, kUg4), (46, kUs4), (53, kUg5), (55, kUs5), (62, kUg6), (64, kUs6), (71, kUg7), (72, kUs7), (79, kUg8), (82, kUs8), (89, kUg9), (91, kUs9), (98, kUg10), (101, kUs10), (108, kUg11), (111, kUs11), (118, kUg12), (121, kUs12), (128, kUg13), (131, kUs13), (138, kUg14), (141, kUs14), (148, kUg15), (151, kUs15), (158, kUg16), (161, kUs16), (168, kUret)]
theorem uLF_ok : layoutOk 0 uLF = true := by decide +kernel
theorem uLF_code : uCode = layoutCode uLF := by decide +kernel
theorem codeAt_uf {image : Image} {b : Nat} (h : R6KAt image b) (i : Nat) {o : Nat} {seg : List (BitVec 32)}
    (hi : uLF[i]? = some (o, seg)) : CodeAt image (pcOf (uBase b + o)) seg := by
  have hc := h.2.2
  rw [uLF_code] at hc
  exact codeAt_sublayout hc uLF_ok hi
sym_block up1Run := symRun { noAlias := true } kUp1 0 10
theorem run_up1 (pc : Word) : symRun { noAlias := true } kUp1 pc 10 =
    some ⟨up1Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block up2Run := symRun { noAlias := true } kUp2 0 10
theorem run_up2 (pc : Word) : symRun { noAlias := true } kUp2 pc 10 =
    some ⟨up2Run.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by
  rfl
sym_block ug0Run := symRun { noAlias := true } kUg0 0 10
theorem run_ug0 (pc : Word) : symRun { noAlias := true } kUg0 pc 10 =
    some ⟨ug0Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug1Run := symRun { noAlias := true } kUg1 0 10
theorem run_ug1 (pc : Word) : symRun { noAlias := true } kUg1 pc 10 =
    some ⟨ug1Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug2Run := symRun { noAlias := true } kUg2 0 10
theorem run_ug2 (pc : Word) : symRun { noAlias := true } kUg2 pc 10 =
    some ⟨ug2Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug3Run := symRun { noAlias := true } kUg3 0 10
theorem run_ug3 (pc : Word) : symRun { noAlias := true } kUg3 pc 10 =
    some ⟨ug3Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug4Run := symRun { noAlias := true } kUg4 0 10
theorem run_ug4 (pc : Word) : symRun { noAlias := true } kUg4 pc 10 =
    some ⟨ug4Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug5Run := symRun { noAlias := true } kUg5 0 10
theorem run_ug5 (pc : Word) : symRun { noAlias := true } kUg5 pc 10 =
    some ⟨ug5Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug6Run := symRun { noAlias := true } kUg6 0 10
theorem run_ug6 (pc : Word) : symRun { noAlias := true } kUg6 pc 10 =
    some ⟨ug6Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug7Run := symRun { noAlias := true } kUg7 0 10
theorem run_ug7 (pc : Word) : symRun { noAlias := true } kUg7 pc 10 =
    some ⟨ug7Run.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
sym_block ug8Run := symRun { noAlias := true } kUg8 0 10
theorem run_ug8 (pc : Word) : symRun { noAlias := true } kUg8 pc 10 =
    some ⟨ug8Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug9Run := symRun { noAlias := true } kUg9 0 10
theorem run_ug9 (pc : Word) : symRun { noAlias := true } kUg9 pc 10 =
    some ⟨ug9Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
sym_block ug10Run := symRun { noAlias := true } kUg10 0 10
theorem run_ug10 (pc : Word) : symRun { noAlias := true } kUg10 pc 10 =
    some ⟨ug10Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug11Run := symRun { noAlias := true } kUg11 0 10
theorem run_ug11 (pc : Word) : symRun { noAlias := true } kUg11 pc 10 =
    some ⟨ug11Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug12Run := symRun { noAlias := true } kUg12 0 10
theorem run_ug12 (pc : Word) : symRun { noAlias := true } kUg12 pc 10 =
    some ⟨ug12Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug13Run := symRun { noAlias := true } kUg13 0 10
theorem run_ug13 (pc : Word) : symRun { noAlias := true } kUg13 pc 10 =
    some ⟨ug13Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug14Run := symRun { noAlias := true } kUg14 0 10
theorem run_ug14 (pc : Word) : symRun { noAlias := true } kUg14 pc 10 =
    some ⟨ug14Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug15Run := symRun { noAlias := true } kUg15 0 10
theorem run_ug15 (pc : Word) : symRun { noAlias := true } kUg15 pc 10 =
    some ⟨ug15Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
sym_block ug16Run := symRun { noAlias := true } kUg16 0 10
theorem run_ug16 (pc : Word) : symRun { noAlias := true } kUg16 pc 10 =
    some ⟨ug16Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem run_uret (pc : Word) : symRun { noAlias := true } kUret pc 10 =
    some ⟨SymState.init, .bin .and (.reg .x1) (.c 18446744073709551614#64), .jump, 1, 1⟩ := by
  rfl

theorem up1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUp1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x10 = BitVec.ofNat 64 DIGITS ∧ RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_up1 pc) hc s hpc (by simp [up1Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, up1Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [up1Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [up1Run.res, rv_simp]
theorem up2_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUp2) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧ (t.getReg .x30 = 6#64 ∧ t.getReg .x11 = 5#64 ∧ t.getReg .x25 = (s.getReg .x6 >>> 63) ||| (s.getReg .x7 <<< 1)) ∧ RegsExcept s t [.x11, .x25, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_up2 pc) hc s hpc (by simp [up2Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, up2Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [up2Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [up2Run.res, rv_simp]
theorem ug0_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg0) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 &&& 255#64) - 40#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug0 pc) hc s hpc (by simp [ug0Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug0Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug0Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug0Run.res, rv_simp]
theorem ug1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 8) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug1 pc) hc s hpc (by simp [ug1Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug1Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug1Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug1Run.res, rv_simp]
theorem ug2_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg2) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 16) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug2 pc) hc s hpc (by simp [ug2Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug2Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug2Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug2Run.res, rv_simp]
theorem ug3_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg3) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 24) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug3 pc) hc s hpc (by simp [ug3Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug3Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug3Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug3Run.res, rv_simp]
theorem ug4_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg4) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 32) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug4 pc) hc s hpc (by simp [ug4Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug4Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug4Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug4Run.res, rv_simp]
theorem ug5_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg5) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 40) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug5 pc) hc s hpc (by simp [ug5Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug5Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug5Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug5Run.res, rv_simp]
theorem ug6_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg6) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 48) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug6 pc) hc s hpc (by simp [ug6Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug6Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug6Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug6Run.res, rv_simp]
theorem ug7_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg7) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x28 = s.getReg .x25 >>> 56 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug7 pc) hc s hpc (by simp [ug7Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug7Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug7Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug7Run.res, rv_simp]
theorem ug8_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg8) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x6 >>> 56) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug8 pc) hc s hpc (by simp [ug8Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug8Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug8Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug8Run.res, rv_simp]
theorem ug9_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg9) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x25 &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug9 pc) hc s hpc (by simp [ug9Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug9Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug9Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug9Run.res, rv_simp]
theorem ug10_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg10) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 7) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug10 pc) hc s hpc (by simp [ug10Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug10Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug10Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug10Run.res, rv_simp]
theorem ug11_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg11) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 14) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug11 pc) hc s hpc (by simp [ug11Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug11Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug11Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug11Run.res, rv_simp]
theorem ug12_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg12) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 21) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug12 pc) hc s hpc (by simp [ug12Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug12Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug12Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug12Run.res, rv_simp]
theorem ug13_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg13) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 28) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug13 pc) hc s hpc (by simp [ug13Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug13Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug13Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug13Run.res, rv_simp]
theorem ug14_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg14) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 35) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug14 pc) hc s hpc (by simp [ug14Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug14Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug14Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug14Run.res, rv_simp]
theorem ug15_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg15) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 42) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug15 pc) hc s hpc (by simp [ug15Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug15Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug15Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug15Run.res, rv_simp]
theorem ug16_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg16) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 49) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ug16 pc) hc s hpc (by simp [ug16Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, ug16Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [ug16Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [ug16Run.res, rv_simp]

/-! ### Unpacker values and digits -/
theorem fld_lo (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 0 64 >>> S) &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (v.toNat / 2 ^ S % 2 ^ w) := by
  rw [bv_and_mask _ w (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, lo_field v S w h]
theorem fld_t5 (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) >>> S) &&& BitVec.ofNat 64 (2 ^ w - 1) =
      BitVec.ofNat 64 (v.toNat / 2 ^ (63 + S) % 2 ^ w) := by
  rw [bv_and_mask _ w (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_ofNat_lt (t5_lt v),
    t5_field v S w h]
theorem xor127 (x : Nat) (hx : x < 128) : BitVec.ofNat 64 x ^^^ 127#64 = BitVec.ofNat 64 (127 - x) := by
  apply BitVec.eq_of_toNat_eq
  have h : ∀ x < 128, x ^^^ 127 = 127 - x := by decide
  rw [BitVec.toNat_xor, toNat_ofNat_lt (show x < 2 ^ 64 by omega), toNat_ofNat_lt (show 127 < 2 ^ 64 by norm_num),
    toNat_ofNat_lt (show 127 - x < 2 ^ 64 by omega), h x hx]
theorem t5_hi (v : Digest) : v.toNat / 2 ^ 63 % 2 ^ 64 / 2 ^ 56 = v.toNat / 2 ^ 119 % 256 := by
  have := v.isLt; omega
theorem r6Rank_0 (v : Digest) : T3.r6Rank v 0 = v.toNat % 256 - 40 := by
  unfold T3.r6Rank; simp [r6Raw_eq v 0 (by norm_num), T3.r6Shift]
theorem r6Rank_g (v : Digest) (g : Nat) (h1 : 1 ≤ g) (h6 : g ≤ 6) : T3.r6Rank v g = v.toNat / 2 ^ (8 * g) % 256 := by
  unfold T3.r6Rank
  rw [if_neg (by omega), r6Raw_eq v g (by omega)]
  simp [T3.r6Shift, show g ≠ 7 by omega]
theorem r6Rank_7 (v : Digest) : T3.r6Rank v 7 = v.toNat / 2 ^ 119 % 256 := by
  unfold T3.r6Rank; rw [if_neg (by norm_num), r6Raw_eq v 7 (by norm_num)]; rfl
theorem udig6 {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (g : Nat) (hg : g < 8) :
    ds.getD (3 * g) 0 = T3.r6Rank v g % 6 ∧ ds.getD (3 * g + 1) 0 = T3.r6Rank v g / 6 % 6 ∧
      ds.getD (3 * g + 2) 0 = T3.r6Rank v g / 6 / 6 := by
  have hv := (decode_top_eq hd).1
  obtain ⟨_, h6, _⟩ := valid_groups hv
  have hr := ((gIdx_r6 v g hg).2 (h6 g hg)).2
  have c0 := coreDigit_r6g v g 0 hg (by norm_num)
  have c1 := coreDigit_r6g v g 1 hg (by norm_num)
  have c2 := coreDigit_r6g v g 2 hg (by norm_num)
  simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [ds_getD_data hd _ (by omega), c0]
  · rw [ds_getD_data hd _ (by omega), c1]
  · rw [ds_getD_data hd _ (by omega), c2]; norm_num; omega
theorem udig5 {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (q : Nat)
    (hq : 8 ≤ q ∧ q < 17) :
    ds.getD (3 * q) 0 = T3.r5Rank v q % 5 ∧ ds.getD (3 * q + 1) 0 = T3.r5Rank v q / 5 % 5 ∧
      ds.getD (3 * q + 2) 0 = T3.r5Rank v q / 5 / 5 := by
  have hv := (decode_top_eq hd).1
  obtain ⟨_, _, h5⟩ := valid_groups hv
  have hr := h5 q hq.1 hq.2
  have c0 := coreDigit_r5g v q 0 hq (by norm_num)
  have c1 := coreDigit_r5g v q 1 hq (by norm_num)
  have c2 := coreDigit_r5g v q 2 hq (by norm_num)
  simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [ds_getD_data hd _ (by omega), c0]
  · rw [ds_getD_data hd _ (by omega), c1]
  · rw [ds_getD_data hd _ (by omega), c2]; norm_num; omega
theorem g0_valid {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    40 ≤ v.toNat % 256 := by
  have hv := (decode_top_eq hd).1
  obtain ⟨_, h6, _⟩ := valid_groups hv
  have := h6 0 (by norm_num)
  unfold T3.r6Valid at this
  rw [r6Raw_eq v 0 (by norm_num)] at this
  simpa [T3.r6Shift] using this
/-! ### Digit-buffer invariant -/
def DInv (t : MachineState) (ds : List Nat) (m : Nat) : Prop :=
  ∀ j, (j < m ∨ j = 51) → t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)
theorem DInv.frame {t t' : MachineState} {ds : List Nat} {m : Nat} (h : DInv t ds m) (hm : m ≤ 51)
    (hf : Frame t t' (fun _ => False)) : DInv t' ds m := by
  intro j hj
  have hD : DIGITS = 0x20420 := rfl
  have hj51 : j ≤ 51 := by rcases hj with hj | hj <;> omega
  rw [hf.getByte (by omega) (fun h => h)]
  exact h j hj
theorem DInv.step {t t' : MachineState} {ds : List Nat} {m : Nat} (h : DInv t ds m) (hm : m + 3 ≤ 51)
    (h0 : t'.getByte (BitVec.ofNat 64 (DIGITS + m)) = BitVec.ofNat 8 (ds.getD m 0))
    (h1 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 1))) = BitVec.ofNat 8 (ds.getD (m + 1) 0))
    (h2 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 2))) = BitVec.ofNat 8 (ds.getD (m + 2) 0))
    (hfr : ∀ B, B < 2 ^ 64 → ¬ (DIGITS + m ≤ B ∧ B < DIGITS + m + 3) →
      t'.getByte (BitVec.ofNat 64 B) = t.getByte (BitVec.ofNat 64 B)) : DInv t' ds (m + 3) := by
  intro j hj
  have hD : DIGITS = 0x20420 := rfl
  by_cases hjm : j < m ∨ j = 51
  · have hj51 : j ≤ 51 := by rcases hjm with hj | hj <;> omega
    have hn : ¬ (DIGITS + m ≤ DIGITS + j ∧ DIGITS + j < DIGITS + m + 3) := by
      rcases hjm with hj | hj <;> omega
    rw [hfr _ (by omega) hn]; exact h j hjm
  · have : j = m ∨ j = m + 1 ∨ j = m + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
theorem ret_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUret) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = s.getReg .x1 &&& 18446744073709551614#64 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_uret pc) hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp]
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
theorem r6Rank_lt (v : Digest) (g : Nat) : T3.r6Rank v g < 256 := by
  unfold T3.r6Rank T3.r6Raw; split_ifs <;> omega
theorem r5Rank_lt (v : Digest) (q : Nat) : T3.r5Rank v q < 128 := by
  unfold T3.r5Rank; omega
theorem udig6' {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (g m : Nat)
    (hm : m = 3 * g) (hg : g < 8) :
    ds.getD m 0 = T3.r6Rank v g % 6 ∧ ds.getD (m + 1) 0 = T3.r6Rank v g / 6 % 6 ∧
      ds.getD (m + 2) 0 = T3.r6Rank v g / 6 / 6 := by subst hm; exact udig6 hd g hg
theorem udig5' {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (q m : Nat)
    (hm : m = 3 * q) (hq : 8 ≤ q ∧ q < 17) :
    ds.getD m 0 = T3.r5Rank v q % 5 ∧ ds.getD (m + 1) 0 = T3.r5Rank v q / 5 % 5 ∧
      ds.getD (m + 2) 0 = T3.r5Rank v q / 5 / 5 := by subst hm; exact udig5 hd q hq
theorem DInv.step' {t t' : MachineState} {ds : List Nat} {m r n : Nat} (h : DInv t ds m) (hm : m + 3 ≤ 51)
    (hb0 : t'.getByte (BitVec.ofNat 64 (DIGITS + m)) = BitVec.ofNat 8 (n % r))
    (hb1 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 1))) = BitVec.ofNat 8 (n / r % r))
    (hb2 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 2))) = BitVec.ofNat 8 (n / r / r))
    (hfr : ∀ B, B < 2 ^ 64 → ¬ (DIGITS + m ≤ B ∧ B < DIGITS + m + 3) →
      t'.getByte (BitVec.ofNat 64 B) = t.getByte (BitVec.ofNat 64 B))
    (hdig : ds.getD m 0 = n % r ∧ ds.getD (m + 1) 0 = n / r % r ∧ ds.getD (m + 2) 0 = n / r / r) :
    DInv t' ds (m + 3) :=
  h.step hm (by rw [hb0, hdig.1]) (by rw [hb1, hdig.2.1]) (by rw [hb2, hdig.2.2]) hfr
/-- The R6 unpacker: from `U_ENTRY` with a decoded word `v` in `x6`, `x7` and its checksum digit in `x28`, write the
52 digits to `DIGITS` and return through `ra`. -/
theorem unpack {image : Image} {b : Nat} (hR : R6KAt image b) (u : MachineState) (hpc : u.pc = pcOf (uBase b))
    (v : Digest) (ds : List Nat) (hd : WCT9.CanonicalPolicy.decode 0 v = some ds)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h28 : u.getReg .x28 = BitVec.ofNat 64 (ds.getD 51 0)) :
    ∃ t, Steps image u 169 373 t ∧ t.pc = u.getReg .x1 &&& ~~~1#64 ∧
      (∀ j < 52, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept u t uRegs ∧ Frame u t (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
  have hub : uBase b < 2 ^ 20 := by rcases hR.1 with rfl | rfl <;> simp [uBase]
  have hD : DIGITS = 0x20420 := rfl
  have hvl := v.isLt
  have hFm : ∀ {x y z : MachineState}, Frame x y (fun _ => False) → Frame y z (fun _ => False) →
      Frame x z (fun _ => False) := fun h1 h2 => (h1.trans h2).mono (fun _ _ h => by simpa using h)
  obtain ⟨c1, s1, p1, x10_1, r1, f1⟩ := up1_spec (codeAt_uf hR 0 rfl) u hpc
  have p1' : c1.pc = pcOf (uBase b + 2) := by rw [p1, pcOf_4, pcOf_4]
  have v51 : accessValid (c1.getReg .x10 + signExtend12 (51#12)) 1 = true := by
    rw [x10_1, show signExtend12 (51#12) = BitVec.ofNat 64 51 from rfl, ofNat_add_ofNat]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show DIGITS + 51 < 2 ^ 64 by omega)]
    omega
  have sb51 := steps_sb (rs1 := .x10) (rs2 := .x28) (off := 51#12) (codeAt_uf hR 1 rfl) p1' rfl v51
  generalize hc2 : (c1.setByte (c1.getReg .x10 + signExtend12 (51#12)) ((c1.getReg .x28).truncate 8)).setPC
    (c1.pc + 4) = c2 at sb51
  have a51 : c1.getReg .x10 + signExtend12 (51#12) = BitVec.ofNat 64 (DIGITS + 51) := by
    rw [x10_1, show signExtend12 (51#12) = BitVec.ofNat 64 51 from rfl, ofNat_add_ofNat]
  have p2 : c2.pc = pcOf (uBase b + 3) := by rw [← hc2]; show c1.pc + 4 = _; rw [p1', pcOf_4]
  have r2 : RegsExcept c1 c2 [] := fun q _ => by rw [← hc2, getReg_setPC', getReg_setByte]
  have b2 : c2.getByte (BitVec.ofNat 64 (DIGITS + 51)) = BitVec.ofNat 8 (ds.getD 51 0) := by
    rw [← hc2, getByte_setPC, a51, getByte_setByte _ _ _ (by omega) (by omega), if_pos rfl,
      r1 .x28 (by decide), h28, trunc8]
  have f2 : Frame c1 c2 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
    intro A hA hn
    rw [← hc2, getMem_setPC', a51, getMem_setByte _ _ _ (by omega) hA _ (by omega)]
  obtain ⟨c3, s3, p3, ⟨x30_3, x11_3, x25_3⟩, r3, f3⟩ := up2_spec (codeAt_uf hR 2 rfl) c2 p2
  have c3x6 : c3.getReg .x6 = v.extractLsb' 0 64 := by
    rw [r3 .x6 (by decide), r2 .x6 (by decide), r1 .x6 (by decide), h6]
  have c3x10 : c3.getReg .x10 = BitVec.ofNat 64 DIGITS := by rw [r3 .x10 (by decide), r2 .x10 (by decide), x10_1]
  have c3x25 : c3.getReg .x25 = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) := by
    rw [x25_3, r2 .x6 (by decide), r2 .x7 (by decide), r1 .x6 (by decide), r1 .x7 (by decide), h6, h7, t5_val]
  have c3x30 : c3.getReg .x30 = BitVec.ofNat 64 6 := x30_3
  have c3x11 : c3.getReg .x11 = BitVec.ofNat 64 5 := x11_3
  have Dc : DInv c3 ds 0 := by
    intro j hj
    have hj' : j = 51 := by omega
    subst hj'
    rw [f3.getByte (by omega) (fun h => h), b2]
  have Rc : RegsExcept c3 c3 [.x28, .x29] := RegsExcept.refl _ _
  have Fc : Frame c3 c3 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := Frame.refl _ _
  have p3' : c3.pc = pcOf (uBase b + 8) := by rw [p3]; simp only [pcOf_4]
  -- group 0
  obtain ⟨a0, sa0, pa0, va0, ra0, fa0⟩ := ug0_spec (codeAt_uf hR 3 rfl) c3 p3'
  have Ra0 : RegsExcept c3 a0 [.x28, .x29] := (Rc.trans ra0).mono (by decide)
  have n0 : a0.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 0) := by
    rw [va0, Rc .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      bv_and_mask _ 8 (by norm_num), lo_mod v 8 (by norm_num), show (40#64 : Word) = BitVec.ofNat 64 40 from rfl,
      bv_sub _ _ (by have := g0_valid hd; omega) (by omega), r6Rank_0]
    try norm_num
  have pa0' : a0.pc = pcOf (uBase b + 10) := by rw [pa0]; simp only [pcOf_4]
  obtain ⟨t0, st0, pt0, b0_0, b1_0, b2_0, bf0, rt0, ft0⟩ :=
    split7 (R := .x30) (o := 0) (r := 6) (codeAt_uf hR 4 rfl) pa0' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra0 .x10 (by decide), c3x10]) (by rw [Ra0 .x30 (by decide), c3x30])
      (by norm_num) n0 (by have := r6Rank_lt v 0; omega)
  have D0 : DInv t0 ds (0 + 3) :=
    DInv.step' (Dc.frame (by norm_num) fa0) (by norm_num) b0_0 b1_0 b2_0 bf0 (udig6' hd 0 0 rfl (by norm_num))
  have R0 : RegsExcept c3 t0 [.x28, .x29] := (Ra0.trans rt0).mono (by decide)
  have F0 : Frame c3 t0 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((Fc.trans fa0).trans ft0).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt0' : t0.pc = pcOf (uBase b + 17) := by rw [pt0]; simp only [pcOf_4]
  -- group 1
  obtain ⟨a1, sa1, pa1, va1, ra1, fa1⟩ := ug1_spec (codeAt_uf hR 5 rfl) t0 pt0'
  have Ra1 : RegsExcept c3 a1 [.x28, .x29] := (R0.trans ra1).mono (by decide)
  have n1 : a1.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 1) := by
    rw [va1, R0 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 8 8 (by norm_num), r6Rank_g v 1 (by norm_num) (by norm_num)]
    try norm_num
  have pa1' : a1.pc = pcOf (uBase b + 19) := by rw [pa1]; simp only [pcOf_4]
  obtain ⟨t1, st1, pt1, b0_1, b1_1, b2_1, bf1, rt1, ft1⟩ :=
    split7 (R := .x30) (o := 3) (r := 6) (codeAt_uf hR 6 rfl) pa1' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra1 .x10 (by decide), c3x10]) (by rw [Ra1 .x30 (by decide), c3x30])
      (by norm_num) n1 (by have := r6Rank_lt v 1; omega)
  have D1 : DInv t1 ds (3 + 3) :=
    DInv.step' (D0.frame (by norm_num) fa1) (by norm_num) b0_1 b1_1 b2_1 bf1 (udig6' hd 1 3 rfl (by norm_num))
  have R1 : RegsExcept c3 t1 [.x28, .x29] := (Ra1.trans rt1).mono (by decide)
  have F1 : Frame c3 t1 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F0.trans fa1).trans ft1).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt1' : t1.pc = pcOf (uBase b + 26) := by rw [pt1]; simp only [pcOf_4]
  -- group 2
  obtain ⟨a2, sa2, pa2, va2, ra2, fa2⟩ := ug2_spec (codeAt_uf hR 7 rfl) t1 pt1'
  have Ra2 : RegsExcept c3 a2 [.x28, .x29] := (R1.trans ra2).mono (by decide)
  have n2 : a2.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 2) := by
    rw [va2, R1 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 16 8 (by norm_num), r6Rank_g v 2 (by norm_num) (by norm_num)]
    try norm_num
  have pa2' : a2.pc = pcOf (uBase b + 28) := by rw [pa2]; simp only [pcOf_4]
  obtain ⟨t2, st2, pt2, b0_2, b1_2, b2_2, bf2, rt2, ft2⟩ :=
    split7 (R := .x30) (o := 6) (r := 6) (codeAt_uf hR 8 rfl) pa2' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra2 .x10 (by decide), c3x10]) (by rw [Ra2 .x30 (by decide), c3x30])
      (by norm_num) n2 (by have := r6Rank_lt v 2; omega)
  have D2 : DInv t2 ds (6 + 3) :=
    DInv.step' (D1.frame (by norm_num) fa2) (by norm_num) b0_2 b1_2 b2_2 bf2 (udig6' hd 2 6 rfl (by norm_num))
  have R2 : RegsExcept c3 t2 [.x28, .x29] := (Ra2.trans rt2).mono (by decide)
  have F2 : Frame c3 t2 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F1.trans fa2).trans ft2).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt2' : t2.pc = pcOf (uBase b + 35) := by rw [pt2]; simp only [pcOf_4]
  -- group 3
  obtain ⟨a3, sa3, pa3, va3, ra3, fa3⟩ := ug3_spec (codeAt_uf hR 9 rfl) t2 pt2'
  have Ra3 : RegsExcept c3 a3 [.x28, .x29] := (R2.trans ra3).mono (by decide)
  have n3 : a3.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 3) := by
    rw [va3, R2 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 24 8 (by norm_num), r6Rank_g v 3 (by norm_num) (by norm_num)]
    try norm_num
  have pa3' : a3.pc = pcOf (uBase b + 37) := by rw [pa3]; simp only [pcOf_4]
  obtain ⟨t3, st3, pt3, b0_3, b1_3, b2_3, bf3, rt3, ft3⟩ :=
    split7 (R := .x30) (o := 9) (r := 6) (codeAt_uf hR 10 rfl) pa3' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra3 .x10 (by decide), c3x10]) (by rw [Ra3 .x30 (by decide), c3x30])
      (by norm_num) n3 (by have := r6Rank_lt v 3; omega)
  have D3 : DInv t3 ds (9 + 3) :=
    DInv.step' (D2.frame (by norm_num) fa3) (by norm_num) b0_3 b1_3 b2_3 bf3 (udig6' hd 3 9 rfl (by norm_num))
  have R3 : RegsExcept c3 t3 [.x28, .x29] := (Ra3.trans rt3).mono (by decide)
  have F3 : Frame c3 t3 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F2.trans fa3).trans ft3).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt3' : t3.pc = pcOf (uBase b + 44) := by rw [pt3]; simp only [pcOf_4]
  -- group 4
  obtain ⟨a4, sa4, pa4, va4, ra4, fa4⟩ := ug4_spec (codeAt_uf hR 11 rfl) t3 pt3'
  have Ra4 : RegsExcept c3 a4 [.x28, .x29] := (R3.trans ra4).mono (by decide)
  have n4 : a4.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 4) := by
    rw [va4, R3 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 32 8 (by norm_num), r6Rank_g v 4 (by norm_num) (by norm_num)]
    try norm_num
  have pa4' : a4.pc = pcOf (uBase b + 46) := by rw [pa4]; simp only [pcOf_4]
  obtain ⟨t4, st4, pt4, b0_4, b1_4, b2_4, bf4, rt4, ft4⟩ :=
    split7 (R := .x30) (o := 12) (r := 6) (codeAt_uf hR 12 rfl) pa4' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra4 .x10 (by decide), c3x10]) (by rw [Ra4 .x30 (by decide), c3x30])
      (by norm_num) n4 (by have := r6Rank_lt v 4; omega)
  have D4 : DInv t4 ds (12 + 3) :=
    DInv.step' (D3.frame (by norm_num) fa4) (by norm_num) b0_4 b1_4 b2_4 bf4 (udig6' hd 4 12 rfl (by norm_num))
  have R4 : RegsExcept c3 t4 [.x28, .x29] := (Ra4.trans rt4).mono (by decide)
  have F4 : Frame c3 t4 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F3.trans fa4).trans ft4).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt4' : t4.pc = pcOf (uBase b + 53) := by rw [pt4]; simp only [pcOf_4]
  -- group 5
  obtain ⟨a5, sa5, pa5, va5, ra5, fa5⟩ := ug5_spec (codeAt_uf hR 13 rfl) t4 pt4'
  have Ra5 : RegsExcept c3 a5 [.x28, .x29] := (R4.trans ra5).mono (by decide)
  have n5 : a5.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 5) := by
    rw [va5, R4 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 40 8 (by norm_num), r6Rank_g v 5 (by norm_num) (by norm_num)]
    try norm_num
  have pa5' : a5.pc = pcOf (uBase b + 55) := by rw [pa5]; simp only [pcOf_4]
  obtain ⟨t5, st5, pt5, b0_5, b1_5, b2_5, bf5, rt5, ft5⟩ :=
    split7 (R := .x30) (o := 15) (r := 6) (codeAt_uf hR 14 rfl) pa5' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra5 .x10 (by decide), c3x10]) (by rw [Ra5 .x30 (by decide), c3x30])
      (by norm_num) n5 (by have := r6Rank_lt v 5; omega)
  have D5 : DInv t5 ds (15 + 3) :=
    DInv.step' (D4.frame (by norm_num) fa5) (by norm_num) b0_5 b1_5 b2_5 bf5 (udig6' hd 5 15 rfl (by norm_num))
  have R5 : RegsExcept c3 t5 [.x28, .x29] := (Ra5.trans rt5).mono (by decide)
  have F5 : Frame c3 t5 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F4.trans fa5).trans ft5).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt5' : t5.pc = pcOf (uBase b + 62) := by rw [pt5]; simp only [pcOf_4]
  -- group 6
  obtain ⟨a6, sa6, pa6, va6, ra6, fa6⟩ := ug6_spec (codeAt_uf hR 15 rfl) t5 pt5'
  have Ra6 : RegsExcept c3 a6 [.x28, .x29] := (R5.trans ra6).mono (by decide)
  have n6 : a6.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 6) := by
    rw [va6, R5 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 48 8 (by norm_num), r6Rank_g v 6 (by norm_num) (by norm_num)]
    try norm_num
  have pa6' : a6.pc = pcOf (uBase b + 64) := by rw [pa6]; simp only [pcOf_4]
  obtain ⟨t6, st6, pt6, b0_6, b1_6, b2_6, bf6, rt6, ft6⟩ :=
    split7 (R := .x30) (o := 18) (r := 6) (codeAt_uf hR 16 rfl) pa6' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra6 .x10 (by decide), c3x10]) (by rw [Ra6 .x30 (by decide), c3x30])
      (by norm_num) n6 (by have := r6Rank_lt v 6; omega)
  have D6 : DInv t6 ds (18 + 3) :=
    DInv.step' (D5.frame (by norm_num) fa6) (by norm_num) b0_6 b1_6 b2_6 bf6 (udig6' hd 6 18 rfl (by norm_num))
  have R6 : RegsExcept c3 t6 [.x28, .x29] := (Ra6.trans rt6).mono (by decide)
  have F6 : Frame c3 t6 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F5.trans fa6).trans ft6).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt6' : t6.pc = pcOf (uBase b + 71) := by rw [pt6]; simp only [pcOf_4]
  -- group 7
  obtain ⟨a7, sa7, pa7, va7, ra7, fa7⟩ := ug7_spec (codeAt_uf hR 17 rfl) t6 pt6'
  have Ra7 : RegsExcept c3 a7 [.x28, .x29] := (R6.trans ra7).mono (by decide)
  have n7 : a7.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 7) := by
    rw [va7, R6 .x25 (by decide), c3x25, bv_shr _ _ (t5_lt v), t5_hi, r6Rank_7]
    try norm_num
  have pa7' : a7.pc = pcOf (uBase b + 72) := by rw [pa7]; simp only [pcOf_4]
  obtain ⟨t7, st7, pt7, b0_7, b1_7, b2_7, bf7, rt7, ft7⟩ :=
    split7 (R := .x30) (o := 21) (r := 6) (codeAt_uf hR 18 rfl) pa7' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra7 .x10 (by decide), c3x10]) (by rw [Ra7 .x30 (by decide), c3x30])
      (by norm_num) n7 (by have := r6Rank_lt v 7; omega)
  have D7 : DInv t7 ds (21 + 3) :=
    DInv.step' (D6.frame (by norm_num) fa7) (by norm_num) b0_7 b1_7 b2_7 bf7 (udig6' hd 7 21 rfl (by norm_num))
  have R7 : RegsExcept c3 t7 [.x28, .x29] := (Ra7.trans rt7).mono (by decide)
  have F7 : Frame c3 t7 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F6.trans fa7).trans ft7).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt7' : t7.pc = pcOf (uBase b + 79) := by rw [pt7]; simp only [pcOf_4]
  -- group 8
  obtain ⟨a8, sa8, pa8, va8, ra8, fa8⟩ := ug8_spec (codeAt_uf hR 19 rfl) t7 pt7'
  have Ra8 : RegsExcept c3 a8 [.x28, .x29] := (R7.trans ra8).mono (by decide)
  have n8 : a8.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 8) := by
    rw [va8, R7 .x6 (by decide), c3x6, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_lo v 56 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ 56 % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 8 (by norm_num)]
    try norm_num
  have pa8' : a8.pc = pcOf (uBase b + 82) := by rw [pa8]; simp only [pcOf_4]
  obtain ⟨t8, st8, pt8, b0_8, b1_8, b2_8, bf8, rt8, ft8⟩ :=
    split7 (R := .x11) (o := 24) (r := 5) (codeAt_uf hR 20 rfl) pa8' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra8 .x10 (by decide), c3x10]) (by rw [Ra8 .x11 (by decide), c3x11])
      (by norm_num) n8 (by have := r5Rank_lt v 8; omega)
  have D8 : DInv t8 ds (24 + 3) :=
    DInv.step' (D7.frame (by norm_num) fa8) (by norm_num) b0_8 b1_8 b2_8 bf8 (udig5' hd 8 24 rfl (by norm_num))
  have R8 : RegsExcept c3 t8 [.x28, .x29] := (Ra8.trans rt8).mono (by decide)
  have F8 : Frame c3 t8 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F7.trans fa8).trans ft8).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt8' : t8.pc = pcOf (uBase b + 89) := by rw [pt8]; simp only [pcOf_4]
  -- group 9
  obtain ⟨a9, sa9, pa9, va9, ra9, fa9⟩ := ug9_spec (codeAt_uf hR 21 rfl) t8 pt8'
  have Ra9 : RegsExcept c3 a9 [.x28, .x29] := (R8.trans ra9).mono (by decide)
  have n9 : a9.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 9) := by
    rw [va9, R8 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      bv_and_mask _ 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_mod v 7 (by norm_num),
      show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ 63 % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 9 (by norm_num)]
    try norm_num
  have pa9' : a9.pc = pcOf (uBase b + 91) := by rw [pa9]; simp only [pcOf_4]
  obtain ⟨t9, st9, pt9, b0_9, b1_9, b2_9, bf9, rt9, ft9⟩ :=
    split7 (R := .x11) (o := 27) (r := 5) (codeAt_uf hR 22 rfl) pa9' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra9 .x10 (by decide), c3x10]) (by rw [Ra9 .x11 (by decide), c3x11])
      (by norm_num) n9 (by have := r5Rank_lt v 9; omega)
  have D9 : DInv t9 ds (27 + 3) :=
    DInv.step' (D8.frame (by norm_num) fa9) (by norm_num) b0_9 b1_9 b2_9 bf9 (udig5' hd 9 27 rfl (by norm_num))
  have R9 : RegsExcept c3 t9 [.x28, .x29] := (Ra9.trans rt9).mono (by decide)
  have F9 : Frame c3 t9 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F8.trans fa9).trans ft9).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt9' : t9.pc = pcOf (uBase b + 98) := by rw [pt9]; simp only [pcOf_4]
  -- group 10
  obtain ⟨a10, sa10, pa10, va10, ra10, fa10⟩ := ug10_spec (codeAt_uf hR 23 rfl) t9 pt9'
  have Ra10 : RegsExcept c3 a10 [.x28, .x29] := (R9.trans ra10).mono (by decide)
  have n10 : a10.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 10) := by
    rw [va10, R9 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 7 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 7) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 10 (by norm_num)]
    try norm_num
  have pa10' : a10.pc = pcOf (uBase b + 101) := by rw [pa10]; simp only [pcOf_4]
  obtain ⟨t10, st10, pt10, b0_10, b1_10, b2_10, bf10, rt10, ft10⟩ :=
    split7 (R := .x11) (o := 30) (r := 5) (codeAt_uf hR 24 rfl) pa10' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra10 .x10 (by decide), c3x10]) (by rw [Ra10 .x11 (by decide), c3x11])
      (by norm_num) n10 (by have := r5Rank_lt v 10; omega)
  have D10 : DInv t10 ds (30 + 3) :=
    DInv.step' (D9.frame (by norm_num) fa10) (by norm_num) b0_10 b1_10 b2_10 bf10 (udig5' hd 10 30 rfl (by norm_num))
  have R10 : RegsExcept c3 t10 [.x28, .x29] := (Ra10.trans rt10).mono (by decide)
  have F10 : Frame c3 t10 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F9.trans fa10).trans ft10).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt10' : t10.pc = pcOf (uBase b + 108) := by rw [pt10]; simp only [pcOf_4]
  -- group 11
  obtain ⟨a11, sa11, pa11, va11, ra11, fa11⟩ := ug11_spec (codeAt_uf hR 25 rfl) t10 pt10'
  have Ra11 : RegsExcept c3 a11 [.x28, .x29] := (R10.trans ra11).mono (by decide)
  have n11 : a11.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 11) := by
    rw [va11, R10 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 14 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 14) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 11 (by norm_num)]
    try norm_num
  have pa11' : a11.pc = pcOf (uBase b + 111) := by rw [pa11]; simp only [pcOf_4]
  obtain ⟨t11, st11, pt11, b0_11, b1_11, b2_11, bf11, rt11, ft11⟩ :=
    split7 (R := .x11) (o := 33) (r := 5) (codeAt_uf hR 26 rfl) pa11' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra11 .x10 (by decide), c3x10]) (by rw [Ra11 .x11 (by decide), c3x11])
      (by norm_num) n11 (by have := r5Rank_lt v 11; omega)
  have D11 : DInv t11 ds (33 + 3) :=
    DInv.step' (D10.frame (by norm_num) fa11) (by norm_num) b0_11 b1_11 b2_11 bf11 (udig5' hd 11 33 rfl (by norm_num))
  have R11 : RegsExcept c3 t11 [.x28, .x29] := (Ra11.trans rt11).mono (by decide)
  have F11 : Frame c3 t11 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F10.trans fa11).trans ft11).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt11' : t11.pc = pcOf (uBase b + 118) := by rw [pt11]; simp only [pcOf_4]
  -- group 12
  obtain ⟨a12, sa12, pa12, va12, ra12, fa12⟩ := ug12_spec (codeAt_uf hR 27 rfl) t11 pt11'
  have Ra12 : RegsExcept c3 a12 [.x28, .x29] := (R11.trans ra12).mono (by decide)
  have n12 : a12.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 12) := by
    rw [va12, R11 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 21 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 21) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 12 (by norm_num)]
    try norm_num
  have pa12' : a12.pc = pcOf (uBase b + 121) := by rw [pa12]; simp only [pcOf_4]
  obtain ⟨t12, st12, pt12, b0_12, b1_12, b2_12, bf12, rt12, ft12⟩ :=
    split7 (R := .x11) (o := 36) (r := 5) (codeAt_uf hR 28 rfl) pa12' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra12 .x10 (by decide), c3x10]) (by rw [Ra12 .x11 (by decide), c3x11])
      (by norm_num) n12 (by have := r5Rank_lt v 12; omega)
  have D12 : DInv t12 ds (36 + 3) :=
    DInv.step' (D11.frame (by norm_num) fa12) (by norm_num) b0_12 b1_12 b2_12 bf12 (udig5' hd 12 36 rfl (by norm_num))
  have R12 : RegsExcept c3 t12 [.x28, .x29] := (Ra12.trans rt12).mono (by decide)
  have F12 : Frame c3 t12 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F11.trans fa12).trans ft12).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt12' : t12.pc = pcOf (uBase b + 128) := by rw [pt12]; simp only [pcOf_4]
  -- group 13
  obtain ⟨a13, sa13, pa13, va13, ra13, fa13⟩ := ug13_spec (codeAt_uf hR 29 rfl) t12 pt12'
  have Ra13 : RegsExcept c3 a13 [.x28, .x29] := (R12.trans ra13).mono (by decide)
  have n13 : a13.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 13) := by
    rw [va13, R12 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 28 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 28) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 13 (by norm_num)]
    try norm_num
  have pa13' : a13.pc = pcOf (uBase b + 131) := by rw [pa13]; simp only [pcOf_4]
  obtain ⟨t13, st13, pt13, b0_13, b1_13, b2_13, bf13, rt13, ft13⟩ :=
    split7 (R := .x11) (o := 39) (r := 5) (codeAt_uf hR 30 rfl) pa13' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra13 .x10 (by decide), c3x10]) (by rw [Ra13 .x11 (by decide), c3x11])
      (by norm_num) n13 (by have := r5Rank_lt v 13; omega)
  have D13 : DInv t13 ds (39 + 3) :=
    DInv.step' (D12.frame (by norm_num) fa13) (by norm_num) b0_13 b1_13 b2_13 bf13 (udig5' hd 13 39 rfl (by norm_num))
  have R13 : RegsExcept c3 t13 [.x28, .x29] := (Ra13.trans rt13).mono (by decide)
  have F13 : Frame c3 t13 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F12.trans fa13).trans ft13).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt13' : t13.pc = pcOf (uBase b + 138) := by rw [pt13]; simp only [pcOf_4]
  -- group 14
  obtain ⟨a14, sa14, pa14, va14, ra14, fa14⟩ := ug14_spec (codeAt_uf hR 31 rfl) t13 pt13'
  have Ra14 : RegsExcept c3 a14 [.x28, .x29] := (R13.trans ra14).mono (by decide)
  have n14 : a14.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 14) := by
    rw [va14, R13 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 35 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 35) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 14 (by norm_num)]
    try norm_num
  have pa14' : a14.pc = pcOf (uBase b + 141) := by rw [pa14]; simp only [pcOf_4]
  obtain ⟨t14, st14, pt14, b0_14, b1_14, b2_14, bf14, rt14, ft14⟩ :=
    split7 (R := .x11) (o := 42) (r := 5) (codeAt_uf hR 32 rfl) pa14' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra14 .x10 (by decide), c3x10]) (by rw [Ra14 .x11 (by decide), c3x11])
      (by norm_num) n14 (by have := r5Rank_lt v 14; omega)
  have D14 : DInv t14 ds (42 + 3) :=
    DInv.step' (D13.frame (by norm_num) fa14) (by norm_num) b0_14 b1_14 b2_14 bf14 (udig5' hd 14 42 rfl (by norm_num))
  have R14 : RegsExcept c3 t14 [.x28, .x29] := (Ra14.trans rt14).mono (by decide)
  have F14 : Frame c3 t14 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F13.trans fa14).trans ft14).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt14' : t14.pc = pcOf (uBase b + 148) := by rw [pt14]; simp only [pcOf_4]
  -- group 15
  obtain ⟨a15, sa15, pa15, va15, ra15, fa15⟩ := ug15_spec (codeAt_uf hR 33 rfl) t14 pt14'
  have Ra15 : RegsExcept c3 a15 [.x28, .x29] := (R14.trans ra15).mono (by decide)
  have n15 : a15.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 15) := by
    rw [va15, R14 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 42 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 42) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 15 (by norm_num)]
    try norm_num
  have pa15' : a15.pc = pcOf (uBase b + 151) := by rw [pa15]; simp only [pcOf_4]
  obtain ⟨t15, st15, pt15, b0_15, b1_15, b2_15, bf15, rt15, ft15⟩ :=
    split7 (R := .x11) (o := 45) (r := 5) (codeAt_uf hR 34 rfl) pa15' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra15 .x10 (by decide), c3x10]) (by rw [Ra15 .x11 (by decide), c3x11])
      (by norm_num) n15 (by have := r5Rank_lt v 15; omega)
  have D15 : DInv t15 ds (45 + 3) :=
    DInv.step' (D14.frame (by norm_num) fa15) (by norm_num) b0_15 b1_15 b2_15 bf15 (udig5' hd 15 45 rfl (by norm_num))
  have R15 : RegsExcept c3 t15 [.x28, .x29] := (Ra15.trans rt15).mono (by decide)
  have F15 : Frame c3 t15 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F14.trans fa15).trans ft15).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt15' : t15.pc = pcOf (uBase b + 158) := by rw [pt15]; simp only [pcOf_4]
  -- group 16
  obtain ⟨a16, sa16, pa16, va16, ra16, fa16⟩ := ug16_spec (codeAt_uf hR 35 rfl) t15 pt15'
  have Ra16 : RegsExcept c3 a16 [.x28, .x29] := (R15.trans ra16).mono (by decide)
  have n16 : a16.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 16) := by
    rw [va16, R15 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 49 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 49) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 16 (by norm_num)]
    try norm_num
  have pa16' : a16.pc = pcOf (uBase b + 161) := by rw [pa16]; simp only [pcOf_4]
  obtain ⟨t16, st16, pt16, b0_16, b1_16, b2_16, bf16, rt16, ft16⟩ :=
    split7 (R := .x11) (o := 48) (r := 5) (codeAt_uf hR 36 rfl) pa16' rfl rfl rfl rfl rfl rfl rfl (by decide)
      rfl rfl rfl (by norm_num) (by rw [Ra16 .x10 (by decide), c3x10]) (by rw [Ra16 .x11 (by decide), c3x11])
      (by norm_num) n16 (by have := r5Rank_lt v 16; omega)
  have D16 : DInv t16 ds (48 + 3) :=
    DInv.step' (D15.frame (by norm_num) fa16) (by norm_num) b0_16 b1_16 b2_16 bf16 (udig5' hd 16 48 rfl (by norm_num))
  have R16 : RegsExcept c3 t16 [.x28, .x29] := (Ra16.trans rt16).mono (by decide)
  have F16 : Frame c3 t16 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F15.trans fa16).trans ft16).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt16' : t16.pc = pcOf (uBase b + 168) := by rw [pt16]; simp only [pcOf_4]
  obtain ⟨t, sret, pret, rret, fret⟩ := ret_spec (codeAt_uf hR 37 rfl) t16 pt16'
  refine ⟨t, (((((((((((((((((((((((((((((((((((((s1.trans sb51).trans s3).trans sa0).trans st0).trans sa1).trans st1).trans sa2).trans st2).trans sa3).trans st3).trans sa4).trans st4).trans sa5).trans st5).trans sa6).trans st6).trans sa7).trans st7).trans sa8).trans st8).trans sa9).trans st9).trans sa10).trans st10).trans sa11).trans st11).trans sa12).trans st12).trans sa13).trans st13).trans sa14).trans st14).trans sa15).trans st15).trans sa16).trans st16).trans sret).of_eq rfl rfl, ?_, ?_, ?_, ?_⟩
  · rw [pret, R16 .x1 (by decide), r3 .x1 (by decide), r2 .x1 (by decide), r1 .x1 (by decide)]; rfl
  · intro j hj
    rw [fret.getByte (by omega) (fun h => h)]
    exact D16 j (by omega)
  · exact ((((r1.trans r2).trans r3).trans R16).trans rret).mono (by decide)
  · exact ((((f1.trans f2).trans f3).trans F16).trans fret).mono (fun A _ h => by
      simp only [or_false, false_or] at h; rcases h with h | h <;> exact h)

end SigGolfCandidate.T3M.Search.R6
end
