import SigGolfCandidate.Merge060
import SigGolfCandidate.FtsExpandSearch
import SigGolfCandidate.FtsExpandPost
set_option debug.skipKernelTC true
set_option linter.all false

/-! # S5185 (FTS16, TIER2): the expand level-2 code (`Images.expandFts16Code`, words 57000..59135)

Image units (A70 `expand.code`, decoded word by word; TIER2 E9/E10/E12):
* 57066..57116 `S2LO`, 57117..57167 `S2HI` (51 words each, identical except word 17, the half load
  `ld t4,8(a2)` / `ld t4,24(a2)`): `sd t4,1120(zero)`; `t4 := 3400`; `bgeu s0,t4,+5`; plain path (`s0 < 3400`,
  coordinate 8): `ld t4,1120; sd zero,1120; ecall; jalr zero,0(a6)`; ground path: save `a4 a7 t6`, `a4 := a2`,
  `a2 := SCR`, `a7 := 0`; trial `sd a7,32(a0); sd zero,40(a0); ecall`; `srli 63` of the kept half's top dword, stop
  on 0 or at `a7 = 255`; copy `SCR -> a4`, clear `SCR`, record `(a0 + WADJ, a7)` at `slotA s0 + 16`, `a2 := a4`,
  restore and clear the saves, `jalr zero,0(a6)` (57116 / 57167).
* 57168..57215 `COPY2`: `t6 := slotA (sB 0) + 16`; nine `{ld t4,0(t6); beq t4,zero,+3; ld t5,8(t6); sd t5,0(t4);
  addi t6,t6,-1696}`; the halting `ecall` at 57215 (`HALT2`), entered from `POST + 38 = 61088: jal zero,57168`.
* 57216..59135 `TRAMP2`: 384 `trampWords b (s2Base hi) (site2C + 1)` (checked in `FtsExpandImage`). -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)

/-! ## Words: sub-windows of `Images.expandFts16Code` -/

/-- `expandFts16Code` slice `[a, b)` (word indices). -/
def f16w (a b : Nat) : List (BitVec 32) := (Images.expandFts16Code.drop (a - FTS16)).take (b - a)
/-- E9: the level-2 search keeping half `hi` (51 words at `s2Base hi`). -/
def search2Words (hi : Bool) : List (BitVec 32) := f16w (s2Base hi) (s2Base hi + 51)
/-- E10: the level-2 record pass and the halt (48 words at `COPY2`, last = `ecall` at `HALT2`). -/
def copy2Words : List (BitVec 32) := f16w COPY2 (HALT2 + 1)
/-- E12: the 384 level-2 trampolines (1920 words at `TRAMP2`). -/
def tramp2Words : List (BitVec 32) := f16w TRAMP2 (TRAMP2 + 1920)

theorem fts16_length : Images.expandFts16Code.length = 2136 := by decide +kernel

theorem codeAt_fts16 : CodeAt Images.expandImage (pcOf FTS16) Images.expandFts16Code := by
  apply SigGolfCandidate.T3M.codeAt_expand_lastR <;> decide +kernel

theorem code_f16w (a b : Nat) (ha : FTS16 ≤ a) (hab : a ≤ b) (hb : b ≤ FTS16 + 2136) :
    CodeAt Images.expandImage (pcOf a) (f16w a b) := by
  have := codeAt_sub (a - FTS16) codeAt_fts16 (seg := f16w a b) (by simp [f16w, fts16_length]; omega)
    (by simp [f16w])
  rwa [show FTS16 + (a - FTS16) = a by omega] at this

theorem codeAt_search2 (hi : Bool) : CodeAt Images.expandImage (pcOf (s2Base hi)) (search2Words hi) :=
  code_f16w _ _ (by cases hi <;> decide) (by omega) (by cases hi <;> decide)
theorem codeAt_copy2 : CodeAt Images.expandImage (pcOf COPY2) copy2Words :=
  code_f16w _ _ (by decide) (by decide) (by decide)
theorem codeAt_tramp2s : CodeAt Images.expandImage (pcOf TRAMP2) tramp2Words :=
  code_f16w _ _ (by decide) (by decide) (by decide)

/-- Image shape (decoded): plain-path `ecall` at +6 and `jalr zero,0(a6)` at +7, the trial `ecall` at +16, the half
load at +17 (`ld t4,8(a2)` low / `ld t4,24(a2)` high), the cap `addi t4,zero,255` at +20, the exit `jalr` at +50;
the two searches differ only at +17; `copy2` ends with the `ecall` at `HALT2`. -/
theorem fts16_shape :
    (search2Words false)[6]? = some 0x73 ∧ (search2Words false)[7]? = some 0x80067 ∧
    (search2Words false)[16]? = some 0x73 ∧ (search2Words false)[17]? = some 0x863e83 ∧
    (search2Words true)[17]? = some 0x1863e83 ∧ (search2Words false)[20]? = some 0xff00e93 ∧
    (search2Words false)[50]? = some 0x80067 ∧
    (∀ i < 51, i ≠ 17 → (search2Words false)[i]? = (search2Words true)[i]?) ∧
    copy2Words.length = 48 ∧ copy2Words[47]? = some 0x73 := by
  decide +kernel

/-! ## E9: the level-2 search behind a trampoline -/

/-- The level-2 node of the coordinate with FTS frame base `S0`: the half-aware width-1 ground fold when
`3400 ≤ S0` (coordinates 0..7: `sB k ≥ 3832`), else the plain hash of the block as it stands (coordinate 8,
`sB 8 = 2984`). Matches `childStepG`'s level-2 branch (`groundFoldH (hiOut j 3) 1`). -/
def node2 (hi : Bool) (S0 : Nat) (pre mid right : List UInt8) : M (Nat × HashOutput) :=
  if 3400 ≤ S0 then groundFoldH hi 1 pre right else (fun a => (0, a)) <$> publicHash (pre ++ mid ++ right)

/-- Cycles of one trampoline round trip into a level-2 search (COMPUTED from the words, 1 cycle per instruction and
8 per one-block `ecall`, the cost model of `W_SEARCH`): ground `12 + 17 n + 15 + 27 + 3` for `n = FUEL 1` failed
trials; plain 20. -/
def W_SEARCH2 : Nat := 17 * FUEL 1 + 57

/-- The level-2 record of frame base `S0` (witness pad address, nonce), 16 bytes above the level-3 record. -/
def slot2 (S0 : Nat) : Nat := slotA S0 + 16

/-- A level-2 trampoline call at word `b` returning to `ret`: trial block at `A` = `pre` (32) ‖ `mid` (16, the pad)
‖ `right` (16); answer to `D`; FTS frame base `S0`. -/
structure Search2In (b ret A D S0 : Nat) (pre mid right : List UInt8) (s : MachineState) : Prop where
  pc : s.pc = pcOf b
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 S0
  x10 : s.getReg .x10 = BitVec.ofNat 64 A
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
  x12 : s.getReg .x12 = BitVec.ofNat 64 D
  lpre : pre.length = 32
  lmid : mid.length = 16
  lright : right.length = 16
  mpre : s.readWords (BitVec.ofNat 64 A) 4 = wordsOf pre
  mmid : s.readWords (BitVec.ofNat 64 (A + 32)) 2 = wordsOf mid
  mright : s.readWords (BitVec.ofNat 64 (A + 48)) 2 = wordsOf right
  hA : A % 8 = 0
  hA1 : 1144 ≤ A
  hA2 : A + 64 ≤ SCR
  hD : D % 8 = 0
  hD1 : 1144 ≤ D
  hD2 : D + 32 ≤ SCR
  hS0 : S0 % 8 = 0
  hS1 : 16 ≤ S0
  hS2 : S0 < 2 ^ 14
  hb : b + 5 < 2 ^ 18
  hret : ret < 2 ^ 18

/-- Words a level-2 search call may write. -/
def SearchW2 (A D S0 : Nat) (X : Nat) : Prop :=
  (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ X = A + 32 ∨ X = A + 40 ∨ (slot2 S0 ≤ X ∧ X < slot2 S0 + 16) ∨
    (1104 ≤ X ∧ X < 1144) ∨ (SCR ≤ X ∧ X < SCR + 32)

/-- Back at `ret` with the level-2 answer at `D`. Ground (`3400 ≤ S0`): as `SearchOut` with the record at `slot2`;
plain: nonce 0, only `D` and the `t4` save word (left 0) written. -/
structure Search2Out (s : MachineState) (ret A D S0 : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = res.2.extractLsb' (64 * k) 64
  nle : res.1 ≤ FUEL 1
  pad32 : 3400 ≤ S0 → ¬ (D ≤ A + 32 ∧ A + 32 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 res.1
  pad40 : 3400 ≤ S0 → ¬ (D ≤ A + 40 ∧ A + 40 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 40)) = 0
  rec0 : 3400 ≤ S0 → t.getMem (BitVec.ofNat 64 (slot2 S0)) = BitVec.ofNat 64 (A + WADJ)
  rec1 : 3400 ≤ S0 → t.getMem (BitVec.ofNat 64 (slot2 S0 + 8)) = BitVec.ofNat 64 res.1
  scr : 3400 ≤ S0 → ∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0
  saves : ∀ k < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) =
    if 3400 ≤ S0 ∨ k = 2 ∨ k = 4 then 0 else s.getMem (BitVec.ofNat 64 (1104 + 8 * k))
  plain : S0 < 3400 → res.1 = 0 ∧
    Frame s t (fun X => X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24 ∨ X = 1120 ∨ X = 1136)
  frame : Frame s t (SearchW2 A D S0)

/-- Window of `search2Words hi`. -/
def s2w (hi : Bool) (a b : Nat) : List (BitVec 32) := (search2Words hi).drop (a - s2Base hi) |>.take (b - a)

theorem search2Words_length (hi : Bool) : (search2Words hi).length = 51 := by cases hi <;> decide +kernel

theorem code_s2w {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi)) (a b : Nat)
    (ha : s2Base hi ≤ a) (hb : b ≤ s2Base hi + 51) (hab : a ≤ b) : CodeAt im (pcOf a) (s2w hi a b) := by
  have hlen := search2Words_length hi
  have := codeAt_sub (a - s2Base hi) hS (seg := s2w hi a b) (by simp [s2w, hlen]; omega) (by simp [s2w])
  rwa [show s2Base hi + (a - s2Base hi) = a by omega] at this

theorem s2_entry_words (hi : Bool) :
    s2w hi (s2Base hi) (s2Base hi + 4) = [0x47d03023, 0x1eb7, 0xd48e8e93, 0x1d47a63] := by
  cases hi <;> decide +kernel

theorem pcOf_add_w (n k : Nat) : pcOf n + BitVec.ofNat 64 (4 * k) = pcOf (n + k) := by
  show BitVec.ofNat 64 (0x1000 + 4 * n) + BitVec.ofNat 64 (4 * k) = BitVec.ofNat 64 (0x1000 + 4 * (n + k))
  rw [ofNat_add_ofNat]; congr 1; ring

theorem s2_entry_code {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi)) :
    CodeAt im (pcOf (s2Base hi)) [0x47d03023] ∧ CodeAt im (pcOf (s2Base hi + 1)) [0x1eb7] ∧
    CodeAt im (pcOf (s2Base hi + 2)) [0xd48e8e93] ∧ CodeAt im (pcOf (s2Base hi + 3)) [0x1d47a63] := by
  have h4 := code_s2w hS (s2Base hi) (s2Base hi + 4) (by omega) (by omega) (by omega)
  rw [s2_entry_words hi] at h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using codeAt_sub 0 h4 (seg := [0x47d03023]) (by simp) rfl
  · have := codeAt_sub 1 h4 (seg := [0x1eb7]) (by simp) rfl; simpa using this
  · have := codeAt_sub 2 h4 (seg := [0xd48e8e93]) (by simp) rfl; simpa using this
  · have := codeAt_sub 3 h4 (seg := [0x1d47a63]) (by simp) rfl; simpa using this

/-- 57066..57069 (and 57117..57120): save `t4` at 1120, `t4 := 3400`, dispatch on the frame base. -/
theorem s2_entry_spec {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
    (s : MachineState) (hpc : s.pc = pcOf (s2Base hi)) (S0 : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (hS0 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf (s2Base hi + if 3400 ≤ S0 then 8 else 4) ∧ RegsExcept s t [.x29] ∧
      t.getReg .x29 = BitVec.ofNat 64 3400 ∧ t.getMem (BitVec.ofNat 64 1120) = s.getReg .x29 ∧
      Frame s t (fun X => X = 1120) := by
  obtain ⟨c0, c1, c2, c3⟩ := s2_entry_code hS
  have e0 : s.getReg .x0 + signExtend12 (1120 : BitVec 12) = BitVec.ofNat 64 1120 := by
    show (0 : Word) + signExtend12 (1120 : BitVec 12) = _; decide
  have hav0 : accessValid (BitVec.ofNat 64 1120) 8 = true := by decide
  have step1 : Steps im s 1 1 ((s.setMem (BitVec.ofNat 64 1120) (s.getReg .x29)).setPC (pcOf (s2Base hi + 1))) :=
    micro_step (i := .base (.SD .x0 .x29 1120)) (m := .store .d .x0 .x29 (signExtend12 1120)) c0 rfl rfl hpc
      (by simp only [Micro.exec, e0, hav0, StoreKind.width, if_true, StoreKind.write, hpc, pcOf_add4])
  set s1 := (s.setMem (BitVec.ofNat 64 1120) (s.getReg .x29)).setPC (pcOf (s2Base hi + 1)) with hs1def
  have hpc_s1 : s1.pc = pcOf (s2Base hi + 1) := rfl
  have hmem_s1 : ∀ A, s1.getMem A = if A = BitVec.ofNat 64 1120 then s.getReg .x29 else s.getMem A := by
    intro A; rw [hs1def, MachineState.getMem_setPC]; simp [MachineState.setMem, MachineState.getMem]
  have h8_s1 : s1.getReg .x8 = BitVec.ofNat 64 S0 := by
    rw [hs1def, MachineState.getReg_setPC, getReg_setMem']; exact h8
  have step2 : Steps im s1 1 1 ((s1.setReg .x29 (luiVal (1 : BitVec 20))).setPC (pcOf (s2Base hi + 2))) :=
    micro_step (i := .base (.LUI .x29 (1 : BitVec 20)))
      (m := .alu .x29 .add (.imm (luiVal (1 : BitVec 20))) (.imm 0)) c1 rfl rfl hpc_s1
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc_s1, pcOf_add4, add_zero])
  set s2 := (s1.setReg .x29 (luiVal (1 : BitVec 20))).setPC (pcOf (s2Base hi + 2)) with hs2def
  have hx29_s2 : s2.getReg .x29 = luiVal (1 : BitVec 20) := by
    rw [hs2def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x29 : Reg) ≠ .x0)]
  have hpc_s2 : s2.pc = pcOf (s2Base hi + 2) := rfl
  have hmem_s2 : ∀ A, s2.getMem A = if A = BitVec.ofNat 64 1120 then s.getReg .x29 else s.getMem A := by
    intro A; rw [hs2def, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hmem_s1 A
  have h8_s2 : s2.getReg .x8 = BitVec.ofNat 64 S0 := by
    rw [hs2def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x29:Reg) ≠ .x8)]
    exact h8_s1
  have hlui : luiVal (1 : BitVec 20) = BitVec.ofNat 64 4096 := by decide
  have e2 : s2.getReg .x29 + signExtend12 (0xD48 : BitVec 12) = BitVec.ofNat 64 3400 := by
    rw [hx29_s2, hlui]; decide
  have step3 : Steps im s2 1 1
      ((s2.setReg .x29 (s2.getReg .x29 + signExtend12 (0xD48 : BitVec 12))).setPC (pcOf (s2Base hi + 3))) :=
    micro_step (i := .base (.ADDI .x29 .x29 (0xD48 : BitVec 12)))
      (m := .alu .x29 .add (.reg .x29) (.imm (signExtend12 (0xD48 : BitVec 12)))) c2 rfl rfl hpc_s2
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc_s2, pcOf_add4])
  set s3 := (s2.setReg .x29 (s2.getReg .x29 + signExtend12 (0xD48 : BitVec 12))).setPC (pcOf (s2Base hi + 3))
    with hs3def
  have hx29_s3 : s3.getReg .x29 = BitVec.ofNat 64 3400 := by
    rw [hs3def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x29:Reg) ≠ .x0)]
    exact e2
  have hpc_s3 : s3.pc = pcOf (s2Base hi + 3) := rfl
  have hmem_s3 : ∀ A, s3.getMem A = if A = BitVec.ofNat 64 1120 then s.getReg .x29 else s.getMem A := by
    intro A; rw [hs3def, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hmem_s2 A
  have h8_s3 : s3.getReg .x8 = BitVec.ofNat 64 S0 := by
    rw [hs3def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x29:Reg) ≠ .x8)]
    exact h8_s2
  have hcond : (BitVec.ult (BitVec.ofNat 64 S0) (BitVec.ofNat 64 3400) : Bool) = decide (S0 < 3400) := by
    have h1 : (BitVec.ofNat 64 S0).toNat = S0 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (BitVec.ofNat 64 3400).toNat = 3400 := by decide
    rw [BitVec.ult, h1, h2]
  by_cases hlt : S0 < 3400
  · have hbranch : CmpOp.eval .geu (s3.getReg .x8) (s3.getReg .x29) = false := by
      rw [h8_s3, hx29_s3]
      show (!(BitVec.ult (BitVec.ofNat 64 S0) (BitVec.ofNat 64 3400))) = false
      rw [hcond]; simp [hlt]
    have step4 : Steps im s3 1 1 (s3.setPC (s3.pc + 4)) :=
      micro_step (i := .base (.BGEU .x8 .x29 (20 : BitVec 13))) (m := .branch .geu .x8 .x29 (signExtend13 20)) c3
        rfl rfl hpc_s3 (by simp [Micro.exec, hbranch])
    refine ⟨_, step1.trans (step2.trans (step3.trans step4)), ?_, ?_, ?_, ?_, ?_⟩
    · show (s3.setPC (s3.pc + 4)).pc = pcOf (s2Base hi + if 3400 ≤ S0 then 8 else 4)
      rw [if_neg (by omega : ¬ 3400 ≤ S0)]
      show s3.pc + 4 = pcOf (s2Base hi + 4)
      rw [hpc_s3, pcOf_add4]
    · intro r hr
      simp only [List.mem_singleton] at hr
      rw [MachineState.getReg_setPC, hs3def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs2def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs1def, MachineState.getReg_setPC, getReg_setMem']
    · rw [MachineState.getReg_setPC]; exact hx29_s3
    · rw [MachineState.getMem_setPC]; rw [hmem_s3 (BitVec.ofNat 64 1120), if_pos rfl]
    · intro A _ hne
      rw [MachineState.getMem_setPC, hmem_s3 (BitVec.ofNat 64 A)]
      rw [if_neg (fun heq => hne (by
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat] at this
        omega))]
  · have hbranch : CmpOp.eval .geu (s3.getReg .x8) (s3.getReg .x29) = true := by
      rw [h8_s3, hx29_s3]
      show (!(BitVec.ult (BitVec.ofNat 64 S0) (BitVec.ofNat 64 3400))) = true
      rw [hcond]; simp [hlt]
    have step4 : Steps im s3 1 1 (s3.setPC (s3.pc + signExtend13 (20 : BitVec 13))) :=
      micro_step (i := .base (.BGEU .x8 .x29 (20 : BitVec 13))) (m := .branch .geu .x8 .x29 (signExtend13 20)) c3
        rfl rfl hpc_s3 (by simp [Micro.exec, hbranch])
    refine ⟨_, step1.trans (step2.trans (step3.trans step4)), ?_, ?_, ?_, ?_, ?_⟩
    · show (s3.setPC (s3.pc + signExtend13 (20 : BitVec 13))).pc =
        pcOf (s2Base hi + if 3400 ≤ S0 then 8 else 4)
      rw [if_pos (by omega : 3400 ≤ S0)]
      show s3.pc + signExtend13 (20 : BitVec 13) = pcOf (s2Base hi + 8)
      rw [hpc_s3, show signExtend13 (20 : BitVec 13) = BitVec.ofNat 64 (4 * 5) from by decide, pcOf_add_w]
    · intro r hr
      simp only [List.mem_singleton] at hr
      rw [MachineState.getReg_setPC, hs3def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs2def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs1def, MachineState.getReg_setPC, getReg_setMem']
    · rw [MachineState.getReg_setPC]; exact hx29_s3
    · rw [MachineState.getMem_setPC]; rw [hmem_s3 (BitVec.ofNat 64 1120), if_pos rfl]
    · intro A _ hne
      rw [MachineState.getMem_setPC, hmem_s3 (BitVec.ofNat 64 A)]
      rw [if_neg (fun heq => hne (by
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat] at this
        omega))]

/-- The plain path from `s2Base hi + 4` (coordinate 8): restore `t4`, clear its save, then the hash `ecall`
(2 steps; the `jalr zero,0(a6)` follows at `+ 7`). -/
theorem s2_plain_spec {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
    (s : MachineState) (hpc : s.pc = pcOf (s2Base hi + 4)) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (s2Base hi + 6) ∧ fetch im t = some (.base .ECALL) ∧
      RegsExcept s t [.x29] ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getMem (BitVec.ofNat 64 1120) = 0 ∧ Frame s t (fun X => X = 1120) := by
  have hwords : s2w hi (s2Base hi + 4) (s2Base hi + 6) = [0x46003e83, 0x46003023] := by
    cases hi <;> decide +kernel
  have h2 := code_s2w hS (s2Base hi + 4) (s2Base hi + 6) (by omega) (by omega) (by omega)
  rw [hwords] at h2
  have c0 : CodeAt im (pcOf (s2Base hi + 4)) [0x46003e83] := by
    simpa using codeAt_sub 0 h2 (seg := [0x46003e83]) (by simp) rfl
  have c1 : CodeAt im (pcOf (s2Base hi + 5)) [0x46003023] := by
    have := codeAt_sub 1 h2 (seg := [0x46003023]) (by simp) rfl; simpa using this
  have e0 : s.getReg .x0 + signExtend12 (1120 : BitVec 12) = BitVec.ofNat 64 1120 := by
    show (0 : Word) + signExtend12 (1120 : BitVec 12) = _; decide
  have hav0 : accessValid (BitVec.ofNat 64 1120) 8 = true := by decide
  have step1 : Steps im s 1 1 ((s.setReg .x29 (s.getMem (BitVec.ofNat 64 1120))).setPC (pcOf (s2Base hi + 5))) :=
    micro_step (i := .base (.LD .x29 .x0 1120)) (m := .load .d .x29 .x0 (signExtend12 1120)) c0 rfl rfl hpc
      (by simp only [Micro.exec, e0, hav0, LoadKind.width, if_true, LoadKind.read, hpc, pcOf_add4])
  set s1 := (s.setReg .x29 (s.getMem (BitVec.ofNat 64 1120))).setPC (pcOf (s2Base hi + 5)) with hs1def
  have hx29_s1 : s1.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) := by
    rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x29 : Reg) ≠ .x0)]
  have hpc_s1 : s1.pc = pcOf (s2Base hi + 5) := rfl
  have e1 : s1.getReg .x0 + signExtend12 (1120 : BitVec 12) = BitVec.ofNat 64 1120 := by
    show (0 : Word) + signExtend12 (1120 : BitVec 12) = _; decide
  have step2 : Steps im s1 1 1 ((s1.setMem (BitVec.ofNat 64 1120) (s1.getReg .x0)).setPC (pcOf (s2Base hi + 6))) :=
    micro_step (i := .base (.SD .x0 .x0 1120)) (m := .store .d .x0 .x0 (signExtend12 1120)) c1 rfl rfl hpc_s1
      (by simp only [Micro.exec, e1, hav0, StoreKind.width, if_true, StoreKind.write, hpc_s1, pcOf_add4])
  set s2 := (s1.setMem (BitVec.ofNat 64 1120) (s1.getReg .x0)).setPC (pcOf (s2Base hi + 6)) with hs2def
  have hpc_s2 : s2.pc = pcOf (s2Base hi + 6) := rfl
  have hword6 : s2w hi (s2Base hi + 6) (s2Base hi + 7) = [0x73] := by cases hi <;> decide +kernel
  have h6 := code_s2w hS (s2Base hi + 6) (s2Base hi + 7) (by omega) (by omega) (by omega)
  rw [hword6] at h6
  have getMemSetMemLocal : ∀ (u : MachineState) (a v A : Word),
      (u.setMem a v).getMem A = if A = a then v else u.getMem A := by
    intro u a v A; simp [MachineState.setMem, MachineState.getMem]
  refine ⟨s2, step1.trans step2, hpc_s2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h6.fetch s2 hpc_s2]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    rw [hs2def, MachineState.getReg_setPC, getReg_setMem', hs1def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · exact hx29_s1
  · rw [hs2def, MachineState.getMem_setPC, getMemSetMemLocal, if_pos rfl]
    simp [MachineState.getReg]
  · intro A hA hne
    rw [hs2def, MachineState.getMem_setPC, getMemSetMemLocal]
    rw [if_neg (fun heq => hne (by
      have heq' := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at heq'
      rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show 1120 < 2 ^ 64 by norm_num)] at heq'
      exact heq'))]
    rw [hs1def, MachineState.getMem_setPC, MachineState.getMem_setReg]

/-! ## E9 proof: the level-2 search blocks (ground path `+ 8 .. + 50`, plain `jalr` at `+ 7`) -/

section p4t

attribute [local rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat

def cfgS2 : Config := { noAlias := true }

theorem shr63_eq_zero (x : Word) : x >>> ((63#64 : Word).toNat % 64) = 0#64 ↔ x.toNat < 2 ^ 63 := by
  rw [show ((63#64 : Word).toNat % 64) = 63 from rfl]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero, Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
    exact Nat.div_eq_of_lt h

sym_block gH2L := symRun cfgS2 [0x44e03823, 0x45103c23, 0x47f03423, 0x60713, 0x7e0637, 0x893] (pcOf 57074) 20
sym_block gL2L := symRun cfgS2 [0x3153023, 0x2053423, 0x73] (pcOf 57080) 20
sym_block gC2L := symRun cfgS2 [0x863e83, 0x3fede93, 0xe8a63] (pcOf 57083) 20
sym_block gN2L := symRun cfgS2 [0xff00e93, 0x1d88663] (pcOf 57086) 20
sym_block gJ2L := symRun cfgS2 [0x188893, 0xfddff06f] (pcOf 57088) 20
sym_block gP2L := symRun cfgS2 [0x80067] (pcOf 57073) 20
sym_block gF2L := symRun cfgS2 [0x63e83, 0x1d73023, 0x863e83, 0x1d73423, 0x1063e83, 0x1d73823, 0x1863e83,
  0x1d73c23, 0x63023, 0x63423, 0x63823, 0x63c23, 0x141e93, 0xce8eb3, 0x11ebc23, 0x56850f93, 0x1feb823, 0x70613,
  0x45003703, 0x45803883, 0x46003e83, 0x46803f83, 0x44003823, 0x44003c23, 0x46003023, 0x46003423, 0x80067]
  (pcOf 57090) 40

theorem h0_2L {im : Image} (s : MachineState)
    (hc : CodeAt im (pcOf 57074) [0x44e03823, 0x45103c23, 0x47f03423, 0x60713, 0x7e0637, 0x893])
    (hpc : s.pc = pcOf 57074) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 57080 ∧
      t.getReg .x12 = BitVec.ofNat 64 SCR ∧ t.getReg .x14 = s.getReg .x12 ∧ t.getReg .x17 = 0 ∧
      RegsExcept s t [.x12, .x14, .x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112 ∨ X = 1128) := by
  refine ⟨_, symRun_sound gH2L hc s hpc (by simp [gH2L.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gH2L.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gH2L.res]; simp [rv_simp, SCR]
  · simp only [Result.toState_getReg, gH2L.res]; simp [rv_simp]
  · simp only [Result.toState_getReg, gH2L.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gH2L.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gH2L.res]; t3n []
  · simp only [Result.toState_getMem, gH2L.res]; t3n []
  · simp only [Result.toState_getMem, gH2L.res]; t3n []
  · intro X hX hn; simp only [Result.toState_getMem, gH2L.res]; t3n []
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

theorem l_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57080) [0x3153023, 0x2053423, 0x73])
    (hpc : s.pc = pcOf 57080) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 57082 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ t.getMem (BitVec.ofNat 64 (A + 40)) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = A + 40) ∧ fetch im t = some (.base .ECALL) := by
  have hob : gL2L.res.obligs s := by simp only [gL2L.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound gL2L hc s hpc hob, ?_, ?_, ?_, ?_, ?_, symRun_ecall gL2L hc s hob rfl⟩
  · simp [gL2L.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gL2L.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gL2L.res]; t3n [h10]; try rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, gL2L.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, gL2L.res]; t3n [h10]
    rw [if_neg (by omega), if_neg (by omega)]

theorem c_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57083) [0x863e83, 0x3fede93, 0xe8a63])
    (hpc : s.pc = pcOf 57083) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (SCR + 8))).toNat < 2 ^ 63 then pcOf 57090 else pcOf 57086) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gC2L hc s hpc (by simp only [gC2L.res]; t3n [h12, SCR]; norm_num), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gC2L.res, rv_simp, h12, SCR, ofNat_add_ofNat, beq_iff_eq]
    have hiff := shr63_eq_zero (s.getMem (BitVec.ofNat 64 (8257536 + 8)))
    by_cases h1 : s.getMem (BitVec.ofNat 64 (8257536 + 8)) >>> ((63#64 : Word).toNat % 64) = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [gC2L.res, rv_simp] <;> rfl
  · intro A _ _; simp [gC2L.res, rv_simp]

theorem n_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57086) [0xff00e93, 0x1d88663])
    (hpc : s.pc = pcOf 57086) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 255 then pcOf 57090 else pcOf 57088) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gN2L hc s hpc (by simp [gN2L.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gN2L.res, rv_simp, beq_iff_eq]
  · intro r hr; simp at hr; cases r <;> simp_all [gN2L.res, rv_simp] <;> rfl
  · intro A _ _; simp [gN2L.res, rv_simp]

theorem j_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57088) [0x188893, 0xfddff06f])
    (hpc : s.pc = pcOf 57088) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 57080 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gJ2L hc s hpc (by simp [gJ2L.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [gJ2L.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gJ2L.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gJ2L.res, rv_simp] <;> rfl
  · intro A _ _; simp [gJ2L.res, rv_simp]

theorem p_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57073) [0x80067])
    (hpc : s.pc = pcOf 57073) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf R ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gP2L hc s hpc (by simp [gP2L.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gP2L.res]; t3n [h16, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [gP2L.res, rv_simp] <;> rfl
  · intro A _ _; simp [gP2L.res, rv_simp]

set_option maxHeartbeats 1000000 in
theorem f_2L {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57090) [0x63e83, 0x1d73023, 0x863e83,
      0x1d73423, 0x1063e83, 0x1d73823, 0x1863e83, 0x1d73c23, 0x63023, 0x63423, 0x63823, 0x63c23, 0x141e93,
      0xce8eb3, 0x11ebc23, 0x56850f93, 0x1feb823, 0x70613, 0x45003703, 0x45803883, 0x46003e83, 0x46803f83,
      0x44003823, 0x44003c23, 0x46003023, 0x46003423, 0x80067])
    (hpc : s.pc = pcOf 57090) (A D S0 R : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h14 : s.getReg .x14 = BitVec.ofNat 64 D)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (h16 : s.getReg .x16 = pcOf R) (hA : A < 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1136 ≤ D) (hD2 : D + 32 ≤ SCR)
    (hS0 : S0 % 8 = 0) (hS1 : 16 ≤ S0) (hS2 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf R ∧
      t.getReg .x12 = BitVec.ofNat 64 D ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧ RegsExcept s t [.x12, .x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = s.getMem (BitVec.ofNat 64 (SCR + 8 * k))) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0)) = BitVec.ofNat 64 (A + WADJ) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0 + 8)) = s.getReg .x17 ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (SCR ≤ X ∧ X < SCR + 32) ∨
        (slot2 S0 ≤ X ∧ X < slot2 S0 + 16) ∨ (1104 ≤ X ∧ X < 1136)) := by
  simp only [SCR, slot2, slotA, WADJ] at h12 hD2 ⊢
  have hob : gF2L.res.obligs s := by
    simp only [gF2L.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [Nat.mod_eq_of_lt, not_false_eq_true, and_true, true_and]
    and_intros <;> omega
  refine ⟨_, symRun_sound gF2L hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hob
  · simp only [Result.toState_pc, gF2L.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, gF2L.res]; t3n [h14]
  · simp only [Result.toState_getReg, gF2L.res]; t3n []
  · simp only [Result.toState_getReg, gF2L.res]; t3n []
  · simp only [Result.toState_getReg, gF2L.res]; t3n []
  · simp only [Result.toState_getReg, gF2L.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gF2L.res, rv_simp] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · intro k hk
    simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, gF2L.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

sym_block gH2H := symRun cfgS2 [0x44e03823, 0x45103c23, 0x47f03423, 0x60713, 0x7e0637, 0x893] (pcOf 57125) 20
sym_block gL2H := symRun cfgS2 [0x3153023, 0x2053423, 0x73] (pcOf 57131) 20
sym_block gC2H := symRun cfgS2 [0x1863e83, 0x3fede93, 0xe8a63] (pcOf 57134) 20
sym_block gN2H := symRun cfgS2 [0xff00e93, 0x1d88663] (pcOf 57137) 20
sym_block gJ2H := symRun cfgS2 [0x188893, 0xfddff06f] (pcOf 57139) 20
sym_block gP2H := symRun cfgS2 [0x80067] (pcOf 57124) 20
sym_block gF2H := symRun cfgS2 [0x63e83, 0x1d73023, 0x863e83, 0x1d73423, 0x1063e83, 0x1d73823, 0x1863e83,
  0x1d73c23, 0x63023, 0x63423, 0x63823, 0x63c23, 0x141e93, 0xce8eb3, 0x11ebc23, 0x56850f93, 0x1feb823, 0x70613,
  0x45003703, 0x45803883, 0x46003e83, 0x46803f83, 0x44003823, 0x44003c23, 0x46003023, 0x46003423, 0x80067]
  (pcOf 57141) 40

theorem h0_2H {im : Image} (s : MachineState)
    (hc : CodeAt im (pcOf 57125) [0x44e03823, 0x45103c23, 0x47f03423, 0x60713, 0x7e0637, 0x893])
    (hpc : s.pc = pcOf 57125) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 57131 ∧
      t.getReg .x12 = BitVec.ofNat 64 SCR ∧ t.getReg .x14 = s.getReg .x12 ∧ t.getReg .x17 = 0 ∧
      RegsExcept s t [.x12, .x14, .x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112 ∨ X = 1128) := by
  refine ⟨_, symRun_sound gH2H hc s hpc (by simp [gH2H.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gH2H.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gH2H.res]; simp [rv_simp, SCR]
  · simp only [Result.toState_getReg, gH2H.res]; simp [rv_simp]
  · simp only [Result.toState_getReg, gH2H.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gH2H.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gH2H.res]; t3n []
  · simp only [Result.toState_getMem, gH2H.res]; t3n []
  · simp only [Result.toState_getMem, gH2H.res]; t3n []
  · intro X hX hn; simp only [Result.toState_getMem, gH2H.res]; t3n []
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

theorem l_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57131) [0x3153023, 0x2053423, 0x73])
    (hpc : s.pc = pcOf 57131) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 57133 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ t.getMem (BitVec.ofNat 64 (A + 40)) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = A + 40) ∧ fetch im t = some (.base .ECALL) := by
  have hob : gL2H.res.obligs s := by simp only [gL2H.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound gL2H hc s hpc hob, ?_, ?_, ?_, ?_, ?_, symRun_ecall gL2H hc s hob rfl⟩
  · simp [gL2H.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gL2H.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gL2H.res]; t3n [h10]; try rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, gL2H.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, gL2H.res]; t3n [h10]
    rw [if_neg (by omega), if_neg (by omega)]

theorem c_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57134) [0x1863e83, 0x3fede93, 0xe8a63])
    (hpc : s.pc = pcOf 57134) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (SCR + 24))).toNat < 2 ^ 63 then pcOf 57141 else pcOf 57137) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gC2H hc s hpc (by simp only [gC2H.res]; t3n [h12, SCR]; norm_num), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gC2H.res, rv_simp, h12, SCR, ofNat_add_ofNat, beq_iff_eq]
    have hiff := shr63_eq_zero (s.getMem (BitVec.ofNat 64 (8257536 + 24)))
    by_cases h1 : s.getMem (BitVec.ofNat 64 (8257536 + 24)) >>> ((63#64 : Word).toNat % 64) = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [gC2H.res, rv_simp] <;> rfl
  · intro A _ _; simp [gC2H.res, rv_simp]

theorem n_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57137) [0xff00e93, 0x1d88663])
    (hpc : s.pc = pcOf 57137) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 255 then pcOf 57141 else pcOf 57139) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gN2H hc s hpc (by simp [gN2H.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gN2H.res, rv_simp, beq_iff_eq]
  · intro r hr; simp at hr; cases r <;> simp_all [gN2H.res, rv_simp] <;> rfl
  · intro A _ _; simp [gN2H.res, rv_simp]

theorem j_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57139) [0x188893, 0xfddff06f])
    (hpc : s.pc = pcOf 57139) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 57131 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gJ2H hc s hpc (by simp [gJ2H.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [gJ2H.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gJ2H.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gJ2H.res, rv_simp] <;> rfl
  · intro A _ _; simp [gJ2H.res, rv_simp]

theorem p_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57124) [0x80067])
    (hpc : s.pc = pcOf 57124) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf R ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gP2H hc s hpc (by simp [gP2H.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gP2H.res]; t3n [h16, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [gP2H.res, rv_simp] <;> rfl
  · intro A _ _; simp [gP2H.res, rv_simp]

set_option maxHeartbeats 1000000 in
theorem f_2H {im : Image} (s : MachineState) (hc : CodeAt im (pcOf 57141) [0x63e83, 0x1d73023, 0x863e83,
      0x1d73423, 0x1063e83, 0x1d73823, 0x1863e83, 0x1d73c23, 0x63023, 0x63423, 0x63823, 0x63c23, 0x141e93,
      0xce8eb3, 0x11ebc23, 0x56850f93, 0x1feb823, 0x70613, 0x45003703, 0x45803883, 0x46003e83, 0x46803f83,
      0x44003823, 0x44003c23, 0x46003023, 0x46003423, 0x80067])
    (hpc : s.pc = pcOf 57141) (A D S0 R : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h14 : s.getReg .x14 = BitVec.ofNat 64 D)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (h16 : s.getReg .x16 = pcOf R) (hA : A < 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1136 ≤ D) (hD2 : D + 32 ≤ SCR)
    (hS0 : S0 % 8 = 0) (hS1 : 16 ≤ S0) (hS2 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf R ∧
      t.getReg .x12 = BitVec.ofNat 64 D ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧ RegsExcept s t [.x12, .x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = s.getMem (BitVec.ofNat 64 (SCR + 8 * k))) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0)) = BitVec.ofNat 64 (A + WADJ) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0 + 8)) = s.getReg .x17 ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (SCR ≤ X ∧ X < SCR + 32) ∨
        (slot2 S0 ≤ X ∧ X < slot2 S0 + 16) ∨ (1104 ≤ X ∧ X < 1136)) := by
  simp only [SCR, slot2, slotA, WADJ] at h12 hD2 ⊢
  have hob : gF2H.res.obligs s := by
    simp only [gF2H.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [Nat.mod_eq_of_lt, not_false_eq_true, and_true, true_and]
    and_intros <;> omega
  refine ⟨_, symRun_sound gF2H hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hob
  · simp only [Result.toState_pc, gF2H.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, gF2H.res]; t3n [h14]
  · simp only [Result.toState_getReg, gF2H.res]; t3n []
  · simp only [Result.toState_getReg, gF2H.res]; t3n []
  · simp only [Result.toState_getReg, gF2H.res]; t3n []
  · simp only [Result.toState_getReg, gF2H.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gF2H.res, rv_simp] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · intro k hk
    simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, gF2H.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

/-! ### Words and dispatchers (any half) -/

theorem code_s2k {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi)) (k n : Nat)
    {ws : List (BitVec 32)} (hk : k + n ≤ 51) (hw : s2w hi (s2Base hi + k) (s2Base hi + k + n) = ws) :
    CodeAt im (pcOf (s2Base hi + k)) ws := by
  have := code_s2w hS (s2Base hi + k) (s2Base hi + k + n) (by omega) (by omega) (by omega)
  rwa [hw] at this

theorem s2_words_h0 (hi : Bool) : s2w hi (s2Base hi + 8) (s2Base hi + 8 + 6) =
    [0x44e03823, 0x45103c23, 0x47f03423, 0x60713, 0x7e0637, 0x893] := by cases hi <;> decide +kernel
theorem s2_words_l (hi : Bool) : s2w hi (s2Base hi + 14) (s2Base hi + 14 + 3) = [0x3153023, 0x2053423, 0x73] := by
  cases hi <;> decide +kernel
theorem s2_words_cL : s2w false (s2Base false + 17) (s2Base false + 17 + 3) = [0x863e83, 0x3fede93, 0xe8a63] := by
  decide +kernel
theorem s2_words_cH : s2w true (s2Base true + 17) (s2Base true + 17 + 3) = [0x1863e83, 0x3fede93, 0xe8a63] := by
  decide +kernel
theorem s2_words_n (hi : Bool) : s2w hi (s2Base hi + 20) (s2Base hi + 20 + 2) = [0xff00e93, 0x1d88663] := by
  cases hi <;> decide +kernel
theorem s2_words_j (hi : Bool) : s2w hi (s2Base hi + 22) (s2Base hi + 22 + 2) = [0x188893, 0xfddff06f] := by
  cases hi <;> decide +kernel
theorem s2_words_p (hi : Bool) : s2w hi (s2Base hi + 7) (s2Base hi + 7 + 1) = [0x80067] := by
  cases hi <;> decide +kernel
theorem s2_words_f (hi : Bool) : s2w hi (s2Base hi + 24) (s2Base hi + 24 + 27) = [0x63e83, 0x1d73023, 0x863e83,
      0x1d73423, 0x1063e83, 0x1d73823, 0x1863e83, 0x1d73c23, 0x63023, 0x63423, 0x63823, 0x63c23, 0x141e93,
      0xce8eb3, 0x11ebc23, 0x56850f93, 0x1feb823, 0x70613, 0x45003703, 0x45803883, 0x46003e83, 0x46803f83,
      0x44003823, 0x44003c23, 0x46003023, 0x46003423, 0x80067] := by
  cases hi <;> decide +kernel

section blocks2
variable {im : Image} {hi : Bool} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi)) (s : MachineState)
include hS

theorem h0_2_spec (hpc : s.pc = pcOf (s2Base hi + 8)) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (s2Base hi + 14) ∧
      t.getReg .x12 = BitVec.ofNat 64 SCR ∧ t.getReg .x14 = s.getReg .x12 ∧ t.getReg .x17 = 0 ∧
      RegsExcept s t [.x12, .x14, .x17] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => X = 1104 ∨ X = 1112 ∨ X = 1128) := by
  have hc := code_s2k hS 8 6 (by omega) (s2_words_h0 hi)
  cases hi
  · exact h0_2L s hc hpc
  · exact h0_2H s hc hpc

theorem l_2_spec (hpc : s.pc = pcOf (s2Base hi + 14)) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (hA : A % 8 = 0) (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (s2Base hi + 16) ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ t.getMem (BitVec.ofNat 64 (A + 40)) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = A + 40) ∧ fetch im t = some (.base .ECALL) := by
  have hc := code_s2k hS 14 3 (by omega) (s2_words_l hi)
  cases hi
  · exact l_2L s hc hpc A h10 hA hA'
  · exact l_2H s hc hpc A h10 hA hA'

theorem c_2_spec (hpc : s.pc = pcOf (s2Base hi + 17)) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (SCR + 8 * (if hi then 3 else 1)))).toNat < 2 ^ 63
        then pcOf (s2Base hi + 24) else pcOf (s2Base hi + 20)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  cases hi
  · exact c_2L s (code_s2k hS 17 3 (by omega) s2_words_cL) hpc h12
  · exact c_2H s (code_s2k hS 17 3 (by omega) s2_words_cH) hpc h12

theorem n_2_spec (hpc : s.pc = pcOf (s2Base hi + 20)) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 255 then pcOf (s2Base hi + 24) else pcOf (s2Base hi + 22)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_s2k hS 20 2 (by omega) (s2_words_n hi)
  cases hi
  · exact n_2L s hc hpc
  · exact n_2H s hc hpc

theorem j_2_spec (hpc : s.pc = pcOf (s2Base hi + 22)) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (s2Base hi + 14) ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_s2k hS 22 2 (by omega) (s2_words_j hi)
  cases hi
  · exact j_2L s hc hpc
  · exact j_2H s hc hpc

theorem p_2_spec (hpc : s.pc = pcOf (s2Base hi + 7)) (R : Nat) (h16 : s.getReg .x16 = pcOf R) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf R ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_s2k hS 7 1 (by omega) (s2_words_p hi)
  cases hi
  · exact p_2L s hc hpc R h16
  · exact p_2H s hc hpc R h16

theorem f_2_spec (hpc : s.pc = pcOf (s2Base hi + 24)) (A D S0 R : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h14 : s.getReg .x14 = BitVec.ofNat 64 D)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (h16 : s.getReg .x16 = pcOf R) (hA : A < 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1136 ≤ D) (hD2 : D + 32 ≤ SCR)
    (hS0 : S0 % 8 = 0) (hS1 : 16 ≤ S0) (hS2 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf R ∧
      t.getReg .x12 = BitVec.ofNat 64 D ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧ RegsExcept s t [.x12, .x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = s.getMem (BitVec.ofNat 64 (SCR + 8 * k))) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0)) = BitVec.ofNat 64 (A + WADJ) ∧
      t.getMem (BitVec.ofNat 64 (slot2 S0 + 8)) = s.getReg .x17 ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (SCR ≤ X ∧ X < SCR + 32) ∨
        (slot2 S0 ≤ X ∧ X < slot2 S0 + 16) ∨ (1104 ≤ X ∧ X < 1136)) := by
  have hc := code_s2k hS 24 27 (by omega) (s2_words_f hi)
  cases hi
  · exact f_2L s hc hpc A D S0 R h10 h14 h12 h8 h16 hA hD hD1 hD2 hS0 hS1 hS2
  · exact f_2H s hc hpc A D S0 R h10 h14 h12 h8 h16 hA hD hD1 hD2 hS0 hS1 hS2

end blocks2

/-! ### The level-2 loop -/

/-- Registers the level-2 loop may hold changed. -/
def loopRegs2 : List Reg := [.x12, .x14, .x16, .x17, .x29]

/-- At word `pcw` of a level-2 search (ground path), after its entry, with nonce `n`. -/
structure AtS2 (s : MachineState) (b A D pcw n : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf pcw
  regs : RegsExcept s u loopRegs2
  x12 : u.getReg .x12 = BitVec.ofNat 64 SCR
  x14 : u.getReg .x14 = BitVec.ofNat 64 D
  x16 : u.getReg .x16 = pcOf (b + 2)
  x17 : u.getReg .x17 = BitVec.ofNat 64 n
  sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14
  sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17
  sv2 : u.getMem (BitVec.ofNat 64 1120) = s.getReg .x29
  sv3 : u.getMem (BitVec.ofNat 64 1128) = s.getReg .x31
  sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16
  frame : Frame s u (LoopW A)
  hn : n ≤ FUEL 1

theorem AtS2.move {s : MachineState} {b A D pcw pcw' n n' : Nat} {u w : MachineState} (h : AtS2 s b A D pcw n u)
    (hpc : w.pc = pcOf pcw') (hr : RegsExcept u w [.x17, .x29]) (hf : Frame u w (fun _ => False))
    (h17 : w.getReg .x17 = BitVec.ofNat 64 n') (hn : n' ≤ FUEL 1) : AtS2 s b A D pcw' n' w where
  pc := hpc
  regs := (h.regs.trans hr).mono (by decide)
  x12 := by rw [hr.get (by decide)]; exact h.x12
  x14 := by rw [hr.get (by decide)]; exact h.x14
  x16 := by rw [hr.get (by decide)]; exact h.x16
  x17 := h17
  sv0 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv0
  sv1 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv1
  sv2 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv2
  sv3 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv3
  sv4 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv4
  frame := (h.frame.trans hf).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim)
  hn := hn

/-- The level-2 trial test (width 1): the kept half's top bit is 0 iff its top word is below `2^63`. -/
theorem zeroOkH1_iff (hi : Bool) (a : HashOutput) :
    zeroOkH hi 1 a = true ↔ (a.extractLsb' (64 * (if hi then 3 else 1)) 64).toNat < 2 ^ 63 := by
  have ha := a.isLt
  cases hi
  · show decide ((a.extractLsb' 0 128).toNat < 2 ^ (128 - 1)) = true ↔ (a.extractLsb' (64 * 1) 64).toNat < 2 ^ 63
    rw [decide_eq_true_iff, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_eq_div_pow]
    constructor <;> intro h <;> omega
  · show decide ((a.extractLsb' 128 128).toNat < 2 ^ (128 - 1)) = true ↔
      (a.extractLsb' (64 * 3) 64).toNat < 2 ^ 63
    rw [decide_eq_true_iff, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_eq_div_pow]
    constructor <;> intro h <;> omega

/-- What follows the trial-`n` hash in `searchH` (fuel = trials left). -/
def sTailH (hi : Bool) (b : Nat) (pre right : List UInt8) : Nat → Nat → HashOutput → M (Nat × HashOutput)
  | 0, n, a => pure (n, a)
  | fuel + 1, n, a => if zeroOkH hi b a then pure (n, a) else searchH hi b pre right fuel (n + 1)

theorem searchH_eq (hi : Bool) (b : Nat) (pre right : List UInt8) (fuel n : Nat) :
    searchH hi b pre right fuel n = publicHash (trialInput pre n right) >>= sTailH hi b pre right fuel n := by
  cases fuel <;> rfl

section run2
variable {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {hi : Bool} {pre mid right : List UInt8}
  {s : MachineState} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
  (hT : CodeAt im (pcOf b) (trampWords b (s2Base hi) ret)) (F : Search2In b ret A D S0 pre mid right s)
include hS hT F

/-- The ground exit `s2Base hi + 24 -> ret`: copy, clear, record at `slot2`, restore; then the trampoline tail. -/
theorem exit_spec2 {n : Nat} {a : HashOutput} {v : MachineState} (hv : AtS2 s b A D (s2Base hi + 24) n v)
    (hh : Hashed v A n a) (hS3 : 3400 ≤ S0) : TBSim im sk v 30 (pure (n, a)) (Search2Out s ret A D S0) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hS1 := F.hS1; have hS2 := F.hS2
  simp only [SCR] at hA2 hD2
  obtain ⟨t1, s1, p1, x12, x14, x17, x29, x31, r1, ans, scr, sl0, sl1, sv, f1⟩ :=
    f_2_spec hS v hv.pc A D S0 (b + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) hv.x14 hv.x12
      (by rw [hv.regs.get (by decide)]; exact F.x8) hv.x16 (by omega) F.hD (by omega) (by simp only [SCR]; omega)
      F.hS0 F.hS1 F.hS2
  obtain ⟨t2, s2, p2, x16, r2, m2, f2⟩ := tramp_tail hT hb hret t1 p1
  have g1136 : t1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f1.get (by decide) (by simp only [SCR, slot2, slotA]; omega), hv.sv4]
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → ¬ (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slot2 S0 ≤ X ∧ X < slot2 S0 + 16) → ¬ (1104 ≤ X ∧ X < 1136) →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  refine tb_pure_steps (s1.trans s2) ?_
  exact {
    pc := p2
    regs := by
      intro r _
      by_cases h16 : r = .x16
      · subst h16; rw [x16, g1136]
      rw [r2.get (by simpa using h16)]
      by_cases hr : r ∈ [Reg.x12, .x14, .x17, .x29, .x31]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [x12, F.x12]
        · rw [x14, hv.sv0]
        · rw [x17, hv.sv1]
        · rw [x29, hv.sv2]
        · rw [x31, hv.sv3]
      · have hr' : r ∉ loopRegs2 := by
          simp only [loopRegs2, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
        rw [r1.get hr, hv.regs.get hr']
    ans := fun k hk => by rw [t2m _ (by omega) (by omega), ans k hk, hh.scr k hk]
    nle := hv.hn
    pad32 := fun _ h => by
      rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR]; omega)
        (by simp only [slot2, slotA, SCR]; omega) (by omega), hh.p32]
    pad40 := fun _ h => by
      rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR]; omega)
        (by simp only [slot2, slotA, SCR]; omega) (by omega), hh.p40]
    rec0 := fun _ => by
      rw [t2m _ (by simp only [slot2, slotA, SCR]; omega) (by simp only [slot2, slotA, SCR]; omega), sl0]
    rec1 := fun _ => by
      rw [t2m _ (by simp only [slot2, slotA, SCR]; omega) (by simp only [slot2, slotA, SCR]; omega), sl1, hv.x17]
    scr := fun _ k hk => by rw [t2m _ (by simp only [SCR]; omega) (by simp only [SCR]; omega), scr k hk]
    saves := fun k hk => by
      rw [if_pos (Or.inl hS3)]
      by_cases h4 : k = 4
      · subst h4; exact m2
      · rw [t2m _ (by omega) (by omega), sv k (by omega)]
    plain := fun h => absurd hS3 (by omega)
    frame := ((hv.frame.trans f1).trans f2).mono (fun X _ h => by
      unfold SearchW2
      unfold LoopW at h
      rcases h with ((h | h | h | h) | (h | h | h | h)) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))) }

/-- One level-2 trial: pad `n ‖ 0`, then the hash of the trial block into `SCR`. -/
theorem trial_spec2 {β : Type} {n : Nat} {u : MachineState} (hu : AtS2 s b A D (s2Base hi + 14) n u) {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtS2 s b A D (s2Base hi + 17) n w → Hashed w A n a → TBSim im sk w W (f a) Q) :
    TBSim im sk u (2 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2
  simp only [SCR] at hA2
  have hnF : n < 2 ^ 64 := by
    have h1 := hu.hn
    have : FUEL 1 = 255 := rfl
    omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, m40, f1, fe1⟩ := l_2_spec hS u hu.pc A g10 hA (by omega)
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (LoopW A) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have g1 : ∀ x, x ∉ loopRegs2 → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 SCR := by rw [r1.get (by simp)]; exact hu.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + (2 + 2) from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i _ => by unfold LoopW; simp only [SCR]; omega),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i _ => by unfold LoopW; simp only [SCR]; omega),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        SphincsSecurity.bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
    simp
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 SCR (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) (by omega) (by decide) (by decide)
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a SCR h12 (by decide)
  have fw : Frame s (writeHash u1 a) (LoopW A) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr h)))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ A + 40 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 =>
    f1.get hX (by rintro (h | h) <;> contradiction)
  refine h a (writeHash u1 a)
    { pc := by rw [pc_writeHash, p1, pcOf_add4]
      regs := fun x hx => by rw [getReg_writeHash, g1 x hx]
      x12 := by rw [getReg_writeHash]; exact h12
      x14 := by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x14
      x16 := by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16
      x17 := by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17
      sv0 := by
        rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv0
      sv1 := by
        rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv1
      sv2 := by
        rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv2
      sv3 := by
        rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv3
      sv4 := by
        rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv4
      frame := fw
      hn := hu.hn }
    ⟨fun k hk => ?_, by rw [keep _ (by omega) (by simp only [SCR]; omega)]; exact m32,
      by rw [keep _ (by omega) (by simp only [SCR]; omega)]; exact m40⟩
  rw [getMem_writeHash u1 a SCR _ h12 (by decide) (by simp only [SCR]; omega)]
  interval_cases k <;> simp

/-- The level-2 search loop from `s2Base hi + 14` with nonce `n` and `fuel` trials after this one. -/
theorem loop_spec2 (hS3 : 3400 ≤ S0) : ∀ fuel n u, AtS2 s b A D (s2Base hi + 14) n u → n + fuel = FUEL 1 →
    TBSim im sk u (17 * fuel + 45) (searchH hi 1 pre right fuel n) (Search2Out s ret A D S0) := by
  have hF : FUEL 1 = 255 := rfl
  have hA2 := F.hA2
  simp only [SCR] at hA2
  -- the zero test at `+ 17`
  have test : ∀ n a w, AtS2 s b A D (s2Base hi + 17) n w → Hashed w A n a → ∃ w1, Steps im w 3 3 w1 ∧
      AtS2 s b A D (if zeroOkH hi 1 a = true then s2Base hi + 24 else s2Base hi + 20) n w1 ∧ Hashed w1 A n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := c_2_spec hS w hw.pc hw.x12
    have e : (w.getMem (BitVec.ofNat 64 (SCR + 8 * (if hi then 3 else 1)))).toNat < 2 ^ 63 ↔
        zeroOkH hi 1 a = true := by
      rw [zeroOkH1_iff, hh.scr _ (by split <;> omega)]
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move f1 (by omega)⟩
    rw [p1]; by_cases hz : zeroOkH hi 1 a = true
    · rw [if_pos (e.mpr hz), if_pos hz]
    · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
  -- the cap test at `+ 20`
  have capT : ∀ n a w, AtS2 s b A D (s2Base hi + 20) n w → Hashed w A n a → ∃ w1, Steps im w 2 2 w1 ∧
      AtS2 s b A D (if n = 255 then s2Base hi + 24 else s2Base hi + 22) n w1 ∧ Hashed w1 A n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := n_2_spec hS w hw.pc
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move f1 (by omega)⟩
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    rw [p1, hw.x17]
    by_cases hz : n = 255
    · rw [if_pos (by rw [hz]), if_pos hz]
    · rw [if_neg (fun h => hz ((ofNat_inj hnl (by norm_num)).mp h)), if_neg hz]
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    rw [hF] at hn
    simp only [Nat.add_zero] at hn
    rw [searchH_eq]
    refine (trial_spec2 hS hT F hu (W := 35) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOkH hi 1 a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (exit_spec2 hS hT F hw1 hh1 hS3)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_pos hn] at hw2
      exact TBSim.steps s1 (TBSim.steps s2 (exit_spec2 hS hT F hw2 hh2 hS3))
  | succ fuel ih =>
    intro n u hu hn
    rw [hF] at hn
    rw [searchH_eq]
    refine (trial_spec2 hS hT F hu (W := 17 * fuel + 52) (fun a w hw hh => ?_)).mono (by omega)
      (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOkH hi 1 a = true
    · rw [if_pos hz] at hw1
      simp only [sTailH, hz, if_true]
      exact (TBSim.steps s1 (exit_spec2 hS hT F hw1 hh1 hS3)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      simp only [sTailH, hz, Bool.false_eq_true, if_false]
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_neg (by omega)] at hw2
      obtain ⟨w3, s3, p3, x17, r3, f3⟩ := j_2_spec hS w2 hw2.pc
      have hw3 : AtS2 s b A D (s2Base hi + 14) (n + 1) w3 := hw2.move p3 (r3.mono (by decide)) f3
        (by rw [x17, hw2.x17, ofNat_add_ofNat]) (by rw [hF]; omega)
      have := TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (ih (n + 1) w3 hw3 (by rw [hF]; omega))))
      exact this.mono (by omega) (fun _ _ h => h)

end run2

end p4t

/-- E9, ground path (`3400 ≤ S0`). -/
theorem tramp_search2_ground {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {hi : Bool} {pre mid right : List UInt8}
    {s : MachineState} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
    (hT : CodeAt im (pcOf b) (trampWords b (s2Base hi) ret)) (F : Search2In b ret A D S0 pre mid right s) (hS3 : 3400 ≤ S0) :
    TBSim im sk s W_SEARCH2 (searchH hi 1 pre right (FUEL 1) 0) (Search2Out s ret A D S0) := by
  have hS2 := F.hS2
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by cases hi <;> decide) s F.pc
  obtain ⟨u1, s1, p1, r1, x29, m1120, f1⟩ :=
    s2_entry_spec hS u0 p0 S0 (by rw [r0.get (by decide)]; exact F.x8) hS2
  rw [if_pos hS3] at p1
  obtain ⟨u2, s2, p2, x12, x14, x17, r2, sv0, sv1, sv3, f2⟩ := h0_2_spec hS u1 p1
  have hu2 : AtS2 s b A D (s2Base hi + 14) 0 u2 :=
    { pc := p2
      regs := ((r0.trans r1).trans r2).mono (by decide)
      x12 := x12
      x14 := by rw [x14, r1.get (by decide), r0.get (by decide)]; exact F.x12
      x16 := by rw [r2.get (by decide), r1.get (by decide)]; exact x16
      x17 := by rw [x17]; rfl
      sv0 := by rw [sv0, r1.get (by decide), r0.get (by decide)]
      sv1 := by rw [sv1, r1.get (by decide), r0.get (by decide)]
      sv2 := by rw [f2.get (by decide) (by omega), m1120, r0.get (by decide)]
      sv3 := by rw [sv3, r1.get (by decide), r0.get (by decide)]
      sv4 := by rw [f2.get (by decide) (by omega), f1.get (by decide) (by omega)]; exact m0
      frame := ((f0.trans f1).trans f2).mono (fun X _ h => by
        unfold LoopW; exact Or.inr (Or.inr (Or.inl (by omega))))
      hn := Nat.zero_le _ }
  have := TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2
    (loop_spec2 (sk := sk) hS hT F hS3 (FUEL 1) 0 u2 hu2 (by omega))))
  refine this.mono ?_ (fun _ _ h => h)
  unfold W_SEARCH2; generalize FUEL 1 = m; omega

/-- E9, plain path (`S0 < 3400`, coordinate 8). -/
theorem tramp_search2_plain {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {hi : Bool} {pre mid right : List UInt8}
    {s : MachineState} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
    (hT : CodeAt im (pcOf b) (trampWords b (s2Base hi) ret)) (F : Search2In b ret A D S0 pre mid right s) (hS3 : ¬ 3400 ≤ S0) :
    TBSim im sk s W_SEARCH2 ((fun a => (0, a)) <$> publicHash (pre ++ mid ++ right)) (Search2Out s ret A D S0) := by
  have hS2 := F.hS2
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by cases hi <;> decide) s F.pc
  obtain ⟨u1, s1, p1, r1, x29, m1120, f1⟩ :=
    s2_entry_spec hS u0 p0 S0 (by rw [r0.get (by decide)]; exact F.x8) hS2
  rw [if_neg hS3] at p1
  obtain ⟨u2, s2, p2, fe2, r2, x29', m1120', f2⟩ := s2_plain_spec hS u1 p1
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hD := F.hD; have hD1 := F.hD1
  have hD2 := F.hD2; have hb := F.hb; have hret := F.hret
  simp only [SCR] at hA2 hD2
  have rr := (r0.trans r1).trans r2
  have h10 : u2.getReg .x10 = BitVec.ofNat 64 A := by rw [rr.get (by decide)]; exact F.x10
  have h11 : u2.getReg .x11 = BitVec.ofNat 64 64 := by rw [rr.get (by decide)]; exact F.x11
  have h12 : u2.getReg .x12 = BitVec.ofNat 64 D := by rw [rr.get (by decide)]; exact F.x12
  have h5 : u2.getReg .x5 = 0 := by rw [rr.get (by decide)]; exact F.x5
  have h16 : u2.getReg .x16 = pcOf (b + 2) := by rw [r2.get (by decide), r1.get (by decide)]; exact x16
  have fs2 : Frame s u2 (fun X => X = 1136 ∨ X = 1120) :=
    ((f0.trans f1).trans f2).mono (fun X _ h => by omega)
  have hl : (pre ++ mid ++ right).length = 64 := by simp [F.lpre, F.lmid, F.lright]
  have hq : hashInput u2 = toQ (pad64 (pre ++ mid ++ right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u2 _ 0 A hl h10 hA (by omega) h11 (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + (2 + 2) from rfl, readWords_add, readWords_add,
      frame_readWordsG fs2 A 4 (by omega) (fun i _ => by omega),
      frame_readWordsG fs2 (A + 8 * 4) 2 (by omega) (fun i _ => by omega),
      frame_readWordsG fs2 (A + 8 * 4 + 8 * 2) 2 (by omega) (fun i _ => by omega),
      F.mpre, show A + 8 * 4 = A + 32 by ring, F.mmid, show A + 32 + 8 * 2 = A + 48 by ring, F.mright,
      wordsOf_append (pre ++ mid) right (by simp [F.lpre, F.lmid]), wordsOf_append pre mid (by rw [F.lpre]),
      List.append_assoc]
  have hblk : (toQ (pad64 (pre ++ mid ++ right))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; omega, by rw [hl]⟩, hl]
  have hv : hashArgumentsValid u2 = true :=
    hashArgs_const u2 A 64 D h10 h11 h12 hA (by norm_num) (by omega) hD (by omega)
  rw [map_eq_bind_pure_comp]
  have e := tb_pub (sk := sk) (W := 4) (f := pure ∘ fun a => (0, a)) (Q := Search2Out s ret A D S0) fe2 h5 hv hq
    (fun a => ?_)
  · have := TBSim.steps s0 (TBSim.steps s1 (TBSim.steps s2 e))
    rw [hblk] at this
    exact this.mono (by unfold W_SEARCH2; omega) (fun _ _ h => h)
  have hwf : Frame u2 (writeHash u2 a) (fun X => X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) :=
    fun X hX hn => by
      rw [getMem_writeHash u2 a D X h12 (by omega) hX, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
  obtain ⟨u4, s4, p4, r4, f4⟩ := p_2_spec hS (writeHash u2 a) (by rw [pc_writeHash, p2, pcOf_add4]) (b + 2)
    (by rw [getReg_writeHash]; exact h16)
  obtain ⟨u5, s5, p5, x16', r5, m5, f5⟩ := tramp_tail hT hb hret u4 p4
  have pf : Frame s u5 (fun X => X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24 ∨ X = 1120 ∨ X = 1136) :=
    ((((fs2.trans hwf).trans f4).trans f5)).mono (fun X _ h => by simp only [or_false] at h; omega)
  have g1136 : u4.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f4.get (by decide) (fun h => h), hwf.get (by decide) (by omega), f2.get (by decide) (by omega),
      f1.get (by decide) (by omega), m0]
  refine tb_pure_steps (s4.trans s5)
    { pc := p5
      regs := fun r _ => ?_
      ans := fun k hk => ?_
      nle := Nat.zero_le _
      pad32 := fun h => absurd h hS3
      pad40 := fun h => absurd h hS3
      rec0 := fun h => absurd h hS3
      rec1 := fun h => absurd h hS3
      scr := fun h => absurd h hS3
      saves := fun k hk => ?_
      plain := fun _ => ⟨rfl, pf⟩
      frame := pf.mono (fun X _ h => by unfold SearchW2; omega) }
  · by_cases h16r : r = .x16
    · subst h16r; rw [x16', g1136]
    rw [r5.get (by simpa using h16r), r4.get (by simp), getReg_writeHash]
    by_cases h29 : r = .x29
    · subst h29; rw [x29', m1120, r0.get (by decide)]
    rw [r2.get (by simpa using h29), r1.get (by simpa using h29), r0.get (by simpa using h16r)]
  · rw [f5.get (by omega) (by omega), f4.get (by omega) (fun h => h),
      getMem_writeHash u2 a D _ h12 (by omega) (by omega)]
    interval_cases k <;> simp
  · by_cases h4 : k = 4
    · subst h4; rw [if_pos (Or.inr (Or.inr rfl))]; exact m5
    by_cases h2 : k = 2
    · subst h2
      rw [if_pos (Or.inr (Or.inl rfl)), f5.get (by decide) (by decide), f4.get (by decide) (fun h => h),
        hwf.get (by decide) (by omega), m1120']
    rw [if_neg (by omega), pf.get (by omega) (by omega)]

/-- **E9/E12: a level-2 trampoline round trip refines `node2`** (the level-2 twin of `tramp_search`; review2 F10 /
stubs F16-TS16). -/
theorem tramp_search2 {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {hi : Bool} {pre mid right : List UInt8}
    {s : MachineState} (hS : CodeAt im (pcOf (s2Base hi)) (search2Words hi))
    (hT : CodeAt im (pcOf b) (trampWords b (s2Base hi) ret)) (F : Search2In b ret A D S0 pre mid right s) :
    TBSim im sk s W_SEARCH2 (node2 hi S0 pre mid right) (Search2Out s ret A D S0) := by
  unfold node2
  by_cases hS3 : 3400 ≤ S0
  · rw [if_pos hS3, groundFoldH]; exact tramp_search2_ground hS hT F hS3
  · rw [if_neg hS3]; exact tramp_search2_plain hS hT F hS3

/-! ## E10: `copy2`, the level-2 record pass, and the halt -/

/-- Memory after `copy2`: for `k = 0..8`, if the level-2 record address at `slot2 (sB k)` is nonzero, store the
recorded nonce there (`k = 0` first; reads from the entry memory, the records lying above every target). -/
def copy2Mem (M : Word → Word) : Word → Word :=
  (List.range 9).foldl (fun N k =>
    if M (BitVec.ofNat 64 (slot2 (sB k))) = 0 then N
    else upd N (M (BitVec.ofNat 64 (slot2 (sB k)))) (M (BitVec.ofNat 64 (slot2 (sB k) + 8)))) M

/-- Steps of `copy2` to its `ecall`: 2, then 3 per record (5 when it is written). -/
def copy2Steps (M : Word → Word) : Nat :=
  2 + ((List.range 9).map fun k => if M (BitVec.ofNat 64 (slot2 (sB k))) = 0 then 3 else 5).sum

theorem copy2Steps_le (M : Word → Word) : copy2Steps M ≤ 47 := by
  unfold copy2Steps
  have h : ∀ x ∈ (List.range 9).map fun k =>
      if M (BitVec.ofNat 64 (slot2 (sB k))) = 0 then 3 else 5, x ≤ 5 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, _, rfl⟩ := hx
    split_ifs <;> omega
  have := List.sum_le_card_nsmul _ 5 h
  simp only [List.length_map, List.length_range, smul_eq_mul] at this
  omega

/-! ## E10 (continued): `copy2_run` -/

/-- Window of `copy2Words` (generic in the supplied `CodeAt` fact, not fixed to `Images.expandImage`). -/
def c2w (a b : Nat) : List (BitVec 32) := (copy2Words.drop (a - COPY2)).take (b - a)

theorem code_c2w {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (a b : Nat) (ha : COPY2 ≤ a)
    (hb : b ≤ COPY2 + 48) (hab : a ≤ b) : CodeAt im (pcOf a) (c2w a b) := by
  have hlen : copy2Words.length = 48 := fts16_shape.2.2.2.2.2.2.2.2.1
  have := codeAt_sub (a - COPY2) hc (seg := c2w a b) (by simp [c2w, hlen]; omega) (by simp [c2w])
  rwa [show COPY2 + (a - COPY2) = a by omega] at this

/-- The repeating 5-word iteration block (`ld t4,0(t6); beq t4,zero,+12; ld t5,8(t6); sd t5,0(t4);
addi t6,t6,-1696`) at word `COPY2 + 2 + 5k`, for each `k < 9`. -/
theorem copy2_iter_words (k : Nat) (hk : k < 9) :
    c2w (COPY2 + 2 + 5 * k) (COPY2 + 2 + 5 * k + 5) =
      [0xfbe83, 0xe8663, 0x8fbf03, 0x1eeb023, 0x960f8f93] := by
  interval_cases k <;> decide +kernel

theorem copy2_iter_code {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (k : Nat) (hk : k < 9) :
    CodeAt im (pcOf (COPY2 + 2 + 5 * k)) [0xfbe83] ∧
    CodeAt im (pcOf (COPY2 + 2 + 5 * k + 1)) [0xe8663] ∧
    CodeAt im (pcOf (COPY2 + 2 + 5 * k + 2)) [0x8fbf03] ∧
    CodeAt im (pcOf (COPY2 + 2 + 5 * k + 3)) [0x1eeb023] ∧
    CodeAt im (pcOf (COPY2 + 2 + 5 * k + 4)) [0x960f8f93] := by
  have h5 := code_c2w hc (COPY2 + 2 + 5 * k) (COPY2 + 2 + 5 * k + 5) (by omega) (by omega) (by omega)
  rw [copy2_iter_words k hk] at h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using codeAt_sub 0 h5 (seg := [0xfbe83]) (by simp) rfl
  · have := codeAt_sub 1 h5 (seg := [0xe8663]) (by simp) rfl
    simpa using this
  · have := codeAt_sub 2 h5 (seg := [0x8fbf03]) (by simp) rfl
    simpa using this
  · have := codeAt_sub 3 h5 (seg := [0x1eeb023]) (by simp) rfl
    simpa using this
  · have := codeAt_sub 4 h5 (seg := [0x960f8f93]) (by simp) rfl
    simpa using this

theorem copy2_iter_ecall_code {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) :
    CodeAt im (pcOf HALT2) [0x73] := by
  have hd : copy2Words.drop 47 = [0x73] := by decide +kernel
  have hlen : copy2Words.length = 48 := fts16_shape.2.2.2.2.2.2.2.2.1
  have h := codeAt_sub 47 hc (seg := [0x73]) (by simp [hlen]) (by rw [hd]; rfl)
  simpa [show COPY2 + 47 = HALT2 from by unfold COPY2 HALT2; omega] using h

theorem sext12_zero : signExtend12 (0 : BitVec 12) = 0 := by decide
theorem sext12_eight : signExtend12 (8 : BitVec 12) = 8 := by decide
theorem sext13_twelve : signExtend13 (12 : BitVec 13) = 12 := by decide

theorem sext12_decr (a : Nat) (ha : 1696 ≤ a) (ha2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a + signExtend12 (0x960 : BitVec 12) = BitVec.ofNat 64 (a - 1696) := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (0x960 : BitVec 12)).toNat = 2 ^ 64 - 1696 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha2, hs, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a - 1696 < 2 ^ 64 by omega)]
  omega

theorem getMem_setMem (s : MachineState) (a v A : Word) :
    (s.setMem a v).getMem A = if A = a then v else s.getMem A := by
  simp [MachineState.setMem, MachineState.getMem]

set_option maxRecDepth 2000 in
/-- One `copy2` loop iteration: from `COPY2 + 2 + 5k` with `t6 = slot2 (sB k)`, run the 5-word block,
advance `t6` by `-1696` and (if the recorded address is nonzero) store the recorded nonce. -/
theorem copy2_iter {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (k : Nat) (hk : k < 9)
    (s : MachineState) (hpc : s.pc = pcOf (COPY2 + 2 + 5 * k))
    (ht6 : s.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)))
    (hb : s.getMem (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 →
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat + 8 ≤ SCR) :
    ∃ t, Steps im s (if s.getMem (BitVec.ofNat 64 (slot2 (sB k))) = 0 then 3 else 5)
                     (if s.getMem (BitVec.ofNat 64 (slot2 (sB k))) = 0 then 3 else 5) t ∧
      t.pc = pcOf (COPY2 + 2 + 5 * (k + 1)) ∧
      t.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k) - 1696) ∧
      RegsExcept s t [.x29, .x30, .x31] ∧
      (∀ A, t.getMem A =
        if s.getMem (BitVec.ofNat 64 (slot2 (sB k))) = 0 then s.getMem A
        else upd s.getMem (s.getMem (BitVec.ofNat 64 (slot2 (sB k))))
          (s.getMem (BitVec.ofNat 64 (slot2 (sB k) + 8))) A) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := copy2_iter_code hc k hk
  have hslt : slot2 (sB k) < 2 ^ 64 := by unfold slot2 slotA SCR sB; omega
  have hmod8 : slot2 (sB k) % 8 = 0 := by unfold slot2 slotA SCR sB; omega
  have hle : slot2 (sB k) + 16 ≤ MEMORY_BYTES := by unfold slot2 slotA SCR MEMORY_BYTES sB; omega
  have hav0 : accessValid (BitVec.ofNat 64 (slot2 (sB k))) 8 = true := by
    rw [memAccessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslt]
    exact ⟨by omega, hmod8⟩
  have e0 : s.getReg .x31 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (slot2 (sB k)) := by
    rw [sext12_zero, add_zero, ht6]
  have step1 : Steps im s 1 1
      ((s.setReg .x29 (s.getMem (BitVec.ofNat 64 (slot2 (sB k))))).setPC (pcOf (COPY2 + 2 + 5 * k + 1))) :=
    micro_step (i := .base (.LD .x29 .x31 0)) (m := .load .d .x29 .x31 (signExtend12 0)) c0 rfl rfl hpc
      (by simp only [Micro.exec, e0, hav0, LoadKind.width, if_true, LoadKind.read, hpc, pcOf_add4])
  set s1 := (s.setReg .x29 (s.getMem (BitVec.ofNat 64 (slot2 (sB k))))).setPC (pcOf (COPY2 + 2 + 5 * k + 1))
    with hs1def
  have hx29_s1 : s1.getReg .x29 = s.getMem (BitVec.ofNat 64 (slot2 (sB k))) := by
    rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x29 : Reg) ≠ .x0)]
  have hx0_s1 : s1.getReg .x0 = (0 : Word) := by
    rw [hs1def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x0)]
    rfl
  have hx31_s1 : s1.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) := by
    rw [hs1def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x31)]
    exact ht6
  have hmem_s1 : ∀ A, s1.getMem A = s.getMem A := by
    intro A; rw [hs1def, MachineState.getMem_setPC, MachineState.getMem_setReg]
  have hpc_s1 : s1.pc = pcOf (COPY2 + 2 + 5 * k + 1) := rfl
  -- the branch-independent `addi t6, t6, -1696` tail, from any state `u` agreeing with `s` on
  -- memory and with `u.getReg .x31 = slot2 (sB k)`.
  have addi_step : ∀ (u : MachineState) (P : Nat), CodeAt im (pcOf P) [0x960f8f93] →
      u.pc = pcOf P → u.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) →
      ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (P + 1) ∧
        v.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k) - 1696) ∧ RegsExcept u v [.x31] ∧
        (∀ A, v.getMem A = u.getMem A) := by
    intro u P cP hup hu31
    have e : u.getReg .x31 + signExtend12 (0x960 : BitVec 12) = BitVec.ofNat 64 (slot2 (sB k) - 1696) := by
      rw [hu31]
      exact sext12_decr (slot2 (sB k)) (by unfold slot2 slotA SCR sB; omega) hslt
    refine ⟨(u.setReg .x31 (u.getReg .x31 + signExtend12 (0x960 : BitVec 12))).setPC (pcOf (P + 1)),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact micro_step (i := .base (.ADDI .x31 .x31 0x960))
        (m := .alu .x31 .add (.reg .x31) (.imm (signExtend12 0x960))) cP rfl rfl hup
        (by simp only [Micro.exec, BinOp.eval, Src.eval, hup, pcOf_add4])
    · rfl
    · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x31 : Reg) ≠ .x0), e]
    · intro r hr
      simp only [List.mem_singleton] at hr
      rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
    · intro A; rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
  by_cases hz : s.getMem (BitVec.ofNat 64 (slot2 (sB k))) = 0
  · -- the beq is taken: ld, beq, addi (3 steps), memory unchanged.
    have step2 : Steps im s1 1 1 (s1.setPC (pcOf (COPY2 + 2 + 5 * k + 1) + signExtend13 12)) :=
      micro_step (i := .base (.BEQ .x29 .x0 12)) (m := .branch .eq .x29 .x0 (signExtend13 12)) c1 rfl rfl hpc_s1
        (by simp only [Micro.exec, CmpOp.eval, hx29_s1, hx0_s1, hz, beq_self_eq_true, if_true, hpc_s1])
    set s2 := s1.setPC (pcOf (COPY2 + 2 + 5 * k + 1) + signExtend13 12) with hs2def
    have hpc_s2 : s2.pc = pcOf (COPY2 + 2 + 5 * k + 4) := by
      rw [hs2def]
      show pcOf (COPY2 + 2 + 5 * k + 1) + signExtend13 12 = pcOf (COPY2 + 2 + 5 * k + 4)
      rw [sext13_twelve, show (12 : Word) = BitVec.ofNat 64 (4 * 3) from by decide, pcOf_add_w]
    have hx31_s2 : s2.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) := by
      rw [hs2def, MachineState.getReg_setPC]; exact hx31_s1
    have hmem_s2 : ∀ A, s2.getMem A = s.getMem A := by
      intro A; rw [hs2def, MachineState.getMem_setPC]; exact hmem_s1 A
    obtain ⟨t, step3, hpt, hxt, hrt, hmt⟩ := addi_step s2 (COPY2 + 2 + 5 * k + 4) c4 hpc_s2 hx31_s2
    refine ⟨t, ?_, by rw [hpt]; ring_nf, hxt, ?_, ?_⟩
    · rw [if_pos hz]
      have := step1.trans (step2.trans step3)
      simpa using this
    · intro r hr
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨hr29, _, hr31⟩ := hr
      have e1 : t.getReg r = s2.getReg r := hrt r (by simp [hr31])
      have e2 : s2.getReg r = s1.getReg r := by rw [hs2def, MachineState.getReg_setPC]
      have e3 : s1.getReg r = s.getReg r := by
        rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr29)]
      simp only [e1, e2, e3]
    · intro A; rw [if_pos hz, hmt A, hmem_s2 A]
  · -- the beq falls through: ld, beq, ld, sd, addi (5 steps); the target gets the recorded nonce.
    have step2 : Steps im s1 1 1 (s1.setPC (pcOf (COPY2 + 2 + 5 * k + 1) + 4)) :=
      micro_step (i := .base (.BEQ .x29 .x0 12)) (m := .branch .eq .x29 .x0 (signExtend13 12)) c1 rfl rfl hpc_s1
        (by simp only [Micro.exec, CmpOp.eval, hx29_s1, hx0_s1, hpc_s1]
            rw [if_neg (by rw [beq_iff_eq]; exact hz)])
    set s2 := s1.setPC (pcOf (COPY2 + 2 + 5 * k + 1) + 4) with hs2def
    have hpc_s2 : s2.pc = pcOf (COPY2 + 2 + 5 * k + 2) := by
      rw [hs2def]
      show pcOf (COPY2 + 2 + 5 * k + 1) + 4 = pcOf (COPY2 + 2 + 5 * k + 2)
      rw [pcOf_add4]
    have hx31_s2 : s2.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) := by
      rw [hs2def, MachineState.getReg_setPC]; exact hx31_s1
    have hmem_s2 : ∀ A, s2.getMem A = s.getMem A := by
      intro A; rw [hs2def, MachineState.getMem_setPC]; exact hmem_s1 A
    have htgtV : s.getMem (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 := hz
    obtain ⟨hmod8', hle'⟩ := hb htgtV
    have htgtlt : (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat < 2 ^ 64 :=
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).isLt
    have e8 : s2.getReg .x31 + signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (slot2 (sB k) + 8) := by
      rw [hx31_s2, sext12_eight, show (8:Word) = BitVec.ofNat 64 8 from by decide, ofNat_add_ofNat]
    have hslt8 : slot2 (sB k) + 8 < 2 ^ 64 := by unfold slot2 slotA SCR sB; omega
    have hmod8_8 : (slot2 (sB k) + 8) % 8 = 0 := by unfold slot2 slotA SCR sB; omega
    have hav8 : accessValid (BitVec.ofNat 64 (slot2 (sB k) + 8)) 8 = true := by
      rw [memAccessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslt8]
      exact ⟨by unfold slot2 slotA SCR MEMORY_BYTES sB; omega, hmod8_8⟩
    have step3 : Steps im s2 1 1
        ((s2.setReg .x30 (s2.getMem (BitVec.ofNat 64 (slot2 (sB k) + 8)))).setPC
          (pcOf (COPY2 + 2 + 5 * k + 3))) :=
      micro_step (i := .base (.LD .x30 .x31 8)) (m := .load .d .x30 .x31 (signExtend12 8)) c2 rfl rfl hpc_s2
        (by simp only [Micro.exec, e8, hav8, LoadKind.width, if_true, LoadKind.read, hpc_s2, pcOf_add4])
    set s3 := (s2.setReg .x30 (s2.getMem (BitVec.ofNat 64 (slot2 (sB k) + 8)))).setPC
      (pcOf (COPY2 + 2 + 5 * k + 3)) with hs3def
    have hx29_s3 : s3.getReg .x29 = s.getMem (BitVec.ofNat 64 (slot2 (sB k))) := by
      rw [hs3def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x30 : Reg) ≠ .x29),
        hs2def, MachineState.getReg_setPC]
      exact hx29_s1
    have hx30_s3 : s3.getReg .x30 = s.getMem (BitVec.ofNat 64 (slot2 (sB k) + 8)) := by
      rw [hs3def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x30 : Reg) ≠ .x0)]
      exact hmem_s2 _
    have hx31_s3 : s3.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) := by
      rw [hs3def, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x30 : Reg) ≠ .x31)]
      exact hx31_s2
    have hpc_s3 : s3.pc = pcOf (COPY2 + 2 + 5 * k + 3) := rfl
    have e0' : s3.getReg .x29 + signExtend12 (0 : BitVec 12) = s.getMem (BitVec.ofNat 64 (slot2 (sB k))) := by
      rw [sext12_zero, add_zero, hx29_s3]
    have hav0' : accessValid (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))) 8 = true := by
      have hSM : SCR ≤ MEMORY_BYTES := by unfold SCR MEMORY_BYTES; omega
      rw [memAccessValid_iff]
      exact ⟨by omega, hmod8'⟩
    have hmem_s3 : ∀ A, s3.getMem A = s.getMem A := by
      intro A; rw [hs3def, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hmem_s2 A
    have step4 : Steps im s3 1 1
        ((s3.setMem (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))) (s3.getReg .x30)).setPC
          (pcOf (COPY2 + 2 + 5 * k + 4))) :=
      micro_step (i := .base (.SD .x29 .x30 0)) (m := .store .d .x29 .x30 (signExtend12 0)) c3 rfl rfl hpc_s3
        (by simp only [Micro.exec, e0', hav0', StoreKind.width, if_true, StoreKind.write, hpc_s3, pcOf_add4])
    set s4 := (s3.setMem (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))) (s3.getReg .x30)).setPC
      (pcOf (COPY2 + 2 + 5 * k + 4)) with hs4def
    have hx31_s4 : s4.getReg .x31 = BitVec.ofNat 64 (slot2 (sB k)) := by
      rw [hs4def, MachineState.getReg_setPC, getReg_setMem']
      exact hx31_s3
    have hpc_s4 : s4.pc = pcOf (COPY2 + 2 + 5 * k + 4) := rfl
    have hmem_s4 : ∀ A, s4.getMem A = upd s.getMem (s.getMem (BitVec.ofNat 64 (slot2 (sB k))))
        (s.getMem (BitVec.ofNat 64 (slot2 (sB k) + 8))) A := by
      intro A
      rw [hs4def, MachineState.getMem_setPC, getMem_setMem]
      unfold upd
      by_cases hA : A = s.getMem (BitVec.ofNat 64 (slot2 (sB k)))
      · rw [if_pos hA, if_pos hA]; exact hx30_s3
      · rw [if_neg hA, if_neg hA]; exact hmem_s3 A
    obtain ⟨t, step5, hpt, hxt, hrt, hmt⟩ := addi_step s4 (COPY2 + 2 + 5 * k + 4) c4 hpc_s4 hx31_s4
    refine ⟨t, ?_, by rw [hpt]; ring_nf, hxt, ?_, ?_⟩
    · rw [if_neg hz]
      have := step1.trans (step2.trans (step3.trans (step4.trans step5)))
      simpa using this
    · intro r hr
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨hr29, hr30, hr31⟩ := hr
      have e1 : t.getReg r = s4.getReg r := hrt r (by simp [hr31])
      have e2 : s4.getReg r = s3.getReg r := by rw [hs4def, MachineState.getReg_setPC, getReg_setMem']
      have e3 : s3.getReg r = s2.getReg r := by
        rw [hs3def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr30)]
      have e4 : s2.getReg r = s1.getReg r := by rw [hs2def, MachineState.getReg_setPC]
      have e5 : s1.getReg r = s.getReg r := by
        rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr29)]
      simp only [e1, e2, e3, e4, e5]
    · intro A; rw [if_neg hz]; exact hmt A ▸ hmem_s4 A

/-! ## E10 (continued): assembling `copy2_run` from `copy2_iter` -/

/-- `copy2Mem`'s fold, after only the first `j` iterations. -/
def copy2MemPartial (M : Word → Word) (j : Nat) : Word → Word :=
  (List.range j).foldl (fun N k =>
    if M (BitVec.ofNat 64 (slot2 (sB k))) = 0 then N
    else upd N (M (BitVec.ofNat 64 (slot2 (sB k)))) (M (BitVec.ofNat 64 (slot2 (sB k) + 8)))) M

theorem copy2MemPartial_zero (M : Word → Word) : copy2MemPartial M 0 = M := rfl

theorem copy2MemPartial_nine (M : Word → Word) : copy2MemPartial M 9 = copy2Mem M := rfl

theorem copy2MemPartial_succ (M : Word → Word) (j : Nat) :
    copy2MemPartial M (j + 1) =
      if M (BitVec.ofNat 64 (slot2 (sB j))) = 0 then copy2MemPartial M j
      else upd (copy2MemPartial M j) (M (BitVec.ofNat 64 (slot2 (sB j)))) (M (BitVec.ofNat 64 (slot2 (sB j) + 8))) := by
  unfold copy2MemPartial
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem slot2_ge_SCR (k : Nat) (hk : k < 9) : SCR ≤ slot2 (sB k) := by
  unfold slot2 slotA SCR sB; omega

/-- No iteration of `copy2Mem`'s fold ever writes at or above `SCR` (every write target is a recorded address,
which `hb` bounds strictly below `SCR`), so the fold leaves any address `≥ SCR` untouched. -/
theorem copy2MemPartial_ge (M : Word → Word)
    (hb : ∀ k < 9, M (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 →
      (M (BitVec.ofNat 64 (slot2 (sB k)))).toNat % 8 = 0 ∧ (M (BitVec.ofNat 64 (slot2 (sB k)))).toNat + 8 ≤ SCR)
    (A : Word) (hA : SCR ≤ A.toNat) : ∀ j ≤ 9, copy2MemPartial M j A = M A := by
  intro j
  induction j with
  | zero => intro _; exact congrFun (copy2MemPartial_zero M) A
  | succ j ih =>
    intro hj
    rw [copy2MemPartial_succ]
    by_cases hz : M (BitVec.ofNat 64 (slot2 (sB j))) = 0
    · rw [if_pos hz]; exact ih (by omega)
    · rw [if_neg hz]
      unfold upd
      rw [if_neg]
      · exact ih (by omega)
      · intro heq
        have hbound := (hb j (by omega) hz).2
        have := congrArg BitVec.toNat heq
        omega

theorem copy2MemPartial_slot2 (M : Word → Word)
    (hb : ∀ k < 9, M (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 →
      (M (BitVec.ofNat 64 (slot2 (sB k)))).toNat % 8 = 0 ∧ (M (BitVec.ofNat 64 (slot2 (sB k)))).toNat + 8 ≤ SCR)
    (j k : Nat) (hj : j ≤ 9) (hk : k < 9) :
    copy2MemPartial M j (BitVec.ofNat 64 (slot2 (sB k))) = M (BitVec.ofNat 64 (slot2 (sB k))) ∧
    copy2MemPartial M j (BitVec.ofNat 64 (slot2 (sB k) + 8)) = M (BitVec.ofNat 64 (slot2 (sB k) + 8)) := by
  have hge := slot2_ge_SCR k hk
  have hlt : slot2 (sB k) < 2 ^ 64 := by unfold slot2 slotA SCR sB; omega
  have hlt8 : slot2 (sB k) + 8 < 2 ^ 64 := by unfold slot2 slotA SCR sB; omega
  refine ⟨copy2MemPartial_ge M hb _ ?_ j hj, copy2MemPartial_ge M hb _ ?_ j hj⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hge
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt8]; omega

theorem luiVal_t6 : luiVal (0x7e5 : BitVec 20) = BitVec.ofNat 64 8278016 := by decide

/-- `COPY2`'s first two words: `lui t6,0x7e5; addi t6,t6,-928`, giving `t6 = slot2 (sB 0)`. -/
theorem copy2Head_code {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) :
    CodeAt im (pcOf COPY2) [0x7e5fb7] ∧ CodeAt im (pcOf (COPY2 + 1)) [0xc60f8f93] := by
  have h5 := code_c2w hc COPY2 (COPY2 + 2) (by omega) (by omega) (by omega)
  have hd : c2w COPY2 (COPY2 + 2) = [0x7e5fb7, 0xc60f8f93] := by decide +kernel
  rw [hd] at h5
  exact ⟨by simpa using codeAt_sub 0 h5 (seg := [0x7e5fb7]) (by simp) rfl,
    by simpa using codeAt_sub 1 h5 (seg := [0xc60f8f93]) (by simp) rfl⟩

theorem copy2Head_step {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (s : MachineState)
    (hpc : s.pc = pcOf COPY2) :
    ∃ u, Steps im s 2 2 u ∧ u.pc = pcOf (COPY2 + 2) ∧ u.getReg .x31 = BitVec.ofNat 64 (slot2 (sB 0)) ∧
      RegsExcept s u [.x31] ∧ (∀ A, u.getMem A = s.getMem A) := by
  obtain ⟨c0, c1⟩ := copy2Head_code hc
  have step1 : Steps im s 1 1 ((s.setReg .x31 (luiVal (0x7e5 : BitVec 20))).setPC (pcOf (COPY2 + 1))) :=
    micro_step (i := .base (.LUI .x31 (0x7e5 : BitVec 20)))
      (m := .alu .x31 .add (.imm (luiVal (0x7e5 : BitVec 20))) (.imm 0)) c0 rfl rfl hpc
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc, pcOf_add4, add_zero])
  set s1 := (s.setReg .x31 (luiVal (0x7e5 : BitVec 20))).setPC (pcOf (COPY2 + 1)) with hs1def
  have hx31_s1 : s1.getReg .x31 = luiVal (0x7e5 : BitVec 20) := by
    rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x31 : Reg) ≠ .x0)]
  have hpc_s1 : s1.pc = pcOf (COPY2 + 1) := rfl
  have hmem_s1 : ∀ A, s1.getMem A = s.getMem A := by
    intro A; rw [hs1def, MachineState.getMem_setPC, MachineState.getMem_setReg]
  have e : s1.getReg .x31 + signExtend12 (0xC60 : BitVec 12) = BitVec.ofNat 64 (slot2 (sB 0)) := by
    rw [hx31_s1, luiVal_t6, show slot2 (sB 0) = 8277088 from by unfold slot2 slotA SCR sB; norm_num]
    decide
  have step2 : Steps im s1 1 1
      ((s1.setReg .x31 (s1.getReg .x31 + signExtend12 (0xC60 : BitVec 12))).setPC (pcOf (COPY2 + 2))) :=
    micro_step (i := .base (.ADDI .x31 .x31 (0xC60 : BitVec 12)))
      (m := .alu .x31 .add (.reg .x31) (.imm (signExtend12 (0xC60 : BitVec 12)))) c1 rfl rfl hpc_s1
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc_s1, pcOf_add4])
  refine ⟨_, step1.trans step2, rfl, by rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq
    (by decide : (Reg.x31 : Reg) ≠ .x0)]; exact e, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs1def,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A
    rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hmem_s1 A

/-- Sum of `stepCost` over the `rem` iterations starting at `n` (matches `copy2Steps`'s own fold order, right
to left over `List.range`'s length, by `copy2RemSteps_nine_eq`). -/
def copy2RemSteps (M : Word → Word) (n : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => (if M (BitVec.ofNat 64 (slot2 (sB n))) = 0 then 3 else 5) + copy2RemSteps M (n + 1) rem

theorem copy2RemSteps_zero (M : Word → Word) (n : Nat) : copy2RemSteps M n 0 = 0 := rfl

theorem copy2RemSteps_succ (M : Word → Word) (n rem : Nat) :
    copy2RemSteps M n (rem + 1) =
      (if M (BitVec.ofNat 64 (slot2 (sB n))) = 0 then 3 else 5) + copy2RemSteps M (n + 1) rem := rfl

theorem copy2RemSteps_nine_eq (M : Word → Word) : 2 + copy2RemSteps M 0 9 = copy2Steps M := by
  simp only [copy2RemSteps, copy2Steps, List.range_succ, List.range_zero, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  ring

/-- The 9-iteration loop, by induction on the remaining count `rem` (`n + rem = 9`): from `COPY2 + 2 + 5 n`
with `t6 = slot2 (sB n)` and memory `copy2MemPartial s.getMem n`, `copy2` reaches `HALT2` with memory `copy2Mem
s.getMem`, in exactly `copy2RemSteps s.getMem n rem` steps. -/
theorem copy2_run_aux {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (s : MachineState)
    (hb : ∀ k < 9, s.getMem (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 →
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat + 8 ≤ SCR) :
    ∀ rem n, n + rem = 9 → ∀ u : MachineState, RegsExcept s u [.x29, .x30, .x31] →
      u.pc = pcOf (COPY2 + 2 + 5 * n) → (∀ A, u.getMem A = copy2MemPartial s.getMem n A) →
      (rem > 0 → u.getReg .x31 = BitVec.ofNat 64 (slot2 (sB n))) →
      ∃ t : MachineState, Steps im u (copy2RemSteps s.getMem n rem) (copy2RemSteps s.getMem n rem) t ∧
        t.pc = pcOf HALT2 ∧ RegsExcept u t [.x29, .x30, .x31] ∧ (∀ A, t.getMem A = copy2Mem s.getMem A) := by
  intro rem
  induction rem with
  | zero =>
    intro n hn u hreg hpc hmem _
    have hn9 : n = 9 := by omega
    subst hn9
    refine ⟨u, by rw [copy2RemSteps_zero]; exact Steps.refl u, ?_, RegsExcept.refl u _,
      fun A => by rw [hmem A, copy2MemPartial_nine]⟩
    rw [hpc]; congr 1 <;> omega
  | succ r ih =>
    intro n hn u hreg hpc hmem hx31
    have hn9 : n < 9 := by omega
    have hx31' := hx31 (by omega)
    have hmem_k : u.getMem (BitVec.ofNat 64 (slot2 (sB n))) = s.getMem (BitVec.ofNat 64 (slot2 (sB n))) := by
      rw [hmem]; exact (copy2MemPartial_slot2 s.getMem hb n n (by omega) hn9).1
    have hmem_k8 : u.getMem (BitVec.ofNat 64 (slot2 (sB n) + 8)) = s.getMem (BitVec.ofNat 64 (slot2 (sB n) + 8)) := by
      rw [hmem]; exact (copy2MemPartial_slot2 s.getMem hb n n (by omega) hn9).2
    have hb' : u.getMem (BitVec.ofNat 64 (slot2 (sB n))) ≠ 0 →
        (u.getMem (BitVec.ofNat 64 (slot2 (sB n)))).toNat % 8 = 0 ∧
        (u.getMem (BitVec.ofNat 64 (slot2 (sB n)))).toNat + 8 ≤ SCR := by
      rw [hmem_k]; exact hb n hn9
    obtain ⟨t', step', hpt', hxt', hrt', hmt'⟩ := copy2_iter hc n hn9 u hpc hx31' hb'
    simp only [hmem_k] at step'
    have hmem_t' : ∀ A, t'.getMem A = copy2MemPartial s.getMem (n + 1) A := by
      intro A
      rw [hmt' A, copy2MemPartial_succ]
      simp only [hmem_k, hmem_k8]
      by_cases hz : s.getMem (BitVec.ofNat 64 (slot2 (sB n))) = 0
      · rw [if_pos hz, if_pos hz, hmem A]
      · rw [if_neg hz, if_neg hz]
        unfold upd
        by_cases hA : A = s.getMem (BitVec.ofNat 64 (slot2 (sB n)))
        · rw [if_pos hA, if_pos hA]
        · rw [if_neg hA, if_neg hA, hmem A]
    have hreg' : RegsExcept s t' [.x29, .x30, .x31] := by
      have htr : RegsExcept s t' ([.x29, .x30, .x31] ++ [.x29, .x30, .x31]) := hreg.trans hrt'
      exact htr.mono (fun r hr => (List.mem_append.mp hr).elim id id)
    have hxt'' : t'.getReg .x31 = BitVec.ofNat 64 (slot2 (sB (n + 1))) := by
      have heq : slot2 (sB n) - 1696 = slot2 (sB (n + 1)) := by unfold slot2 slotA SCR sB; omega
      rw [hxt', heq]
    obtain ⟨t, step, hptf, hrtf, hmtf⟩ := ih (n + 1) (by omega) t' hreg' hpt' hmem_t' (fun _ => hxt'')
    refine ⟨t, ?_, hptf, ?_, hmtf⟩
    · rw [copy2RemSteps_succ]; exact step'.trans step
    · have htr2 : RegsExcept u t ([.x29, .x30, .x31] ++ [.x29, .x30, .x31]) := hrt'.trans hrtf
      exact htr2.mono (fun r hr => (List.mem_append.mp hr).elim id id)

/-- **E10**: from `COPY2` (entered by `POST + 38: jal zero, COPY2`), `copy2` writes the nonzero level-2 records and
stops at the halting `ecall` at `HALT2`. -/
theorem copy2_run {im : Image} (hc : CodeAt im (pcOf COPY2) copy2Words) (s : MachineState)
    (hpc : s.pc = pcOf COPY2)
    (hb : ∀ k < 9, s.getMem (BitVec.ofNat 64 (slot2 (sB k))) ≠ 0 →
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slot2 (sB k)))).toNat + 8 ≤ SCR) :
    ∃ t, Steps im s (copy2Steps s.getMem) (copy2Steps s.getMem) t ∧ t.pc = pcOf HALT2 ∧
      fetch im t = some (.base .ECALL) ∧ RegsExcept s t [.x29, .x30, .x31] ∧
      (∀ A, t.getMem A = copy2Mem s.getMem A) := by
  obtain ⟨u, step0, hpu, hxu, hru, hmu⟩ := copy2Head_step hc s hpc
  obtain ⟨t, step, hpt, hrt, hmt⟩ := copy2_run_aux hc s hb 9 0 rfl u (hru.mono (by decide))
    hpu (fun A => by rw [hmu A, copy2MemPartial_zero]) (fun _ => hxu)
  refine ⟨t, ?_, hpt, ?_, (hru.trans hrt).mono (by decide), hmt⟩
  · rw [← copy2RemSteps_nine_eq]; exact step0.trans step
  · have hc73 := copy2_iter_ecall_code hc
    rw [hc73.fetch t hpt]
    rfl

end SigGolfCandidate.FtsGrind
