import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PairCopy
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.LayoutBlock
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Lv
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactLoop
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def WIT : Nat := 0x800
def SNAP2 : Nat := 0x310000
/-- Nested FTS (r1-1): the final witness base (the frontier's was `WIT`). Witness trim: `0x520` (was `0x4c0`). -/
def WOUT : Nat := 0xB58
/-- Witness trim: the compactor's zeroing loop still starts at the old base `0x4c0` (unchanged machine word); the
96 bytes `[0x4c0, 0x520)` are scratch below the witness. -/
def WZ : Nat := 0x480
def copyRegs (src dst n ret : Nat) : RegFile :=
  (((RegFile.init.set .x1 (.c (pcOf ret))).set .x10 (.c (BitVec.ofNat 64 src))).set .x11
    (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def zeroRegs (dst n ret : Nat) : RegFile :=
  ((RegFile.init.set .x1 (.c (pcOf ret))).set .x11 (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
theorem run_snap : symRun cfgC cSnap (pcOf 42142) 40 =
    some ⟨⟨copyRegs WIT SNAP2 2729 42149, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
theorem run_zero2 : symRun cfgC cZero2 (pcOf 42149) 40 =
    some ⟨⟨zeroRegs WZ 3124 42154, [], []⟩, .c (pcOf 42137), .jump, 5, 5⟩ := by kernel_rfl
theorem run_hdr : symRun cfgC cHdr (pcOf 42154) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf 33117), .jump, 1, 1⟩ := by kernel_rfl
theorem run_ctr : symRun cfgC cCtr (pcOf 33117) 40 =
    some ⟨⟨copyRegs (SNAP2 + 32) 1184 2 (33117 + 5), [], []⟩, .c (pcOf 42130), .jump, 5, 5⟩ := by kernel_rfl
theorem run_preg (c : Nat) (hc : c < 9) : symRun cfgC (cPReg c) (pcOf (pregAt c)) 40 =
    some ⟨⟨copyRegs (SNAP2 + 64 + 896 * c) (10152 - 896 * c) 112 (pregAt c + 6), [], []⟩, .c (pcOf 42130), .jump,
      6, 6⟩ := by
  interval_cases c <;> kernel_rfl
theorem run_pend : symRun cfgC cPEnd (pcOf 33284) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf 42224), .jump, 1, 1⟩ := by kernel_rfl
/-- Nested FTS (r1-1): hold placement of coordinate `c` stores its top sibling at `hdst c + 144 flag`. -/
def hdst (c : Nat) : Nat := 8384 - 896 * c
def hfE (c : Nat) : E := E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 16)))
def hbE (c : Nat) : E := .bin .add (.bin .sll (hfE c) (.c 7#64)) (.bin .sll (hfE c) (.c 4#64))
def holdRegs (c : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (.c (BitVec.ofNat 64 (hdst c)))).set .x13
    (.bin .add (hbE c) (.c (BitVec.ofNat 64 (hdst c))))).set .x28 (.c 0x380000#64)).set .x29
    (E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c))))).set .x30 (E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 8))))).set
    .x31 (.bin .sll (hfE c) (.c 4#64))
def holdSym (c : Nat) : SymMem :=
  [(⟨some (hbE c), BitVec.ofNat 64 (hdst c + 8)⟩, E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 8)))),
    (⟨some (hbE c), BitVec.ofNat 64 (hdst c)⟩, E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c))))]
def holdObl (c : Nat) : List Oblig :=
  [.valid ⟨some (hbE c), BitVec.ofNat 64 (hdst c + 8)⟩ 8, .valid ⟨some (hbE c), BitVec.ofNat 64 (hdst c)⟩ 8]
theorem run_hold (c : Nat) (hc : c < 9) : symRun cfgC (cHold c) (pcOf (holdPc c)) 40 =
    some ⟨⟨holdRegs c, holdSym c, holdObl c⟩, .c (pcOf (holdPc c + 12)), .endOfCode, 12, 12⟩ := by
  interval_cases c <;> kernel_rfl
theorem run_top : symRun cfgC cTop (pcOf 42224) 40 =
    some ⟨⟨copyRegs (SNAP2 + 8136) (WIT + 8952) 528 42231, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
def chAt (lay : Nat) : Nat := if lay = 1 then 42235 else if lay = 2 then 42408 else 42557
def cCh (lay : Nat) : List (BitVec 32) := if lay = 1 then cCh1 else if lay = 2 then cCh2 else cCh3
def chSrc (lay : Nat) : Nat := SNAP2 + 8136 + 64 * (if lay = 1 then 66 + 7 else if lay = 2 then 116 + 6 else 165 + 6)
def chDst (lay : Nat) : Nat := lvDst lay + 16 * (if lay = 1 then 25 else 20)
theorem run_ch (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : symRun cfgC (cCh lay) (pcOf (chAt lay)) 40 =
    some ⟨⟨copyRegs (chSrc lay) (chDst lay) 344 (chAt lay + 7), [], []⟩, .c (pcOf 48000), .jump, 7, 7⟩ := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC copied zeroed copy_spec zero_spec)
set_option linter.unusedSimpArgs false
theorem and_mask (a m : Nat) (_hm : m ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]
theorem copySet_spec {im : Image} {code : List (BitVec 32)} {p src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem copySetQ_spec {im : Image} {code : List (BitVec 32)} {p q src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf q), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf q ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem copySetL_spec {im : Image} {code : List (BitVec 32)} {p L src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + L), [], []⟩, .c (pcOf 42130), .jump, L, L⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s L L t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + L) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem zeroSet_spec {im : Image} (hcode : CodeAt im (pcOf 42149) cZero2) (s : MachineState)
    (hpc : s.pc = pcOf 42149) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 42137 ∧ t.getReg .x11 = BitVec.ofNat 64 WZ ∧
      t.getReg .x12 = BitVec.ofNat 64 3124 ∧ t.getReg .x1 = pcOf 42154 ∧
      RegsExcept s t [.x1, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound run_zero2 hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem idx_spec {im : Image} (hcode : CodeAt im (pcOf 42231) cIdx) (s : MachineState) (hpc : s.pc = pcOf 42231) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42235 ∧
      t.getReg .x22 = s.getMem (BitVec.ofNat 64 0x60) >>> 33 ∧ t.getReg .x18 = BitVec.ofNat 64 LPLAN ∧
      RegsExcept s t [.x18, .x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RIdx (by exact hcode) s hpc (by simp [RIdx.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RIdx.res, E.eval]
  · simp [RIdx.res, rv_simp]
  · simp [RIdx.res, rv_simp, LPLAN]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h18, h22⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
def rowAt (lay : Nat) : Nat := if lay = 1 then 42242 else if lay = 2 then 42415 else 42564
def rowLen (lay : Nat) : Nat := if lay = 1 then 5 else if lay = 2 then 4 else 3
def cRowL (lay : Nat) : List (BitVec 32) := if lay = 1 then cRow1 else if lay = 2 then cRow2 else cRow3
def lroute (lay idx : Nat) : Nat := if lay = 1 then idx / 2 ^ 12 % 128 else if lay = 2 then idx / 2 ^ 6 % 64 else idx % 64
theorem lroute_lt (lay idx : Nat) : lroute lay idx < 2 ^ lvH lay := by
  unfold lroute lvH; split_ifs <;> simp_all <;> exact Nat.mod_lt _ (by norm_num)
set_option maxRecDepth 20000 in
theorem row1_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 1)) (cRowL 1)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 1)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 1) (rowLen 1) t ∧ t.pc = pcOf (rowAt 1 + rowLen 1) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 1 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 1 (lroute 1 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow1.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 1 idx) := by
    simp only [Result.toState_getReg, RRow1.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (12#64 : Word) = BitVec.ofNat 64 12 from rfl, ofNat_shr', show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      and_mask _ 7 (by norm_num)]
    unfold lroute
    simp only [if_true]
    rw [Nat.mod_eq_of_lt hi]; norm_num
  have e20 : (RRow1.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 1 (lroute 1 idx)) := by
    have : (RRow1.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 1 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN + 512#64 := by
      rw [← e19]; simp only [Result.toState_getReg, RRow1.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, show (512#64 : Word) = BitVec.ofNat 64 512 from rfl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [if_true]; ring
  refine ⟨_, symRun_sound RRow1 hcode s hpc (by simp [RRow1.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 1 + rowLen 1 = 42247 by decide]; simp [Result.toState_pc, RRow1.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem row2_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 2)) (cRowL 2)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 2)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 2) (rowLen 2) t ∧ t.pc = pcOf (rowAt 2 + rowLen 2) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 2 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 2 (lroute 2 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow2.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 2 idx) := by
    simp only [Result.toState_getReg, RRow2.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ofNat_shr', show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      and_mask _ 6 (by norm_num)]
    unfold lroute
    simp only [show (2 : Nat) ≠ 1 by decide, if_true, if_false]
    rw [Nat.mod_eq_of_lt hi]; norm_num
  have e20 : (RRow2.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 2 (lroute 2 idx)) := by
    have : (RRow2.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 2 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN := by
      rw [← e19]; simp only [Result.toState_getReg, RRow2.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [show (2 : Nat) ≠ 1 by decide, if_false]; ring
  refine ⟨_, symRun_sound RRow2 hcode s hpc (by simp [RRow2.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 2 + rowLen 2 = 42419 by decide]; simp [Result.toState_pc, RRow2.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem row3_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 3)) (cRowL 3)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 3)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 3) (rowLen 3) t ∧ t.pc = pcOf (rowAt 3 + rowLen 3) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 3 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 3 (lroute 3 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow3.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 3 idx) := by
    simp only [Result.toState_getReg, RRow3.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      and_mask _ 6 (by norm_num)]
    unfold lroute
    simp only [show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_false]
    norm_num
  have e20 : (RRow3.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 3 (lroute 3 idx)) := by
    have : (RRow3.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 3 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN := by
      rw [← e19]; simp only [Result.toState_getReg, RRow3.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [show (3 : Nat) ≠ 1 by decide, if_false]; ring
  refine ⟨_, symRun_sound RRow3 hcode s hpc (by simp [RRow3.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 3 + rowLen 3 = 42567 by decide]; simp [Result.toState_pc, RRow3.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
theorem copyPhase {code : List (BitVec 32)} {p src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hn : 0 < n) (hn' : n < 2 ^ 32) (hs : src % 8 = 0)
    (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (7 + (6 * n + 1)) (7 + (6 * n + 1)) t ∧ t.pc = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if dst ≤ A ∧ A < dst + 8 * n ∧ (A - dst) % 8 = 0 then s.getMem (BitVec.ofNat 64 (src + (A - dst)))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySet_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := copy_spec hc u pu src dst n (p + 7) u10 u11 u12 u1 hn hn' hs hs' hd hd' hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  unfold copied
  split
  · rw [fu _ (by omega) (fun h => h)]
  · rw [fu _ hA (fun h => h)]
/-- Pairing stage 1: a lower layer's chain area is written by the pair copy block 48000 (called with `jal ra`). -/
theorem pairPhase {code : List (BitVec 32)} {p src dst : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst 344 (p + 7), [], []⟩, .c (pcOf 48000), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES)
    (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∃ t, Steps im s (7 + 258) (7 + 258) t ∧ t.pc = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        PairCopy.pairCopyMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySetQ_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := PairCopy.pairCopy_spec hc.pair u pu src dst (p + 7) u10 u11 u1 hs hs' hd hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  have hso : PairCopy.srcOff ((A - dst) % 104) ≤ 120 := by unfold PairCopy.srcOff; split_ifs <;> omega
  unfold PairCopy.pairCopyMem PairCopy.pcMem
  split_ifs <;> (beta_reduce; rw [fu _ (by omega) (fun h => h)])
theorem copyPhaseL {code : List (BitVec 32)} {p L src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + L), [], []⟩, .c (pcOf 42130), .jump, L, L⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hn : 0 < n) (hn' : n < 2 ^ 32) (hs : src % 8 = 0)
    (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (L + (6 * n + 1)) (L + (6 * n + 1)) t ∧ t.pc = pcOf (p + L) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if dst ≤ A ∧ A < dst + 8 * n ∧ (A - dst) % 8 = 0 then s.getMem (BitVec.ofNat 64 (src + (A - dst)))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySetL_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := copy_spec hc u pu src dst n (p + L) u10 u11 u12 u1 hn hn' hs hs' hd hd' hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  unfold copied
  split
  · rw [fu _ (by omega) (fun h => h)]
  · rw [fu _ hA (fun h => h)]
theorem jump1_spec {code : List (BitVec 32)} {p q : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 = some ⟨⟨RegFile.init, [], []⟩, .c (pcOf q), .jump, 1, 1⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf q ∧ RegsExcept s t [] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · intro r _; rw [Result.toState_getReg]; cases r <;> rfl
  · intro A; simp [rv_simp]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem hold_spec (c : Nat) (hc9 : c < 9) (s : MachineState) (hpc : s.pc = pcOf (holdPc c)) (f : Nat) (hf2 : f < 2)
    (hf : s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (holdPc c + 12) ∧ RegsExcept s t [.x6, .x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = hdst c + 144 * f + 8 then s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 8))
        else if A = hdst c + 144 * f then s.getMem (BitVec.ofNat 64 (Compact.holdAt c))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hb : (hbE c).eval s = BitVec.ofNat 64 (144 * f) := by
    simp only [hbE, hfE, E.eval, BinOp.eval, hf]
    rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl <;> decide
  have hd : hdst c + 160 ≤ 9472 ∧ 1216 ≤ hdst c ∧ hdst c % 16 = 0 := by unfold hdst; omega
  have hv : ∀ x, x + 8 ≤ 16777216 → x % 8 = 0 → accessValid (BitVec.ofNat 64 x) 8 = true := by
    intro x h1 h2
    rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by rw [hM]; omega, h2⟩
  have hobl : Oblig.all s (holdObl c) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [holdObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]; exact hv _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]; exact hv _ (by omega) (by omega)
  refine ⟨_, symRun_sound (run_hold c hc9) (code_cHold hc c hc9) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h6, h13, h28, h29, h30, h31⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    simp only [Result.toState_getMem, holdSym, memEval_cons, memEval_nil, Addr.eval, hb, E.eval, ofNat_add_ofNat]
    have hX1 : 144 * f + (hdst c + 8) < 2 ^ 64 := by omega
    have hX0 : 144 * f + hdst c < 2 ^ 64 := by omega
    by_cases e1 : A = hdst c + 144 * f + 8
    · rw [if_pos (by rw [e1]; congr 1; omega), if_pos e1]
    · rw [if_neg (fun h => e1 (by have := (ofNat_inj hA hX1).mp h; omega)), if_neg e1]
      by_cases e2 : A = hdst c + 144 * f
      · rw [if_pos (by rw [e2]; congr 1; omega), if_pos e2]
      · rw [if_neg (fun h => e2 (by have := (ofNat_inj hA hX0).mp h; omega)), if_neg e2]
end
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def sibS (lay r j : Nat) : Nat := 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)
def padS (lay r j : Nat) : Nat := 16 * plan lay r j + 32
theorem sibOff_eq (b : Nat) (hb : b < 2) : SigGolfCandidate.T3M.sibOff b = 48 * (1 - b) := by
  unfold SigGolfCandidate.T3M.sibOff; split <;> omega
theorem lv_disj (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay) (j j' : Nat)
    (hj : j < lvH lay) (hj' : j' < lvH lay) (hne : j ≠ j') :
    sibS lay r j ≠ sibS lay r j' ∧ sibS lay r j ≠ padS lay r j' ∧ padS lay r j ≠ padS lay r j' := by
  obtain ⟨h1, h4⟩ := hl
  have hb : ∀ i, r / 2 ^ i % 2 < 2 := fun i => Nat.mod_lt _ (by norm_num)
  have key : ∀ L : SigGolfCandidate.T3.Layer, L.val = lay → L.val ≠ 0 →
      SigGolfCandidate.T3.height L = lvH lay → (∀ i, plan lay r i = (ClaudeWCT.W9.T3M.lowerPlan L r).getD i 0) →
      sibS lay r j ≠ sibS lay r j' ∧ sibS lay r j ≠ padS lay r j' ∧ padS lay r j ≠ padS lay r j' := by
    intro L hL hL0 hH hP
    have hr' : r < 2 ^ SigGolfCandidate.T3.height L := by rw [hH]; exact hr
    have hj1 : j < SigGolfCandidate.T3.height L := by rw [hH]; exact hj
    have hj2 : j' < SigGolfCandidate.T3.height L := by rw [hH]; exact hj'
    have d1 := ClaudeWCT.W9.T3M.lower_sib_disjoint L hL0 r hr' j hj1 j' hj2 hne
    have d2 := ClaudeWCT.W9.T3M.lower_pad_disjoint L hL0 r hr' j' hj2 j hj1
    have d3 := ClaudeWCT.W9.T3M.lower_pad_pad_disjoint L hL0 r hr' j hj1 j' hj2 hne
    unfold ClaudeWCT.W9.T3M.lowerSibSlot at d1 d2
    rw [sibOff_eq _ (hb j), sibOff_eq _ (hb j')] at d1
    rw [sibOff_eq _ (hb j)] at d2
    unfold sibS padS
    rw [hP j, hP j']
    refine ⟨?_, ?_, ?_⟩ <;> omega
  interval_cases lay
  · exact key 1 rfl (by decide) rfl (fun i => rfl)
  · exact key 2 rfl (by decide) rfl (fun i => rfl)
  · exact key 3 rfl (by decide) rfl (fun i => rfl)
def lvHit (lay r j p : Nat) : Prop :=
  p = sibS lay r j ∨ p = sibS lay r j + 8 ∨ p = padS lay r j ∨ p = padS lay r j + 8
instance (lay r j p : Nat) : Decidable (lvHit lay r j p) := by unfold lvHit; infer_instance
def lvsMem (M : Nat → Word) (lay r L : Nat) (A : Nat) : Word :=
  if lvDst lay ≤ A then
    match (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | some j => M (lvSrc lay j + (A - lvDst lay - 16 * plan lay r j))
    | none => M A
  else M A
theorem lvs_find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem lvs_find_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem plan_mod16 (lay r j : Nat) : sibS lay r j % 16 = 0 ∧ padS lay r j % 16 = 0 := by
  unfold sibS padS
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibS_ne_padS (lay r j : Nat) : sibS lay r j ≠ padS lay r j := by
  unfold sibS padS
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega
theorem lvsMem_succ (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay)
    (L : Nat) (hL : L < lvH lay) (A : Nat) :
    lvsMem M lay r (L + 1) A =
      if A = lvDst lay + sibS lay r L + 8 then M (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2) + 8)
      else if A = lvDst lay + sibS lay r L then M (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2))
      else if A = lvDst lay + padS lay r L + 8 then M (lvSrc lay L + 40)
      else if A = lvDst lay + padS lay r L then M (lvSrc lay L + 32)
      else lvsMem M lay r L A := by
  have hm := plan_mod16 lay r L
  have hsp := sibS_ne_padS lay r L
  unfold lvsMem
  by_cases hA : lvDst lay ≤ A
  · rw [if_pos hA, if_pos hA, lvs_find_succ]
    cases h : (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | some l =>
      obtain ⟨hl', hp⟩ := lvs_find_some h
      have hp' : lvHit lay r l (A - lvDst lay) := of_decide_eq_true hp
      unfold lvHit at hp'
      have hd := lv_disj lay hl r hr l L (by omega) hL (by omega)
      have hd' := lv_disj lay hl r hr L l hL (by omega) (by omega)
      have hml := plan_mod16 lay r l
      simp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    | none =>
      simp only
      by_cases q1 : A = lvDst lay + sibS lay r L + 8
      · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q1]
        simp only
        congr 1; unfold sibS at q1; omega
      · rw [if_neg q1]
        by_cases q2 : A = lvDst lay + sibS lay r L
        · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q2]
          simp only
          congr 1; unfold sibS at q2; omega
        · rw [if_neg q2]
          by_cases q3 : A = lvDst lay + padS lay r L + 8
          · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q3]
            simp only
            congr 1; unfold padS at q3; omega
          · rw [if_neg q3]
            by_cases q4 : A = lvDst lay + padS lay r L
            · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q4]
              simp only
              congr 1; unfold padS at q4; omega
            · rw [if_neg q4, if_neg (show ¬ decide (lvHit lay r L (A - lvDst lay)) = true from fun h => by have := of_decide_eq_true h; unfold lvHit at this; omega)]
  · rw [if_neg hA, if_neg hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
def pathTop (lay : Nat) : Nat := 16 * (if lay = 1 then 25 else 20)
theorem sibS_padS_lt (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    sibS lay r j + 16 ≤ pathTop lay ∧ padS lay r j + 16 ≤ pathTop lay := by
  have h := (plan_ok lay r j hl hr hj).2
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold sibS padS pathTop; split_ifs at h ⊢ <;> constructor <;> omega
theorem pathTop_le (lay : Nat) : pathTop lay ≤ 16 * 25 := by unfold pathTop; split_ifs <;> omega
theorem lvsMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay)
    (L : Nat) (hL : L ≤ lvH lay) (A : Nat) (hA : A < lvDst lay ∨ lvDst lay + pathTop lay ≤ A) :
    lvsMem M lay r L A = M A := by
  unfold lvsMem
  split
  · cases h : (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | none => rfl
    | some l =>
      obtain ⟨hl', hp⟩ := lvs_find_some h
      have hp' : lvHit lay r l (A - lvDst lay) := of_decide_eq_true hp
      unfold lvHit at hp'
      have := sibS_padS_lt lay r l hl hr (by omega)
      omega
  · rfl
theorem lvsMem_zero (M : Nat → Word) (lay r A : Nat) : lvsMem M lay r 0 A = M A := by
  unfold lvsMem; split <;> rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem lvs_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (u : MachineState) (M0 : Nat → Word)
    (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A) (hpc : u.pc = pcOf (lvAt lay 0)) (r : Nat)
    (hr : r < 2 ^ lvH lay) (h19 : u.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt u) :
    ∀ L ≤ lvH lay - 1, ∃ t, Steps im u (23 * L) (23 * L) t ∧ t.pc = pcOf (lvAt lay L) ∧
      RegsExcept u t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = lvsMem M0 lay r L A := by
  have hD : 0x800 + 11648 ≤ lvDst lay ∧ lvDst lay + 16 * 25 ≤ 0x800 + 20944 := by
    unfold lvDst; split_ifs <;> omega
  have hLP : LPLAN = 0xff9400 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [lvAt] using hpc, RegsExcept.refl u _, fun A hA => by
      rw [hM A hA, lvsMem_zero]⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpt : LPlanAt t := fun k hk => by
      have := pathTop_le lay
      rw [mt _ (by omega), lvsMem_out M0 lay hl r hr L (by omega) _ (Or.inr (by omega)), ← hM _ (by omega)]
      exact hp k hk
    obtain ⟨t', st', pt', rt', mt'⟩ := lv_spec hc lay L hl (by omega) t pt r hr
      (by rw [rt.get (by decide), h19]) (by rw [rt.get (by decide), h20]) hpt
    have hS : 0x310000 ≤ lvSrc lay L ∧ lvSrc lay L + 64 ≤ 0x310000 + 21832 := by
      unfold lvSrc; unfold lvH at hL; split_ifs at * <;> omega
    have hb : r / 2 ^ L % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hpt23 := pathTop_le lay
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold lvAt; split_ifs <;> ring_nf,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, lvsMem_succ M0 lay hl r hr L (by omega) A]
    have e1 := mt (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2) + 8) (by omega)
    have e2 := mt (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2)) (by omega)
    have e3 := mt (lvSrc lay L + 40) (by omega)
    have e4 := mt (lvSrc lay L + 32) (by omega)
    rw [lvsMem_out M0 lay hl r hr L (by omega) _ (Or.inr (by omega))] at e1 e2 e3 e4
    rw [e1, e2, e3, e4, mt A hA]
    unfold sibS padS
    simp only [Nat.add_assoc, Nat.reduceAdd]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC copied zeroed copy_spec zero_spec)
set_option linter.unusedSimpArgs false
/-- Slot of coordinate `c`'s top sibling (flag clamped to `0, 1`; the honest flag is `1 - bit6`). -/
def hslot (M : Nat → Word) (c : Nat) : Nat := hdst c + 144 * min (M (Compact.holdAt c + 16)).toNat 1
/-- Memory after the first `Q` hold placements over `M` (hold slots read from `M`). -/
def plMem (M : Nat → Word) : Nat → Nat → Word
  | 0, A => M A
  | Q + 1, A => if A = hslot M Q + 8 then M (Compact.holdAt Q + 8)
      else if A = hslot M Q then M (Compact.holdAt Q) else plMem M Q A
theorem hslot_bound (M : Nat → Word) (c : Nat) : hdst c ≤ hslot M c ∧ hslot M c ≤ hdst c + 144 := by
  unfold hslot; have := Nat.min_le_right (M (Compact.holdAt c + 16)).toNat 1; constructor <;> omega
theorem plMem_out (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) (A : Nat) (hA : A < 1152 ∨ 11048 ≤ A) :
    plMem M Q A = M A := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have hb := hslot_bound M Q
    have hd : hdst Q + 160 ≤ 9472 ∧ 1216 ≤ hdst Q := by unfold hdst; omega
    simp only [plMem]
    rw [if_neg (by omega), if_neg (by omega), ih (by omega)]
/-- The nine region copies of P_final: region `c` (112 words) from the staging snapshot to `10152 - 896 c`. -/
def regsMem (M : Nat → Word) (Q : Nat) (A : Nat) : Word :=
  if 0 < Q ∧ 11048 - 896 * Q ≤ A ∧ A < 11048 ∧ A % 8 = 0 then
    M (SNAP2 + 64 + 896 * ((11047 - A) / 896) + (A - (10152 - 896 * ((11047 - A) / 896))))
  else M A
theorem regsMem_succ (M : Nat → Word) (Q : Nat) (hQ : Q < 9) (A : Nat) :
    (if 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0 then
      M (SNAP2 + 64 + 896 * Q + (A - (10152 - 896 * Q))) else regsMem M Q A) = regsMem M (Q + 1) A := by
  unfold regsMem
  by_cases h1 : 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0
  · rw [if_pos h1, if_pos (by omega), show (11047 - A) / 896 = Q by omega]
  · rw [if_neg h1]
    by_cases h2 : 0 < Q ∧ 11048 - 896 * Q ≤ A ∧ A < 11048 ∧ A % 8 = 0
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
def ctrMem (M : Nat → Word) (A : Nat) : Word :=
  if 1184 ≤ A ∧ A < 1184 + 8 * 2 ∧ (A - 1184) % 8 = 0 then M (SNAP2 + 32 + (A - 1184)) else M A
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem pregs_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (pregAt 0)) :
    ∀ Q ≤ 9, ∃ t, Steps im u (679 * Q) (679 * Q) t ∧ t.pc = pcOf (pregAt Q) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = regsMem M0 Q A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  intro Q hQ
  induction Q with
  | zero => exact ⟨u, Steps.refl u, by simpa using hpc, RegsExcept.refl u _, fun A hA => by
      rw [hM A hA]; unfold regsMem; rw [if_neg (by omega)]⟩
  | succ Q ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hrun := run_preg Q (by omega)
    obtain ⟨t', st', pt', rt', mt'⟩ := copyPhaseL hc (code_cPReg hc Q (by omega)) hrun t pt
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold pregAt; congr 1,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, ← regsMem_succ M0 Q (by omega) A]
    by_cases h1 : 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0
    · rw [if_pos h1, if_pos h1, mt _ (by omega)]
      unfold regsMem
      rw [if_neg (by omega)]
    · rw [if_neg h1, if_neg h1, mt A hA]
set_option maxRecDepth 20000 in
theorem holds_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (holdPc 0)) (hfl : ∀ c < 9, ∃ f < 2, M0 (Compact.holdAt c + 16) = BitVec.ofNat 64 f) :
    ∀ Q ≤ 9, ∃ t, Steps im u (12 * Q) (12 * Q) t ∧ t.pc = pcOf (holdPc Q) ∧
      RegsExcept u t [.x6, .x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = plMem M0 Q A := by
  intro Q hQ
  induction Q with
  | zero => exact ⟨u, Steps.refl u, by simpa using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ Q ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    obtain ⟨f, hf2, hf⟩ := hfl Q (by omega)
    have hH : Compact.holdAt Q = 0x380000 + 32 * Q := rfl
    have hth : ∀ j < 24, t.getMem (BitVec.ofNat 64 (Compact.holdAt Q + j)) = M0 (Compact.holdAt Q + j) :=
      fun j hj => by rw [mt _ (by omega), plMem_out M0 Q (by omega) _ (Or.inr (by omega))]
    have hth0 : t.getMem (BitVec.ofNat 64 (Compact.holdAt Q)) = M0 (Compact.holdAt Q) := by
      rw [mt _ (by omega), plMem_out M0 Q (by omega) _ (Or.inr (by omega))]
    obtain ⟨t', st', pt', rt', mt'⟩ := hold_spec hc Q (by omega) t pt f hf2 (by rw [hth 16 (by omega), hf])
    have hs : hslot M0 Q = hdst Q + 144 * f := by
      unfold hslot; rw [hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; congr 2; omega
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold holdPc; congr 1,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, hth 8 (by omega), hth0, mt A hA]
    simp only [plMem, hs]
end
/-- Pairing stage 1: the lower chain area after the pair copy block (writes only in `[chDst, chDst + 2248)`). -/
def chMem (M : Nat → Word) (lay : Nat) (A : Nat) : Word := PairCopy.pairCopyMem M (chSrc lay) (chDst lay) A
theorem chMem_out (M : Nat → Word) (lay A : Nat) (h : A < chDst lay ∨ chDst lay + 2248 ≤ A) : chMem M lay A = M A := by
  simp only [chMem, PairCopy.pairCopyMem, PairCopy.pcMem]
  split_ifs <;> first | rfl | omega
/-- C3 (FULL, E6): offset of the root window's tweak high word (LE64 1) in a lower path area. -/
def rootOff (lay r : Nat) : Nat := 16 * plan lay r (rootJ lay) + 24
theorem rootOff_lt (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay) :
    rootOff lay r + 8 ≤ pathTop lay ∧ rootOff lay r % 8 = 0 := by
  have hj : rootJ lay < lvH lay := by obtain ⟨h1, h4⟩ := hl; unfold rootJ lvH; split_ifs <;> omega
  have h := (plan_ok lay r (rootJ lay) hl hr hj).2
  unfold rootOff pathTop; split_ifs at h ⊢ <;> omega
def layMem (M : Nat → Word) (lay idx : Nat) (A : Nat) : Word :=
  if A = lvDst lay + rootOff lay (lroute lay idx) then 1#64
  else lvsMem (chMem M lay) lay (lroute lay idx) (lvH lay) A
def layLen (lay : Nat) : Nat := 265 + rowLen lay + 23 * lvH lay + 4
theorem chDst_eq (lay : Nat) : chDst lay = lvDst lay + pathTop lay := by unfold chDst pathTop; rfl
theorem layMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx A : Nat)
    (hA : A < lvDst lay ∨ chDst lay + 2248 ≤ A) : layMem M lay idx A = M A := by
  have hA' := hA
  have hce := chDst_eq lay
  have hro := rootOff_lt lay hl (lroute lay idx) (lroute_lt lay idx)
  rw [chDst_eq] at hA'
  unfold layMem
  rw [if_neg (by omega), lvsMem_out _ lay hl _ (lroute_lt lay idx) _ le_rfl _ (by omega)]
  rw [chMem_out _ _ _ (by omega)]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem layer_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (u : MachineState) (M0 : Nat → Word)
    (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A) (hpc : u.pc = pcOf (chAt lay)) (idx : Nat)
    (hidx : idx < 2 ^ 31) (h22 : u.getReg .x22 = BitVec.ofNat 64 idx) (h18 : u.getReg .x18 = BitVec.ofNat 64 LPLAN)
    (hp : LPlanAt u) :
    ∃ t, Steps im u (layLen lay) (layLen lay) t ∧ t.pc = pcOf (lvAt lay (lvH lay)) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12, .x19, .x20, .x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = layMem M0 lay idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨h1, h4⟩ := hl
  have hcode : CodeAt im (pcOf (chAt lay)) (cCh lay) := by
    interval_cases lay
    · exact code_cCh1 hc
    · exact code_cCh2 hc
    · exact code_cCh3 hc
  have hsrc : chSrc lay % 8 = 0 ∧ 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 := by
    interval_cases lay <;> decide
  have hdst : chDst lay % 8 = 0 ∧ chDst lay + 2248 ≤ 0x800 + 20960 ∧
      lvDst lay % 8 = 0 ∧ 0x800 + 13176 ≤ lvDst lay := by
    interval_cases lay <;> decide
  obtain ⟨u1, s1, p1, r1, m1⟩ := pairPhase hc hcode (run_ch lay ⟨h1, h4⟩) u hpc hsrc.1 (by omega) hdst.1
    (by omega)
  have hm1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = chMem M0 lay A := fun A hA => by
    rw [m1 A hA]
    have hso : PairCopy.srcOff ((A - chDst lay) % 104) ≤ 120 := by unfold PairCopy.srcOff; split_ifs <;> omega
    simp only [chMem, PairCopy.pairCopyMem, PairCopy.pcMem]
    split_ifs <;> rw [hM _ (by omega)]
  have hp1 : LPlanAt u1 := fun k hk => by
    rw [hm1 _ (by omega), chMem_out _ _ _ (Or.inr (by unfold LPLAN; omega)), ← hM _ (by omega)]; exact hp k hk
  have hrow : ∀ u1 : MachineState, u1.pc = pcOf (chAt lay + 7) → u1.getReg .x22 = BitVec.ofNat 64 idx →
      u1.getReg .x18 = BitVec.ofNat 64 LPLAN →
      ∃ t, Steps im u1 (rowLen lay) (rowLen lay) t ∧ t.pc = pcOf (rowAt lay + rowLen lay) ∧
        t.getReg .x19 = BitVec.ofNat 64 (lroute lay idx) ∧
        t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay (lroute lay idx)) ∧
        RegsExcept u1 t [.x19, .x20] ∧ Frame u1 t (fun _ => False) := by
    intro u1 hp1 h22' h18'
    interval_cases lay
    · exact row1_spec (code_cRow1 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
    · exact row2_spec (code_cRow2 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
    · exact row3_spec (code_cRow3 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
  obtain ⟨u2, s2, p2, x19, x20, r2, f2⟩ := hrow u1 p1 (by rw [r1.get (by decide), h22])
    (by rw [r1.get (by decide), h18])
  have hm2 : ∀ A < 2 ^ 64, u2.getMem (BitVec.ofNat 64 A) = chMem M0 lay A := fun A hA => by
    rw [f2 A hA (fun h => h), hm1 A hA]
  have hp2 : LPlanAt u2 := fun k hk => by rw [f2 _ (by unfold LPLAN; omega) (fun h => h)]; exact hp1 k hk
  obtain ⟨u3, s3, p3, r3, m3⟩ := lvs_spec hc lay ⟨h1, h4⟩ u2 (chMem M0 lay) hm2
    (by rw [p2]; interval_cases lay <;> rfl) (lroute lay idx) (lroute_lt lay idx) x19 x20 hp2 (lvH lay - 1) le_rfl
  have hjr : rootJ lay = lvH lay - 1 := by unfold rootJ lvH; split_ifs <;> omega
  have hH1 : 1 ≤ lvH lay := by unfold lvH; split_ifs <;> omega
  have hDu : lvDst lay ≤ 0x800 + 18392 := by unfold lvDst; split_ifs <;> omega
  have hr := lroute_lt lay idx
  have hpt := pathTop_le lay
  have hpt3 : LPlanAt u3 := fun k hk => by
    rw [m3 _ (by omega), lvsMem_out _ lay ⟨h1, h4⟩ _ hr _ (by omega) _ (Or.inr (by unfold LPLAN; omega)), ← hm2 _ (by omega)]
    exact hp2 k hk
  obtain ⟨u4, s4, p4, r4, m4⟩ := lvRoot_spec hc lay ⟨h1, h4⟩ u3 (by rw [p3, hjr]) (lroute lay idx) hr
    (by rw [r3.get (by decide), x19]) (by rw [r3.get (by decide), x20]) hpt3
  refine ⟨u4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold layLen; omega) (by unfold layLen; omega),
    by rw [p4, hjr]; congr 1; unfold lvAt; split_ifs <;> omega,
    (((r1.trans r2).trans r3).trans r4).mono (by decide), fun A hA => ?_⟩
  rw [← hjr] at m3
  have hS : 0x310000 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc rootJ; split_ifs <;> omega
  have hb : lroute lay idx / 2 ^ rootJ lay % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have e1 := m3 (lvSrc lay (rootJ lay) + 48 * (1 - lroute lay idx / 2 ^ rootJ lay % 2) + 8) (by omega)
  have e2 := m3 (lvSrc lay (rootJ lay) + 48 * (1 - lroute lay idx / 2 ^ rootJ lay % 2)) (by omega)
  have e3 := m3 (lvSrc lay (rootJ lay) + 40) (by omega)
  have e4 := m3 (lvSrc lay (rootJ lay) + 32) (by omega)
  rw [lvsMem_out _ lay ⟨h1, h4⟩ _ hr _ (by omega) _ (Or.inr (by omega))] at e1 e2 e3 e4
  have hsucc := lvsMem_succ (chMem M0 lay) lay ⟨h1, h4⟩ _ hr (rootJ lay) (by omega) A
  rw [show rootJ lay + 1 = lvH lay by omega] at hsucc
  rw [m4 A hA, e1, e2, e3, e4, m3 A hA]
  unfold layMem rootOff
  rw [hsucc]
  unfold sibS padS
  simp only [Nat.add_assoc, Nat.reduceAdd]
end
/-- Pairing stage 1: the staged rho / digest-counter words now sit 16 bytes higher (abs 23008 .. 23040). -/
def tailMem (M : Nat → Word) (A : Nat) : Word :=
  if A = WIT + 20984 then LoadKind.wu.fromWord (M (SNAP2 + 16)) 0
  else if A = WIT + 20976 then 0
  else if A = WIT + 20968 then M (SNAP2 + 8)
  else if A = WIT + 20960 then M SNAP2
  else M A
set_option maxRecDepth 20000 in
theorem tail_spec {im : Image} (hcode : CodeAt im (pcOf 42705) cTail) (s : MachineState) (hpc : s.pc = pcOf 42705) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 42716 ∧ RegsExcept s t [.x5, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = tailMem (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound RTail hcode s hpc (by simp [RTail.res, rv_simp]), ?_, ?_, fun A hA => ?_⟩
  · simp [Result.toState_pc, RTail.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · have key : ∀ c : Nat, c < 2 ^ 64 → (BitVec.ofNat 64 A = BitVec.ofNat 64 c ↔ A = c) := fun c hc => ofNat_inj hA hc
    simp only [Result.toState_getMem, RTail.res, memEval_cons, memEval_nil, Addr.eval, E.eval, UnOp.eval,
      key 23032 (by norm_num), key 23024 (by norm_num), key 23016 (by norm_num), key 23008 (by norm_num)]
    unfold tailMem
    simp only [show WIT = 0x800 from rfl, show SNAP2 = 0x310000 from rfl, Nat.reduceAdd]
    rfl
def snapMem (M : Nat → Word) (A : Nat) : Word :=
  if SNAP2 ≤ A ∧ A < SNAP2 + 8 * 2729 ∧ (A - SNAP2) % 8 = 0 then M (WIT + (A - SNAP2)) else M A
/-- Zeroing of 3124 words from `WZ` (to `WIT + 19248`; everything above is rewritten by the layer-3 chain copy
and the tail). -/
def zMem (M : Nat → Word) (A : Nat) : Word :=
  if WZ ≤ A ∧ A < WZ + 8 * 3124 ∧ (A - WZ) % 8 = 0 then 0 else M A
def topMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT + 8952 ≤ A ∧ A < WIT + 8952 + 8 * 528 ∧ (A - (WIT + 8952)) % 8 = 0 then M (SNAP2 + 8136 + (A - (WIT + 8952)))
  else M A
/-- Nested FTS (r1-1): memory after the zeroing, the L3 counter copy, the nine region copies and the nine hold
placements of P_final. -/
def stMem (M : Nat → Word) (A : Nat) : Word := plMem (regsMem (ctrMem (zMem (snapMem M))) 9) 9 A
def run2Mem (M : Nat → Word) (idx : Nat) (A : Nat) : Word :=
  tailMem (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) A
theorem stMem_out (M : Nat → Word) (A : Nat) (hA : A < WZ ∨ SNAP2 + 8 * 2729 ≤ A) : stMem M A = M A := by
  have hW : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem stMem_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    stMem M (SNAP2 + x) = M (WIT + x) := by
  have hW : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl _ (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show SNAP2 + x - SNAP2 = x by omega]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run2_spec (s : MachineState) (hpc : s.pc = pcOf 42142) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hix : s.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 idx) (hp : LPlanAt s)
    (hfl : ∀ c < 9, ∃ f < 2, s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f) :
    ∃ t, Steps im s 39570 39570 t ∧ t.pc = pcOf 42716 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = run2Mem (fun B => s.getMem (BitVec.ofNat 64 B)) idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨u1, s1, p1, r1, m1⟩ := copyPhase hc (code_cSnap hc) run_snap s hpc (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have e1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = snapMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => by rw [m1 A hA]; rfl
  obtain ⟨u2a, s2a, p2a, x11, x12, x1, r2a, f2a⟩ := zeroSet_spec (code_cZero2 hc) u1 (by rw [p1])
  obtain ⟨u2, s2, p2, r2, m2⟩ := zero_spec hc u2a p2a WZ 3124 42154 x11 x12 x1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  have e2 : ∀ A < 2 ^ 64, u2.getMem (BitVec.ofNat 64 A) =
      zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [m2 A hA]; unfold zeroed zMem; split
    · rfl
    · rw [f2a A hA (fun h => h), e1 A hA]
  obtain ⟨u3a, s3a, p3a, r3a, m3a⟩ := jump1_spec hc (code_cHdr hc) run_hdr u2 p2
  obtain ⟨u3, s3, p3, r3, m3⟩ := copyPhaseL hc (code_cCtr hc) run_ctr u3a p3a (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) =
      ctrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B)))) A := fun A hA => by
    rw [m3 A hA]; unfold ctrMem; split
    · rw [m3a, e2 _ (by omega)]
    · rw [m3a, e2 A hA]
  obtain ⟨u4, s4, p4, r4, m4⟩ := pregs_spec hc u3 _ e3 (by rw [p3]; rfl) 9 le_rfl
  have hfl' : ∀ c < 9, ∃ f < 2,
      regsMem (ctrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))))) 9 (Compact.holdAt c + 16) =
        BitVec.ofNat 64 f := by
    intro c hc9
    obtain ⟨f, hf2, hf⟩ := hfl c hc9
    have hH : Compact.holdAt c = 0x380000 + 32 * c := rfl
    refine ⟨f, hf2, ?_⟩
    unfold regsMem ctrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hf
  obtain ⟨u5, s5, p5, r5, m5⟩ := holds_spec hc u4 _ m4 (by rw [p4]; rfl) hfl' 9 le_rfl
  obtain ⟨u5b, s5b, p5b, r5b, m5b⟩ := jump1_spec hc (code_cPEnd hc) run_pend u5 (by rw [p5]; rfl)
  obtain ⟨u6a, s6a, p6a, r6a, m6a⟩ := copyPhase hc (code_cTop hc) run_top u5b (by rw [p5b]) (by norm_num)
    (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e5 : ∀ A < 2 ^ 64, u6a.getMem (BitVec.ofNat 64 A) =
      topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [m6a A hA]; unfold topMem; split
    · rw [m5b, m5 _ (by omega)]; rfl
    · rw [m5b, m5 A hA]; rfl
  obtain ⟨u6, s6, p6, x22, x18, r6, f6⟩ := idx_spec (code_cIdx hc) u6a p6a
  have hp6 : LPlanAt u6 := fun k hk => by
    rw [f6 _ (by omega) (fun h => h), e5 _ (by omega)]
    unfold topMem
    rw [if_neg (by omega), stMem_out _ _ (Or.inr (by omega))]
    exact hp k hk
  have x22' : u6.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [x22, show (96#64 : Word) = BitVec.ofNat 64 0x60 from rfl, e5 _ (by omega)]
    unfold topMem
    rw [if_neg (by omega), stMem_out _ _ (Or.inl (by omega))]
    exact hix
  have e6 : ∀ A < 2 ^ 64, u6.getMem (BitVec.ofNat 64 A) =
      topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [f6 A hA (fun h => h), e5 A hA]
  obtain ⟨u7, s7, p7, r7, m7⟩ := layer_spec hc 1 (by omega) u6 _ e6 (by rw [p6]; rfl) idx hidx x22' x18 hp6
  have hp7 : LPlanAt u7 := fun k hk => by
    rw [m7 _ (by omega), layMem_out _ 1 (by omega) idx _ (Or.inr (by unfold chDst lvDst; simp; omega)),
      ← e6 _ (by omega)]
    exact hp6 k hk
  obtain ⟨u8, s8, p8, r8, m8⟩ := layer_spec hc 2 (by omega) u7 _ m7 (by rw [p7]; rfl) idx hidx
    (by rw [r7.get (by decide), x22']) (by rw [r7.get (by decide), x18]) hp7
  have hp8 : LPlanAt u8 := fun k hk => by
    rw [m8 _ (by omega), layMem_out _ 2 (by omega) idx _ (Or.inr (by unfold chDst lvDst; simp; omega)),
      ← m7 _ (by omega)]
    exact hp7 k hk
  obtain ⟨u9, s9, p9, r9, m9⟩ := layer_spec hc 3 (by omega) u8 _ m8 (by rw [p8]; rfl) idx hidx
    (by rw [r8.get (by decide), r7.get (by decide), x22']) (by rw [r8.get (by decide), r7.get (by decide), x18]) hp8
  obtain ⟨u10, s10, p10, r10, m10⟩ := tail_spec (code_cTail hc) u9 (by rw [p9]; rfl)
  refine ⟨u10, (((((((((((((s1.trans s2a).trans s2).trans s3a).trans s3).trans s4).trans s5).trans s5b).trans
    s6a).trans s6).trans s7).trans s8).trans s9).trans s10).of_eq (by unfold layLen rowLen lvH; norm_num)
    (by unfold layLen rowLen lvH; norm_num), p10, fun A hA => ?_⟩
  rw [m10 A hA]
  unfold run2Mem tailMem
  beta_reduce
  have g : ∀ B < 2 ^ 64, u9.getMem (BitVec.ofNat 64 B) =
      layMem (layMem (layMem (topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B)))) 1 idx) 2 idx) 3 idx B := m9
  rw [g _ (by omega), g _ (by omega), g _ (by omega), g A hA]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
def zoneLay (o : Nat) : Nat := if o < 15824 then 1 else if o < 18392 then 2 else 3
def pathOut (M : Nat → Word) (lay r p : Nat) : Word :=
  if p = rootOff lay r then 1#64 else
  match (List.range (lvH lay)).find? (fun j => decide (lvHit lay r j p)) with
  | some j => M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))
  | none => 0
/-- Pairing stage 1: word `q` (from `chDst`) of a lower chain area after the pair copy and the zero fill. -/
def chOut (M : Nat → Word) (lay q : Nat) : Word :=
  if q < 2184 ∧ PairCopy.isVal (q % 104) then
    M (chSrc lay - SNAP2 + WIT + (128 * (q / 104) + PairCopy.srcOff (q % 104)))
  else if q = 2232 ∨ q = 2240 then M (chSrc lay - SNAP2 + WIT + (2688 + (q - 2184)))
  else 0
/-- Output word at staging-relative offset `o` (`WIT + o`) after the constructor's front part (pairing stage 1: top
region `[8952, 13176)`, lower regions to `20960`, staged rho/counter at `20960 .. 20984`). -/
def out2old (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 8952 then M (WIT + o)
  else if o < 13176 then M (WIT + (o - 816))
  else if o < 20960 then
    (if o - (lvDst (zoneLay o) - WIT) < pathTop (zoneLay o) then
      pathOut M (zoneLay o) (lroute (zoneLay o) idx) (o - (lvDst (zoneLay o) - WIT))
    else chOut M (zoneLay o) (o - (chDst (zoneLay o) - WIT)))
  else if o = 20960 then M WIT
  else if o = 20968 then M (WIT + 8)
  else if o = 20976 then 0
  else LoadKind.wu.fromWord (M (WIT + 16)) 0
/-- Output word at offset `o` from the final witness base `WOUT` (pairing stage 1: `WOUT = WIT + 856`; below 8096 the
P_final memory). -/
def out2 (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 8096 then stMem M (WOUT + o) else out2old M idx (o + 856)
theorem lay_consts : lvDst 1 = 0x800 + 13176 ∧ lvDst 2 = 0x800 + 15824 ∧ lvDst 3 = 0x800 + 18392 ∧
    chDst 1 = 0x800 + 13176 + 400 ∧ chDst 2 = 0x800 + 15824 + 320 ∧ chDst 3 = 0x800 + 18392 + 320 := by
  unfold lvDst chDst; decide
theorem snap_read (M : Nat → Word) (idx x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) (SNAP2 + x) = M (WIT + x) := by
  have hS : SNAP2 = 0x310000 := rfl
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
theorem lays_low (M : Nat → Word) (idx A : Nat) (hA : A < WIT + 13176) :
    (layMem (layMem (layMem M 1 idx) 2 idx) 3 idx) A = M A := by
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 2 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 1 (by omega) idx A (Or.inl (by omega))]
theorem pre_low (M : Nat → Word) (A : Nat) (hA : WIT + 13176 ≤ A) (hA' : A < WIT + 20960) (h8 : (A - WIT) % 8 = 0) :
    topMem (stMem M) A = 0 := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold topMem
  rw [if_neg (by omega)]
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem pre_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    topMem (stMem M) (SNAP2 + x) = M (WIT + x) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
set_option maxRecDepth 200000 in
theorem chMem_at (P M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4)
    (hP : ∀ x < 8 * 2729, x % 8 = 0 → P (SNAP2 + x) = M (WIT + x)) (q : Nat) (hZ : P (chDst lay + q) = 0)
    (hq : q < 2248) (h8 : q % 8 = 0) : chMem P lay (chDst lay + q) = chOut M lay q := by
  have hS : SNAP2 = 0x310000 := rfl
  have hW : WIT = 0x800 := rfl
  have hsrc : 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 ∧ chSrc lay % 8 = 0 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hso : PairCopy.srcOff (q % 104) ≤ 120 ∧ PairCopy.srcOff (q % 104) % 8 = 0 := by
    unfold PairCopy.srcOff; split_ifs <;> omega
  have key : ∀ y, chSrc lay ≤ y → y < chSrc lay + 2752 → y % 8 = 0 → P y = M (y - SNAP2 + WIT) := by
    intro y h1 h2 h3
    have := hP (y - SNAP2) (by omega) (by omega)
    rw [show SNAP2 + (y - SNAP2) = y by omega] at this
    rw [this]; apply congrArg M; omega
  unfold chMem PairCopy.pairCopyMem PairCopy.pcMem chOut
  rw [Nat.add_sub_cancel_left]
  unfold PairCopy.isVal at *
  split_ifs <;> first
    | exact hZ
    | (rw [key _ (by omega) (by omega) (by omega)]; apply congrArg M; omega)
    | omega
theorem layMem_zone (P : Nat → Word) (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx : Nat)
    (hP : ∀ x < 8 * 2729, x % 8 = 0 → P (SNAP2 + x) = M (WIT + x))
    (hZ : ∀ A, lvDst lay ≤ A → A < chDst lay + 2248 → (A - WIT) % 8 = 0 → P A = 0)
    (o : Nat) (h1 : lvDst lay - WIT ≤ o) (h2 : o < chDst lay - WIT + 2248) (h8 : o % 8 = 0) :
    layMem P lay idx (WIT + o) =
      if o - (lvDst lay - WIT) < pathTop lay then pathOut M lay (lroute lay idx) (o - (lvDst lay - WIT))
      else chOut M lay (o - (chDst lay - WIT)) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hce := chDst_eq lay
  have hD : 0x800 + 13176 ≤ lvDst lay ∧ lvDst lay % 8 = 0 ∧ lvDst lay + pathTop lay + 2248 ≤ 0x800 + 20960 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hsrc : 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 ∧ chSrc lay % 8 = 0 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hr := lroute_lt lay idx
  have hpt : pathTop lay % 16 = 0 := by unfold pathTop; split <;> omega
  have hro := rootOff_lt lay hl (lroute lay idx) hr
  unfold layMem
  by_cases hp : o - (lvDst lay - WIT) < pathTop lay
  · rw [if_pos hp]
    by_cases hrt : o - (lvDst lay - WIT) = rootOff lay (lroute lay idx)
    · unfold pathOut
      rw [if_pos (by omega), if_pos hrt]
    rw [if_neg (show ¬ WIT + o = lvDst lay + rootOff lay (lroute lay idx) by omega)]
    unfold lvsMem pathOut
    rw [if_neg hrt, if_pos (by omega), show WIT + o - lvDst lay = o - (lvDst lay - WIT) by omega]
    cases h : (List.range (lvH lay)).find? (fun j => decide (lvHit lay (lroute lay idx) j (o - (lvDst lay - WIT)))) with
    | none =>
      simp only
      rw [chMem_out _ _ _ (Or.inl (by omega))]
      exact hZ _ (by omega) (by omega) (by omega)
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      have hh : lvHit lay (lroute lay idx) j (o - (lvDst lay - WIT)) := of_decide_eq_true hp'
      unfold lvHit at hh
      have hsp := sibS_padS_lt lay (lroute lay idx) j hl hr hj
      have hm := plan_mod16 lay (lroute lay idx) j
      have hls : 0x310000 + 8136 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x310000 + 21832 ∧ lvSrc lay j % 8 = 0 := by
        unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
      have hpl : 16 * plan lay (lroute lay idx) j ≤ sibS lay (lroute lay idx) j ∧
          sibS lay (lroute lay idx) j + 16 ≤ 16 * plan lay (lroute lay idx) j + 64 ∧
          padS lay (lroute lay idx) j = 16 * plan lay (lroute lay idx) j + 32 := by
        unfold sibS padS
        have : lroute lay idx / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      rw [chMem_out _ _ _ (Or.inr (by omega))]
      have := hP (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) (by omega)
        (by omega)
      rw [show SNAP2 + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega] at this
      rw [this, show WIT + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j - SNAP2 + WIT + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega]
  · rw [if_neg hp, if_neg (show ¬ WIT + o = lvDst lay + rootOff lay (lroute lay idx) by omega),
      lvsMem_out _ lay hl _ hr _ le_rfl _ (Or.inr (by omega))]
    rw [show WIT + o = chDst lay + (o - (chDst lay - WIT)) by omega]
    exact chMem_at P M lay hl hP _ (hZ _ (by omega) (by omega) (by omega)) (by omega) (by omega)
theorem run2_zone_old (M : Nat → Word) (idx o : Nat) (hlo : 8952 ≤ o) (ho : o < 20992) (h8 : o % 8 = 0) :
    run2Mem M idx (WIT + o) = out2old M idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hTs : ∀ x < 8 * 2729, x % 8 = 0 → topMem (stMem M) (SNAP2 + x) = M (WIT + x) :=
    fun x hx h => pre_snap M x hx h
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  unfold run2Mem tailMem out2old
  by_cases ht : 20960 ≤ o
  · have hs := fun x hx h => snap_read M idx x hx h
    rcases (show o = 20960 ∨ o = 20968 ∨ o = 20976 ∨ o = 20984 by omega) with rfl | rfl | rfl | rfl
    · simp only [show ¬ (WIT + 20960 = WIT + 20984) by omega, show ¬ (WIT + 20960 = WIT + 20976) by omega,
        show ¬ (WIT + 20960 = WIT + 20968) by omega, if_false, if_true, show ¬ (20960 < 8952) by omega,
        show ¬ (20960 < 13176) by omega, show ¬ (20960 < 20960) by omega]
      have := hs 0 (by omega) (by omega); simpa using this
    · simp only [show ¬ (WIT + 20968 = WIT + 20984) by omega, show ¬ (WIT + 20968 = WIT + 20976) by omega,
        if_false, if_true, show ¬ (20968 < 8952) by omega, show ¬ (20968 < 13176) by omega,
        show ¬ (20968 < 20960) by omega, show ¬ (20968 = 20960) by omega]
      exact hs 8 (by omega) (by omega)
    · simp only [show ¬ (WIT + 20976 = WIT + 20984) by omega, if_false, if_true, show ¬ (20976 < 8952) by omega,
        show ¬ (20976 < 13176) by omega, show ¬ (20976 < 20960) by omega, show ¬ (20976 = 20960) by omega,
        show ¬ (20976 = 20968) by omega]
    · simp only [if_true, show ¬ (20984 < 8952) by omega, show ¬ (20984 < 13176) by omega,
        show ¬ (20984 < 20960) by omega, show ¬ (20984 = 20960) by omega, show ¬ (20984 = 20968) by omega,
        show ¬ (20984 = 20976) by omega, if_false]
      rw [hs 16 (by omega) (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (show ¬ o < 8952 by omega)]
    by_cases hl : o < 13176
    · rw [lays_low _ idx (WIT + o) (by omega), if_pos hl]
      unfold topMem
      rw [if_pos (by omega), show SNAP2 + 8136 + (WIT + o - (WIT + 8952)) = SNAP2 + (8136 + (o - 8952)) by omega,
        stMem_snap M _ (by omega) (by omega), show WIT + (8136 + (o - 8952)) = WIT + (o - 816) by omega]
    · rw [if_neg hl, if_pos (by omega)]
      have hZ1 : ∀ A, lvDst 1 ≤ A → A < chDst 1 + 2248 → (A - WIT) % 8 = 0 →
          topMem (stMem M) A = 0 := fun A h1 h2 h3 =>
        pre_low M A (by omega) (by omega) h3
      by_cases hz1 : o < 15824
      · have hzl : zoneLay o = 1 := by unfold zoneLay; rw [if_pos hz1]
        rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega)),
          layMem_out _ 2 (by omega) idx (WIT + o) (Or.inl (by omega))]
        exact layMem_zone (topMem (stMem M)) M 1 (by omega) idx hTs hZ1 o (by omega)
          (by omega) h8
      · have hP2 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (topMem (stMem M)) 1 idx
            (SNAP2 + x) = M (WIT + x) := fun x hx h => by
          rw [layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hTs x hx h
        have hZ2 : ∀ A, lvDst 2 ≤ A → A < chDst 2 + 2248 → (A - WIT) % 8 = 0 →
            layMem (topMem (stMem M)) 1 idx A = 0 := fun A h1 h2 h3 => by
          rw [layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
          exact pre_low M A (by omega) (by omega) h3
        by_cases hz2 : o < 18392
        · have hzl : zoneLay o = 2 := by unfold zoneLay; rw [if_neg hz1, if_pos hz2]
          rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega))]
          exact layMem_zone (layMem (topMem (stMem M)) 1 idx) M 2 (by omega) idx hP2 hZ2 o (by omega)
            (by omega) h8
        · have hzl : zoneLay o = 3 := by unfold zoneLay; rw [if_neg hz1, if_neg hz2]
          have hP3 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (layMem (topMem (stMem M))
              1 idx) 2 idx (SNAP2 + x) = M (WIT + x) := fun x hx h => by
            rw [layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hP2 x hx h
          have hZ3 : ∀ A, lvDst 3 ≤ A → A < chDst 3 + 2248 → (A - WIT) % 8 = 0 →
              layMem (layMem (topMem (stMem M)) 1 idx) 2 idx A = 0 := fun A h1 h2 h3 => by
            rw [layMem_out _ 2 (by omega) idx A (Or.inr (by omega)), layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
            exact pre_low M A (by omega) (by omega) h3
          rw [hzl]
          exact layMem_zone (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) M 3 (by omega) idx hP3 hZ3 o
            (by omega) (by omega) h8
/-- Pairing stage 1: final words below `WOUT + 20136` (the staged rho / counter ends at L3's leaf buffer + 32). -/
theorem run2_zone (M : Nat → Word) (idx o : Nat) (ho : o < 20136) (h8 : o % 8 = 0) :
    run2Mem M idx (WOUT + o) = out2 M idx o := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  unfold out2
  by_cases hl : o < 8096
  · rw [if_pos hl]
    unfold run2Mem tailMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), lays_low _ idx _ (by omega)]
    unfold topMem
    rw [if_neg (by omega)]
  · rw [if_neg hl, show WOUT + o = WIT + (o + 856) by omega]
    exact run2_zone_old M idx (o + 856) (by omega) (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand.Compact2
end


namespace ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
/-- Pairing stage 1: physical memory after the buffer pass: `43472` writes LE64(1) at 1240 (scratch below the
witness), then the layout block 48100 (`Layout.lbMem`). -/
def bufferMem (M : Nat → Word) (A : Nat) : Word :=
  if A = 1240 then 1#64 else Layout.lbMem M A

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cEntry : List (BitVec 32) := [0x34c0106f]
def cInitJ : List (BitVec 32) := [2287988847]
def cETail : List (BitVec 32) := [1052307,1305492515,25911,2634351891,2000683119]
/-- Pairing stage 1: `43953: jal 48100` (was the old buffer expansion). -/
def cInitB : List (BitVec 32) := [0x0cc0406f]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cEntry : CodeAt im (pcOf 42716) cEntry := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cInitJ : CodeAt im (pcOf 43951) cInitJ := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cETail : CodeAt im (pcOf 43472) cETail := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cInitB : CodeAt im (pcOf 43953) cInitB := codeAt_of_compact_window hc (by decide) (by decide +kernel)
end
sym_block REntry := symRun cfgC cEntry (pcOf 42716) 40
sym_block RInitJ := symRun cfgC cInitJ (pcOf 43951) 40
sym_block RETail := symRun cfgC cETail (pcOf 43472) 40
sym_block RInitB := symRun cfgC cInitB (pcOf 43953) 40
def MemEq (M N : Nat → Word) : Prop := ∀ A < 2^64, M A=N A
theorem lbS_low : ∀ k < 181, 1256 ≤ Layout.sK k := by decide
theorem lbMem_congr (M N : Nat → Word) (h : ∀ B, B ≠ 1240 → M B = N B) (A : Nat) (hA : A ≠ 1240) :
    Layout.lbMem M A = Layout.lbMem N A := by
  unfold Layout.lbMem Layout.itMem Layout.hitVal
  split_ifs with h1 h2
  · exact h _ (by omega)
  · cases hf : (List.range 181).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
    | none => rfl
    | some k =>
      have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have := lbS_low k hk
      exact h _ (by omega)
  · exact h _ hA
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
/-- Pairing stage 1: the buffer pass from 42716 to the top-path post-pass at 43500 (1 + 1 + 5 + 1 + 2275 steps). -/
theorem buffer_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2283 2283 t ∧ t.pc=pcOf 43500 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (bufferMem (fun A=>s.getMem (BitVec.ofNat 64 A))) := by
  have s0 := symRun_sound REntry (code_cEntry hc) s hpc (by simp [REntry.res, rv_simp])
  set u0 := REntry.res.toState s
  have p0 : u0.pc = pcOf 43951 := by simp [u0, REntry.res, E.eval]
  have s1 := symRun_sound RInitJ (code_cInitJ hc) u0 p0 (by simp [RInitJ.res, rv_simp])
  set u1 := RInitJ.res.toState u0
  have p1 : u1.pc = pcOf 43472 := by simp [u1, RInitJ.res, E.eval]
  have s2 := symRun_sound RETail (code_cETail hc) u1 p1 (by simp [RETail.res, rv_simp])
  set u2 := RETail.res.toState u1
  have p2 : u2.pc = pcOf 43953 := by simp [u2, RETail.res, E.eval]
  have s3 := symRun_sound RInitB (code_cInitB hc) u2 p2 (by simp [RInitB.res, rv_simp])
  set u3 := RInitB.res.toState u2
  have p3 : u3.pc = pcOf 48100 := by simp [u3, RInitB.res, E.eval]
  have m3 : ∀ B < 2 ^ 64, u3.getMem (BitVec.ofNat 64 B) = if B = 1240 then 1#64 else s.getMem (BitVec.ofNat 64 B) := by
    intro B hB
    have key := ofNat_inj hB (show 1240 < 2 ^ 64 by norm_num)
    simp only [u3, u2, u1, u0, Result.toState_getMem, RInitB.res, RETail.res, RInitJ.res, REntry.res,
      memEval_cons, memEval_nil, Addr.eval, E.eval, BitVec.add_zero, key]
  obtain ⟨t, st, pt, mt⟩ := Layout.layout_spec hc.layout u3 p3
  refine ⟨t, ((((s0.trans s1).trans s2).trans s3).trans st).of_eq (by simp [REntry.res, RInitJ.res, RETail.res,
    RInitB.res]) (by simp [REntry.res, RInitJ.res, RETail.res, RInitB.res]), pt, fun A hA => ?_⟩
  beta_reduce
  rw [mt A hA]
  unfold bufferMem
  by_cases h : A = 1240
  · subst h
    rw [if_pos rfl]
    unfold Layout.lbMem Layout.itMem
    rw [if_neg (by omega), if_neg (by omega)]
    simpa using m3 1240 (by norm_num)
  · rw [if_neg h]
    have hB : ∀ B, B ≠ 1240 → B < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 B) = s.getMem (BitVec.ofNat 64 B) :=
      fun B hb hB' => by rw [m3 B hB', if_neg hb]
    unfold Layout.lbMem Layout.itMem Layout.hitVal
    have hlt : ∀ k < 181, Layout.sK k + 16 ≤ 23008 := fun k hk => (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).2.1
    split_ifs with h1 h2
    · exact hB _ (by omega) (by omega)
    · cases hf : (List.range 181).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
      | none => rfl
      | some k =>
        have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
        have := lbS_low k hk
        have := hlt k hk
        exact hB _ (by omega) (by omega)
    · exact hB _ h hA
theorem buffer_prefix_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2283 2283 t ∧ t.pc=pcOf 43500 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (bufferMem (fun A=>s.getMem (BitVec.ofNat 64 A))) :=
  buffer_spec hc s hpc
end

def clearMem (M : Nat → Word) (dst i A : Nat) : Word :=
  if dst  ≤  A ∧ A < dst+8*i ∧ (A-dst)%8=0 then 0 else M A
/-! ### C4: the top-path post-pass (words 43500..43763, entered from the layout block's `jal 43500`)

After the buffer pass the top path area `[11000, 11768)` still holds the old layout: level `j`'s sibling at
`11704 - 64 j` (`+48` when bit `j` of the top leaf is 0). The post-pass copies the twelve siblings to a scratch
area at `0x40000`, zeroes the 768-byte area, and stores sibling `j` at slot `ppSlot leaf j` read from the plan
table (`TOPA`/`TOPB`). -/
namespace Post
def ppBit (leaf j : Nat) : Nat := leaf / 2 ^ j % 2
theorem ppBit_lt (leaf j : Nat) : ppBit leaf j < 2 := Nat.mod_lt _ (by norm_num)
/-- Old address of the level-`j` top sibling. -/
def ppOld (leaf j : Nat) : Nat := 11704 - 64 * j + 48 * (1 - ppBit leaf j)
/-- Plan slot of the level-`j` top sibling (the table byte). -/
def ppSlot (leaf j : Nat) : Nat := if j < 6 then slotA (leaf % 64) j else slotB (leaf / 64) (j - 6)
def ppNew (leaf j : Nat) : Nat := 11000 + 16 * ppSlot leaf j
def SCR : Nat := 0x40000
/-- Memory after the first `L` placements, over the memory `M` at the hook (scratch excluded). -/
def ppPlace (M : Nat → Word) (leaf : Nat) : Nat → Nat → Word
  | 0, A => if 11000 ≤ A ∧ A < 11768 ∧ (A - 11000) % 8 = 0 then 0 else M A
  | L + 1, A => if A = ppNew leaf L + 8 then M (ppOld leaf L + 8)
      else if A = ppNew leaf L then M (ppOld leaf L) else ppPlace M leaf L A
/-- Memory after the first `L` gather blocks. -/
def gMemF (M : Nat → Word) (leaf L A : Nat) : Word :=
  if SCR ≤ A ∧ A < SCR + 16 * L ∧ (A - SCR) % 8 = 0 then M (ppOld leaf ((A - SCR) / 16) + (A - SCR) % 16) else M A
theorem ppOld_lt (leaf j : Nat) : ppOld leaf j + 16 ≤ 11768 ∧ ppOld leaf j % 8 = 0 := by
  have := ppBit_lt leaf j; unfold ppOld; omega
theorem ppSlot_le (leaf j : Nat) (hj : j < 12) (hl : leaf < 4096) : ppSlot leaf j ≤ 47 := by
  unfold ppSlot
  split
  · exact (slots_ok.1 _ (Nat.mod_lt _ (by norm_num)) j (by omega)).2
  · have := slots_ok.2.1 (leaf / 64) (by omega) (j - 6) (by omega); omega
def cPost : List (BitVec 32) := [100676355,54743827,263863,218003,1307539,1295251,5479955,4428691,29590451,15927,3683520019,8261171,933507,9322243,30847011,31896611,1266579,1307539,1295251,5479955,4428691,29590451,15927,3616411155,8261171,933507,9322243,30849059,31898659,2315155,1307539,1295251,5479955,4428691,29590451,15927,3549302291,8261171,933507,9322243,64401443,65451043,3363731,1307539,1295251,5479955,4428691,29590451,15927,3482193427,8261171,933507,9322243,64403491,65453091,4412307,1307539,1295251,5479955,4428691,29590451,15927,3415084563,8261171,933507,9322243,97955875,99005475,5460883,1307539,1295251,5479955,4428691,29590451,15927,3347975699,8261171,933507,9322243,97957923,99007523,6509459,1307539,1295251,5479955,4428691,29590451,15927,3280866835,8261171,933507,9322243,131510307,132559907,7558035,1307539,1295251,5479955,4428691,29590451,15927,3213757971,8261171,933507,9322243,131512355,132561955,8606611,1307539,1295251,5479955,4428691,29590451,15927,3146649107,8261171,933507,9322243,165064739,166114339,9655187,1307539,1295251,5479955,4428691,29590451,15927,3079540243,8261171,933507,9322243,165066787,166116387,10703763,1307539,1295251,5479955,4428691,29590451,15927,3012431379,8261171,933507,9322243,198619171,199668771,11752339,1307539,1295251,5479955,4428691,29590451,15927,2945322515,8261171,933507,9322243,198621219,199670819,13751,2944763283,13879,3750102547,372771,8750483,4274384099,16780855,3087928851,66286483,3380115,8258867,6509459,3380115,8258995,537232787,13879,2944796179,344963,4428691,12813235,441987,8830723,30650403,31700003,1393539,4428691,12813235,17219203,25607939,30650403,31700003,2442115,4428691,12813235,33996419,42385155,30650403,31700003,3490691,4428691,12813235,50773635,59162371,30650403,31700003,4539267,4428691,12813235,67550851,75939587,30650403,31700003,5587843,4428691,12813235,84328067,92716803,30650403,31700003,377731,4428691,12813235,101105283,109494019,30650403,31700003,1426307,4428691,12813235,117882499,126271235,30650403,31700003,2474883,4428691,12813235,134659715,143048451,30650403,31700003,3523459,4428691,12813235,151436931,159825667,30650403,31700003,4572035,4428691,12813235,168214147,176602883,30650403,31700003,5620611,4428691,12813235,184991363,193380099,30650403,31700003,616575087,1299,115]
def cPro : List (BitVec 32) := cPost.take 3
def cG (j : Nat) : List (BitVec 32) := (cPost.drop (3 + 13 * j)).take 13
def cZs : List (BitVec 32) := (cPost.drop 159).take 4
def cZl : List (BitVec 32) := (cPost.drop 163).take 3
def cTs : List (BitVec 32) := (cPost.drop 166).take 11
def cP (j : Nat) : List (BitVec 32) := (cPost.drop (177 + 7 * j)).take 7
def cFin : List (BitVec 32) := cPost.drop 261
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cPro : CodeAt im (pcOf 43500) cPro := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZs : CodeAt im (pcOf 43659) cZs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZl : CodeAt im (pcOf 43663) cZl := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTs : CodeAt im (pcOf 43666) cTs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cG (j : Nat) (hj : j < 12) : CodeAt im (pcOf (43503 + 13 * j)) (cG j) := by
  interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cP (j : Nat) (hj : j < 12) : CodeAt im (pcOf (43677 + 7 * j)) (cP j) := by
  interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end
sym_block RPro := symRun cfgC cPro (pcOf 43500) 40
sym_block RZs := symRun cfgC cZs (pcOf 43659) 40
sym_block RZl := symRun cfgC cZl (pcOf 43663) 40
sym_block RTs := symRun cfgC cTs (pcOf 43666) 40
def gBit (j : Nat) : E := .bin .xor (.bin .and (.bin .srl (.reg .x6) (.c (BitVec.ofNat 64 j))) (.c 1#64)) (.c 1#64)
def gOff (j : Nat) : E := .bin .add (.bin .sll (gBit j) (.c 4#64)) (.bin .sll (gBit j) (.c 5#64))
def gOld (j k : Nat) : E := .bin .add (gOff j) (.c (BitVec.ofNat 64 (11704 - 64 * j + k)))
def gRes (j : Nat) : Result :=
  ⟨⟨(((RegFile.init.set .x7 (gOff j)).set .x28 (gOld j 0)).set .x29 (.ld (gOld j 0))).set .x30 (.ld (gOld j 8)),
    [(⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩, .ld (gOld j 8)),
     (⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩, .ld (gOld j 0))],
    [.valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩ 8, .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩ 8,
     .valid ⟨some (gOff j), BitVec.ofNat 64 (11704 - 64 * j + 8)⟩ 8,
     .valid ⟨some (gOff j), BitVec.ofNat 64 (11704 - 64 * j)⟩ 8]⟩,
   .c (pcOf (43503 + 13 * (j + 1))), .endOfCode, 13, 13⟩
set_option maxRecDepth 20000 in
theorem run_g (j : Nat) (hj : j < 12) : symRun cfgC (cG j) (pcOf (43503 + 13 * j)) 40 = some (gRes j) := by
  interval_cases j <;> kernel_rfl
def pRow (j : Nat) : Reg := if j < 6 then .x10 else .x11
def pSlot (j : Nat) : E := .bin .add (.bin .sll (.un (.ld .bu (j % 6)) (.ld (.reg (pRow j)))) (.c 4#64)) (.reg .x12)
def pScr (k : Nat) : E := if k = 0 then .reg .x13 else .bin .add (.reg .x13) (.c (BitVec.ofNat 64 k))
def pRes (j : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x7 (pSlot j)).set .x29 (.ld (pScr (16 * j)))).set .x30 (.ld (pScr (16 * j + 8))),
    [(⟨some (pSlot j), 8#64⟩, .ld (pScr (16 * j + 8))), (⟨some (pSlot j), 0#64⟩, .ld (pScr (16 * j)))],
    [.valid ⟨some (pSlot j), 8#64⟩ 8, .valid ⟨some (pSlot j), 0#64⟩ 8,
     .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩ 8, .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩ 8,
     .align8 (.reg (pRow j)), .valid ⟨some (.reg (pRow j)), BitVec.ofNat 64 (j % 6)⟩ 1]⟩,
   .c (pcOf (43677 + 7 * (j + 1))), .endOfCode, 7, 7⟩
set_option maxRecDepth 20000 in
theorem run_p (j : Nat) (hj : j < 12) : symRun cfgC (cP j) (pcOf (43677 + 7 * j)) 40 = some (pRes j) := by
  interval_cases j <;> kernel_rfl
end Post

namespace Post
theorem gOff_eval {s : MachineState} {leaf : Nat} (j : Nat) (hj : j < 64) (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf)
    (hl : leaf < 2 ^ 64) : (gOff j).eval s = BitVec.ofNat 64 (48 * (1 - ppBit leaf j)) := by
  have hs : (BitVec.ofNat 64 j).toNat % 64 = j := by rw [toNat_ofNat_lt (by omega)]; omega
  simp only [gOff, gBit, E.eval, BinOp.eval, h6, hs, ofNat_shr _ _ hl, ofNat_and1]
  unfold ppBit
  rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ j) with h | h <;> rw [h] <;> decide
theorem ofNat_and63 (a : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a &&& 63#64 = BitVec.ofNat 64 (a % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h63 : (63#64 : Word).toNat = 2 ^ 6 - 1 := rfl
  rw [BitVec.toNat_and, h63, toNat_ofNat_lt ha, toNat_ofNat_lt (show a % 64 < 2 ^ 64 by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod a 6
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem pro_spec (s : MachineState) (hpc : s.pc = pcOf 43500) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 43503 ∧ t.getReg .x6 = s.getMem (BitVec.ofNat 64 96) >>> 52 ∧
      t.getReg .x13 = BitVec.ofNat 64 SCR ∧ RegsExcept s t [.x6, .x13] ∧ ∀ a, t.getMem a = s.getMem a := by
  refine ⟨_, symRun_sound RPro (code_cPro hc) s hpc (by simp [RPro.res, rv_simp, accessValid_iff]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [RPro.res, rv_simp]
  · simp [RPro.res, rv_simp]
  · simp [RPro.res, rv_simp, SCR]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro a; rfl
theorem g_spec (j : Nat) (hj : j < 12) (s : MachineState) (hpc : s.pc = pcOf (43503 + 13 * j)) (leaf : Nat)
    (hl : leaf < 4096) (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (43503 + 13 * (j + 1)) ∧ RegsExcept s t [.x7, .x28, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = SCR + 16 * j + 8 then s.getMem (BitVec.ofNat 64 (ppOld leaf j + 8))
        else if A = SCR + 16 * j then s.getMem (BitVec.ofNat 64 (ppOld leaf j))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hb := ppBit_lt leaf j
  have hS : SCR = 0x40000 := rfl
  have ho := gOff_eval (s := s) j (by omega) h6 (by omega)
  have hO : ∀ k, (gOld j k).eval s = BitVec.ofNat 64 (ppOld leaf j + k) := fun k => by
    simp only [gOld, E.eval, BinOp.eval, ho, ofNat_add_ofNat]; congr 1; unfold ppOld; omega
  have hobl : (gRes j).obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho'
    simp only [gRes, List.mem_cons, List.not_mem_nil, or_false] at ho'
    rcases ho' with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ho, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ho, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
  refine ⟨_, symRun_sound (run_g j hj) (code_cG hc j hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gRes, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    have hO8 := hO 8
    have hO0 := hO 0
    rw [Nat.add_zero] at hO0
    simp only [Result.toState_getMem, gRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h13, ofNat_add_ofNat,
      hO8, hO0]
    rw [show SCR + (16 * j + 8) = SCR + 16 * j + 8 by omega]
    by_cases q1 : A = SCR + 16 * j + 8
    · rw [if_pos (by rw [q1]), if_pos q1]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h)), if_neg q1]
      by_cases q2 : A = SCR + 16 * j
      · rw [if_pos (by rw [q2]), if_pos q2]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
theorem g_loop (s : MachineState) (hpc : s.pc = pcOf 43503) (leaf : Nat) (hl : leaf < 4096)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) :
    ∀ L ≤ 12, ∃ t, Steps im s (13 * L) (13 * L) t ∧ t.pc = pcOf (43503 + 13 * L) ∧
      RegsExcept s t [.x7, .x28, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = gMemF (fun B => s.getMem (BitVec.ofNat 64 B)) leaf L A := by
  have hS : SCR = 0x40000 := rfl
  intro L
  induction L with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, by simpa using hpc, RegsExcept.refl s _, fun A _ => ?_⟩
    unfold gMemF; rw [if_neg (by omega)]
  | succ L ih =>
    intro hL
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    obtain ⟨u, su, pu, ru, mu⟩ := g_spec hc L (by omega) t pt leaf hl (by rw [rt.get (by decide)]; exact h6)
      (by rw [rt.get (by decide)]; exact h13)
    refine ⟨u, (st.trans su).of_eq (by ring) (by ring), pu, (rt.trans ru).mono (by decide), fun A hA => ?_⟩
    have hp := ppOld_lt leaf L
    rw [mu A hA]
    unfold gMemF
    by_cases q1 : A = SCR + 16 * L + 8
    · subst q1
      rw [if_pos rfl, mt _ (by omega)]
      unfold gMemF
      rw [if_neg (by omega), if_pos (by omega), show (SCR + 16 * L + 8 - SCR) / 16 = L by omega,
        show (SCR + 16 * L + 8 - SCR) % 16 = 8 by omega]
    · rw [if_neg q1]
      by_cases q2 : A = SCR + 16 * L
      · subst q2
        rw [if_pos rfl, mt _ (by omega)]
        unfold gMemF
        rw [if_neg (by omega), if_pos (by omega), show (SCR + 16 * L - SCR) / 16 = L by omega,
          show (SCR + 16 * L - SCR) % 16 = 0 by omega, Nat.add_zero]
      · rw [if_neg q2, mt A hA]
        unfold gMemF
        by_cases q3 : SCR ≤ A ∧ A < SCR + 16 * L ∧ (A - SCR) % 8 = 0
        · rw [if_pos q3, if_pos (by omega)]
        · rw [if_neg q3, if_neg (by omega)]
theorem zs_spec (s : MachineState) (hpc : s.pc = pcOf 43659) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 43663 ∧ t.getReg .x11 = BitVec.ofNat 64 11000 ∧
      t.getReg .x12 = BitVec.ofNat 64 (11000 + 8 * 96) ∧ RegsExcept s t [.x11, .x12] ∧ ∀ a, t.getMem a = s.getMem a := by
  refine ⟨_, symRun_sound RZs (code_cZs hc) s hpc (by simp [RZs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [RZs.res, rv_simp]
  · simp [RZs.res, rv_simp]
  · simp [RZs.res, rv_simp]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro a; rfl
theorem z_iter (s : MachineState) (hpc : s.pc = pcOf 43663) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (dst + 8 * (n + 1)))
    (hd : dst % 8 = 0) (hbound : dst + 8 * (n + 1) ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if n = 0 then pcOf 43666 else pcOf 43663) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 (dst + 8 * (n + 1)) ∧
      RegsExcept s t [.x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RZl (code_cZl hc) s hpc (by
    simp [RZl.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZl.res, E.eval, CmpOp.eval, BinOp.eval, h11, h12, ofNat_add_ofNat]
    have he : BitVec.ult (BitVec.ofNat 64 (dst + 8)) (BitVec.ofNat 64 (dst + 8 * (n + 1))) = decide (n ≠ 0) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dst + 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show dst + 8 * (n + 1) < 2 ^ 64 by omega)]
      simp only [decide_eq_decide]
      omega
    rw [he]
    by_cases hn : n = 0 <;> simp [hn]
  · simp [RZl.res, rv_simp, h11, ofNat_add_ofNat]
  · simp [RZl.res, rv_simp, h12]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    have key := ofNat_inj hA (show dst < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RZl.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11,
      BitVec.add_zero, key]
    rfl
theorem z_loop (s : MachineState) (hpc : s.pc = pcOf 43663) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (dst + 8 * n))
    (hn : 0 < n) (hd : dst % 8 = 0) (hbound : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3 * i) (3 * i) t ∧
      t.pc = (if i < n then pcOf 43663 else pcOf 43666) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i) ∧ t.getReg .x12 = BitVec.ofNat 64 (dst + 8 * n) ∧
      RegsExcept s t [.x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clearMem (fun B => s.getMem (BitVec.ofNat 64 B)) dst i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, by simpa [hn] using hpc, by simpa using h11, h12, RegsExcept.refl s _, ?_⟩
    intro A _; unfold clearMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, pt, t11, t12, rt, mt⟩ := ih (by omega)
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := z_iter hc t (by rw [pt, if_pos (by omega)])
      (dst + 8 * i) (n - i - 1) t11 (by rw [t12]; congr 1 <;> omega) (by omega) (by omega)
    refine ⟨u, (st.trans su).of_eq (by omega) (by omega), ?_, ?_, ?_, (rt.trans ru).mono (by decide), ?_⟩
    · rw [pu]; by_cases hz : n - i - 1 = 0
      · rw [if_pos hz, if_neg (by omega)]
      · rw [if_neg hz, if_pos (by omega)]
    · rw [u11]; congr 1 <;> omega
    · rw [u12]; congr 1 <;> omega
    · intro A hA
      rw [mu A hA, mt A hA]
      unfold clearMem
      by_cases ha : A = dst + 8 * i
      · subst A; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg ha]
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem ts_spec (s : MachineState) (hpc : s.pc = pcOf 43666) (leaf : Nat) (hl : leaf < 4096)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 43677 ∧ t.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)) ∧
      t.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)) ∧ t.getReg .x12 = BitVec.ofNat 64 11000 ∧
      RegsExcept s t [.x7, .x10, .x11, .x12, .x28] ∧ ∀ a, t.getMem a = s.getMem a := by
  have h3 : (3#64 : Word).toNat % 64 = 3 := rfl
  have h6' : (6#64 : Word).toNat % 64 = 6 := rfl
  refine ⟨_, symRun_sound RTs (code_cTs hc) s hpc (by simp [RTs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [RTs.res, rv_simp]
  · simp only [Result.toState_getReg, RTs.res, rv_simp, E.eval, BinOp.eval, h6, h3, ofNat_and63 _ (by omega : leaf < 2 ^ 64),
      ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold TOPA; omega
  · simp only [Result.toState_getReg, RTs.res, rv_simp, E.eval, BinOp.eval, h6, h3, h6',
      ofNat_shr _ _ (by omega : leaf < 2 ^ 64), ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold TOPB; omega
  · simp [RTs.res, rv_simp]
  · c_regs RTs.res
  · intro a; rfl
end
end Post

namespace Post
theorem pSlot_eval {s : MachineState} {leaf : Nat} (j : Nat) (hj : j < 12) (hl : leaf < 4096)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)))
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 11000) (ht : TopTabAt s) :
    (pSlot j).eval s = BitVec.ofNat 64 (ppNew leaf j) := by
  have h4 : (4#64 : Word).toNat % 64 = 4 := rfl
  have hw : LoadKind.bu.fromWord (s.getMem (s.getReg (pRow j))) (j % 6) = BitVec.ofNat 64 (ppSlot leaf j) := by
    unfold pRow ppSlot
    by_cases h6 : j < 6
    · simp only [h6, if_true]
      rw [h10, ht.1 _ (Nat.mod_lt _ (by norm_num)), Nat.mod_eq_of_lt h6]
      exact topA_ok _ (Nat.mod_lt _ (by norm_num)) j h6
    · simp only [h6, if_false]
      rw [h11, ht.2 _ (by omega), show j % 6 = j - 6 by omega]
      exact topB_ok _ (by omega) (j - 6) (by omega)
  simp only [pSlot, E.eval, UnOp.eval, BinOp.eval]
  rw [hw, h4, ofNat_shl, h12, ofNat_add_ofNat]
  unfold ppNew; congr 1; ring
theorem ppPlace_out (M : Nat → Word) (leaf : Nat) (hl : leaf < 4096) (L : Nat) (hL : L ≤ 12) (A : Nat)
    (hA : A < 11000 ∨ 11768 ≤ A) : ppPlace M leaf L A = M A := by
  induction L with
  | zero => unfold ppPlace; rw [if_neg (by omega)]
  | succ L ih =>
    have := ppSlot_le leaf L (by omega) hl
    unfold ppPlace; unfold ppNew
    rw [if_neg (by omega), if_neg (by omega)]
    exact ih (by omega)
theorem gMemF_scr (M : Nat → Word) (leaf L k : Nat) (hk : k < L) (d : Nat) (hd : d = 0 ∨ d = 8) :
    gMemF M leaf L (SCR + 16 * k + d) = M (ppOld leaf k + d) := by
  unfold gMemF
  rw [if_pos (by omega), show (SCR + 16 * k + d - SCR) / 16 = k by omega, show (SCR + 16 * k + d - SCR) % 16 = d by omega]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem p_spec (j : Nat) (hj : j < 12) (s : MachineState) (hpc : s.pc = pcOf (43677 + 7 * j)) (leaf : Nat)
    (hl : leaf < 4096) (h10 : s.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)))
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 11000) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) (ht : TopTabAt s) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf (43677 + 7 * (j + 1)) ∧ RegsExcept s t [.x7, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = ppNew leaf j + 8 then s.getMem (BitVec.ofNat 64 (SCR + 16 * j + 8))
        else if A = ppNew leaf j then s.getMem (BitVec.ofNat 64 (SCR + 16 * j))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hS : SCR = 0x40000 := rfl
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hsl := ppSlot_le leaf j hj hl
  have hp := pSlot_eval j hj hl h10 h11 h12 ht
  have hscr : ∀ k, (pScr k).eval s = BitVec.ofNat 64 (SCR + k) := fun k => by
    unfold pScr
    split
    · rename_i hk; subst hk; simp only [E.eval, h13, Nat.add_zero]
    · simp only [E.eval, BinOp.eval, h13, ofNat_add_ofNat]
  have hobl : (pRes j).obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho'
    simp only [pRes, List.mem_cons, List.not_mem_nil, or_false] at ho'
    rcases ho' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hp, ofNat_add_ofNat]
      exact valid8 _ (by unfold ppNew; omega) (by unfold ppNew; omega)
    · simp only [Oblig.holds, Addr.eval, hp, BitVec.add_zero]
      exact valid8 _ (by unfold ppNew; omega) (by unfold ppNew; omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, pRow]
      split
      · rw [h10, toNat_ofNat_lt (by omega)]; omega
      · rw [h11, toNat_ofNat_lt (by omega)]; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, pRow]
      split
      · rw [h10, ofNat_add_ofNat, accessValid_iff, toNat_ofNat_lt (by omega)]
        exact ⟨by omega, Nat.mod_one _⟩
      · rw [h11, ofNat_add_ofNat, accessValid_iff, toNat_ofNat_lt (by omega)]
        exact ⟨by omega, Nat.mod_one _⟩
  refine ⟨_, symRun_sound (run_p j hj) (code_cP hc j hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pRes, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | exact absurd rfl hr.1 | exact absurd rfl hr.2.1 | exact absurd rfl hr.2.2 | rfl
  · intro A hA
    have e8 := hscr (16 * j + 8)
    have e0 := hscr (16 * j)
    simp only [Result.toState_getMem, pRes, memEval_cons, memEval_nil, Addr.eval, E.eval, hp, e8, e0,
      ofNat_add_ofNat, BitVec.add_zero]
    rw [show SCR + (16 * j + 8) = SCR + 16 * j + 8 by omega]
    have hn : ppNew leaf j + 8 < 2 ^ 64 := by unfold ppNew; omega
    by_cases q1 : A = ppNew leaf j + 8
    · rw [if_pos (by rw [q1]), if_pos q1]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA hn).mp h)), if_neg q1]
      by_cases q2 : A = ppNew leaf j
      · rw [if_pos (by rw [q2]), if_pos q2]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
/-- The common post-pass: from 43500 to word 43761 (546 steps). Outside the scratch area the
memory is `ppPlace M leaf 12`. -/
theorem post_prefix_spec (s : MachineState) (hpc : s.pc = pcOf 43500) (leaf : Nat) (hl : leaf < 4096)
    (hix : s.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 leaf) (ht : TopTabAt s) :
    ∃ t, Steps im s 546 546 t ∧ t.pc = pcOf 43761 ∧
      ∀ A < 2 ^ 64, ¬ (SCR ≤ A ∧ A < SCR + 192) →
        t.getMem (BitVec.ofNat 64 A) = ppPlace (fun B => s.getMem (BitVec.ofNat 64 B)) leaf 12 A := by
  have hS : SCR = 0x40000 := rfl
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  obtain ⟨s1, h1, p1, r1, m1⟩ : ∃ t, Steps im s 0 0 t ∧ t.pc = pcOf 43500 ∧ RegsExcept s t [] ∧
      ∀ a, t.getMem a = s.getMem a := ⟨s, Steps.refl s, hpc, RegsExcept.refl s _, fun _ => rfl⟩
  obtain ⟨s2, h2, p2, x6, x13, r2, m2⟩ := pro_spec hc s1 p1
  have x6' : s2.getReg .x6 = BitVec.ofNat 64 leaf := by rw [x6, m1, hix]
  have e2 : (fun B => s2.getMem (BitVec.ofNat 64 B)) = (fun B => s.getMem (BitVec.ofNat 64 B)) :=
    funext fun B => by rw [m2, m1]
  obtain ⟨s3, h3, p3, r3, m3⟩ := g_loop hc s2 p2 leaf hl x6' x13 12 le_rfl
  rw [e2] at m3
  obtain ⟨s4, h4, p4, x11, x12, r4, m4⟩ := zs_spec hc s3 (by simpa using p3)
  obtain ⟨s5, h5, p5, y11, y12, r5, m5⟩ := z_loop hc s4 p4 11000 96 x11 x12 (by norm_num) (by norm_num) (by decide)
    96 le_rfl
  rw [if_neg (by omega)] at p5
  have x6'' : s5.getReg .x6 = BitVec.ofNat 64 leaf := by
    rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), x6']
  obtain ⟨s6, h6, p6, z10, z11, z12, r6, m6⟩ := ts_spec hc s5 p5 leaf hl x6''
  have z13 : s6.getReg .x13 = BitVec.ofNat 64 SCR := by
    rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide), x13]
  set M := fun B => s.getMem (BitVec.ofNat 64 B) with hM
  have hm6 : ∀ A < 2 ^ 64, s6.getMem (BitVec.ofNat 64 A) =
      if SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0 then gMemF M leaf 12 A else ppPlace M leaf 0 A := by
    intro A hA
    rw [m6, m5 A hA]
    unfold clearMem
    have e4 : (fun B => s4.getMem (BitVec.ofNat 64 B)) = (fun B => s3.getMem (BitVec.ofNat 64 B)) :=
      funext fun B => by rw [m4]
    rw [e4]
    unfold ppPlace
    by_cases hz : 11000 ≤ A ∧ A < 11000 + 8 * 96 ∧ (A - 11000) % 8 = 0
    · rw [if_pos hz, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg hz]
      simp only
      rw [m3 A hA]
      by_cases hs : SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0
      · rw [if_pos hs]
      · rw [if_neg hs, if_neg (by omega)]
        unfold gMemF; rw [if_neg (by omega)]
  have place : ∀ L ≤ 12, ∃ t, Steps im s6 (7 * L) (7 * L) t ∧ t.pc = pcOf (43677 + 7 * L) ∧
      RegsExcept s6 t [.x7, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0 then gMemF M leaf 12 A else ppPlace M leaf L A := by
    intro L
    induction L with
    | zero => intro _; exact ⟨s6, Steps.refl s6, by simpa using p6, RegsExcept.refl s6 _, hm6⟩
    | succ L ih =>
      intro hL
      obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
      have htt : TopTabAt t := by
        refine ⟨fun k hk => ?_, fun k hk => ?_⟩
        · rw [mt _ (by omega), if_neg (by omega), ppPlace_out M leaf hl L (by omega) _ (by omega)]
          exact ht.1 k hk
        · rw [mt _ (by omega), if_neg (by omega), ppPlace_out M leaf hl L (by omega) _ (by omega)]
          exact ht.2 k hk
      have hsl := ppSlot_le leaf L (by omega) hl
      obtain ⟨u, su, pu, ru, mu⟩ := p_spec hc L (by omega) t pt leaf hl
        (by rw [rt.get (by decide), z10]) (by rw [rt.get (by decide), z11]) (by rw [rt.get (by decide), z12])
        (by rw [rt.get (by decide), z13]) htt
      refine ⟨u, (st.trans su).of_eq (by ring) (by ring), pu, (rt.trans ru).mono (by decide),
        fun A hA => ?_⟩
      rw [mu A hA]
      by_cases q1 : A = ppNew leaf L + 8
      · rw [if_pos q1, mt _ (by omega), if_pos (by omega), gMemF_scr M leaf 12 L (by omega) 8 (Or.inr rfl)]
        rw [if_neg (by unfold ppNew at q1; omega)]
        unfold ppPlace; rw [if_pos q1]
      · rw [if_neg q1]
        by_cases q2 : A = ppNew leaf L
        · rw [if_pos q2, mt _ (by omega), if_pos (by omega)]
          have := gMemF_scr M leaf 12 L (by omega) 0 (Or.inl rfl)
          rw [Nat.add_zero, Nat.add_zero] at this
          rw [this, if_neg (by unfold ppNew at q2; omega)]
          unfold ppPlace; rw [if_neg q1, if_pos q2]
        · rw [if_neg q2, mt A hA]
          by_cases hs : SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0
          · rw [if_pos hs, if_pos hs]
          · rw [if_neg hs, if_neg hs]
            conv_rhs => unfold ppPlace
            rw [if_neg q1, if_neg q2]
  obtain ⟨s7, h7, p7, r7, m7⟩ := place 12 le_rfl
  refine ⟨s7, (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))).of_eq
    (by norm_num) (by norm_num), by simpa using p7, fun A hA hn => ?_⟩
  rw [m7 A hA, if_neg (by omega)]

end
end Post

namespace Post
theorem ppSlot_inj (leaf : Nat) (hl : leaf < 4096) (j L : Nat) (hj : j < 12) (hL : L < 12)
    (h : ppSlot leaf j = ppSlot leaf L) : j = L := by
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hr' : leaf / 64 < 64 := by omega
  unfold ppSlot at h
  by_cases h6 : j < 6 <;> by_cases h6' : L < 6
  · rw [if_pos h6, if_pos h6'] at h; exact slots_ok.2.2.1 _ hr j h6 L h6' h
  · rw [if_pos h6, if_neg h6'] at h
    have := (slots_ok.1 _ hr j h6).1; have := slots_ok.2.1 _ hr' (L - 6) (by omega); omega
  · rw [if_neg h6, if_pos h6'] at h
    have := (slots_ok.1 _ hr L h6').1; have := slots_ok.2.1 _ hr' (j - 6) (by omega); omega
  · rw [if_neg h6, if_neg h6'] at h
    have := slots_ok.2.2.2 _ hr' (j - 6) (by omega) (L - 6) (by omega) h; omega
/-- A placed sibling: the word `d ∈ {0, 8}` of slot `ppSlot leaf j` holds the old sibling's word. -/
theorem ppPlace_hit (M : Nat → Word) (leaf : Nat) (hl : leaf < 4096) (j : Nat) (hj : j < 12) (d : Nat)
    (hd : d = 0 ∨ d = 8) : ppPlace M leaf 12 (ppNew leaf j + d) = M (ppOld leaf j + d) := by
  have key : ∀ L, j < L → L ≤ 12 → ppPlace M leaf L (ppNew leaf j + d) = M (ppOld leaf j + d) := by
    intro L
    induction L with
    | zero => intro h; omega
    | succ L ih =>
      intro h1 h2
      unfold ppPlace
      by_cases hL : L = j
      · subst hL
        rcases hd with rfl | rfl
        · rw [if_neg (by omega), if_pos (by omega), Nat.add_zero]
        · rw [if_pos rfl]
      · have hne : ppSlot leaf j ≠ ppSlot leaf L := fun h => hL (ppSlot_inj leaf hl j L hj (by omega) h).symm
        unfold ppNew
        rw [if_neg (by omega), if_neg (by omega)]
        exact ih (by omega) (by omega)
  exact key 12 hj le_rfl
/-- An unplaced word of the area is zero. -/
theorem ppPlace_miss (M : Nat → Word) (leaf : Nat) (q : Nat) (hq : q < 96)
    (hm : ∀ j < 12, ¬ (16 * ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * ppSlot leaf j + 16)) :
    ppPlace M leaf 12 (11000 + 8 * q) = 0 := by
  have key : ∀ L ≤ 12, ppPlace M leaf L (11000 + 8 * q) = 0 := by
    intro L
    induction L with
    | zero => intro _; unfold ppPlace; rw [if_pos (by omega)]
    | succ L ih =>
      intro hL
      have := hm L (by omega)
      unfold ppPlace; unfold ppNew
      rw [if_neg (by omega), if_neg (by omega)]
      exact ih (by omega)
  exact key 12 le_rfl
end Post
namespace Post
theorem ppPlace_congr (M M' : Nat → Word) (h : ∀ B < 2 ^ 64, M B = M' B) (leaf : Nat) (hl : leaf < 4096) :
    ∀ L ≤ 12, ∀ A < 2 ^ 64, ppPlace M leaf L A = ppPlace M' leaf L A := by
  intro L
  induction L with
  | zero => intro _ A hA; unfold ppPlace; split_ifs <;> first | rfl | exact h A hA
  | succ L ih =>
    intro hL A hA
    have := ppOld_lt leaf L
    unfold ppPlace
    split_ifs
    · exact h _ (by omega)
    · exact h _ (by omega)
    · exact ih (by omega) A hA
end Post
/-- Pairing stage 1: the buffer pass (layout block), then the top-path post-pass (2283 + 546 steps, to 43761). -/
theorem bufferPost_prefix_spec {im : Image} (hc : CompactCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 42716)
    (leaf : Nat) (hl : leaf < 4096) (hix : s.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 leaf)
    (ht : TopTabAt s) :
    ∃ t, Steps im s 2829 2829 t ∧ t.pc = pcOf 43761 ∧
      ∀ A < 2 ^ 64, ¬ (Post.SCR ≤ A ∧ A < Post.SCR + 192) →
        t.getMem (BitVec.ofNat 64 A) = Post.ppPlace (bufferMem (fun B => s.getMem (BitVec.ofNat 64 B))) leaf 12 A := by
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  obtain ⟨q, sq, pq, mq0⟩ := buffer_spec hc s hpc
  have mq : ∀ A < 2 ^ 64, q.getMem (BitVec.ofNat 64 A) = bufferMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => mq0 A hA
  have hout : ∀ A, A < 23008 ∨ 26144 ≤ A → A ≠ 1240 → bufferMem (fun B => s.getMem (BitVec.ofNat 64 B)) A =
      s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    unfold bufferMem Layout.lbMem Layout.itMem
    rw [if_neg h1]
    split_ifs with h2 h3 <;> first | rfl | omega
  have hq96 : q.getMem (BitVec.ofNat 64 96) = s.getMem (BitVec.ofNat 64 96) := by
    rw [mq 96 (by norm_num), hout 96 (by omega) (by omega)]
  have hqt : TopTabAt q := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [mq _ (by omega), hout _ (by omega) (by omega)]; exact ht.1 k hk
    · rw [mq _ (by omega), hout _ (by omega) (by omega)]; exact ht.2 k hk
  obtain ⟨t, st, pt, mt⟩ := Post.post_prefix_spec hc q pq leaf hl (by rw [hq96]; exact hix) hqt
  refine ⟨t, (sq.trans st).of_eq (by norm_num) (by norm_num), pt, fun A hA hn => ?_⟩
  rw [mt A hA hn]
  exact Post.ppPlace_congr _ _ (fun B hB => mq B hB) leaf hl 12 le_rfl A hA

end ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
