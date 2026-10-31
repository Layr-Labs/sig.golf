import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge078
import SigGolfCandidate.Merge079

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Final ====
section

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
/-- Nested FTS (r1-1): hold placement of coordinate `c` stores its top sibling at `hdst c + 144 flag` (r3w: store
immediates `-48 (6 - c)` for `c < 6`; the FTS content of these slots is dead, zeroed by the finish pass). -/
def hdst (c : Nat) : Nat := 8384 - 896 * c - 48 * (6 - c)
def hfE (c : Nat) : E := E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 16)))
def hbE (c : Nat) : E := .bin .add (.bin .sll (hfE c) (.c 7#64)) (.bin .sll (hfE c) (.c 4#64))
def holdRegs (c : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (.c (BitVec.ofNat 64 (8384 - 896 * c)))).set .x13
    (.bin .add (hbE c) (.c (BitVec.ofNat 64 (8384 - 896 * c))))).set .x28 (.c 0x380000#64)).set .x29
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
      SigGolfCandidate.T3.height L = lvH lay → (∀ i, plan lay r i = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan L r).getD i 0) →
      sibS lay r j ≠ sibS lay r j' ∧ sibS lay r j ≠ padS lay r j' ∧ padS lay r j ≠ padS lay r j' := by
    intro L hL hL0 hH hP
    have hr' : r < 2 ^ SigGolfCandidate.T3.height L := by rw [hH]; exact hr
    have hj1 : j < SigGolfCandidate.T3.height L := by rw [hH]; exact hj
    have hj2 : j' < SigGolfCandidate.T3.height L := by rw [hH]; exact hj'
    have d1 := ClaudeWCT.W9.Machine.Expand.OldW.lower_sib_disjoint L hL0 r hr' j hj1 j' hj2 hne
    have d2 := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_disjoint L hL0 r hr' j' hj2 j hj1
    have d3 := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_pad_disjoint L hL0 r hr' j hj1 j' hj2 hne
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at d1 d2
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
  obtain ⟨u2, s2, p2, r2, m2⟩ := ClaudeWCT.W9.Machine.Expand.Compact.zero_spec hc u2a p2a WZ 3124 42154 x11 x12 x1 (by norm_num) (by norm_num)
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
theorem lbS_low : ∀ k < 180, 1256 ≤ Layout.sK k := by decide
theorem lbMem_congr (M N : Nat → Word) (h : ∀ B, B ≠ 1240 → M B = N B) (A : Nat) (hA : A ≠ 1240) :
    Layout.lbMem M A = Layout.lbMem N A := by
  unfold Layout.lbMem Layout.itMem Layout.hitVal
  split_ifs with h1 h2
  · exact h _ (by omega)
  · cases hf : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
    | none => rfl
    | some k =>
      have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have := lbS_low k hk
      exact h _ (by omega)
  · exact h _ hA
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
/-- Pairing stage 1: the buffer pass from 42716 to the top-path post-pass at 43500 (1 + 1 + 5 + 1 + 2287 steps). -/
theorem buffer_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2295 2295 t ∧ t.pc=pcOf 43500 ∧
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
    have hlt : ∀ k < 180, Layout.sK k + 16 ≤ 23008 := fun k hk => (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).2.1
    split_ifs with h1 h2
    · exact hB _ (by omega) (by omega)
    · cases hf : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
      | none => rfl
      | some k =>
        have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
        have := lbS_low k hk
        have := hlt k hk
        exact hB _ (by omega) (by omega)
    · exact hB _ h hA
theorem buffer_prefix_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2295 2295 t ∧ t.pc=pcOf 43500 ∧
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
/-- Pairing stage 1: the buffer pass (layout block), then the top-path post-pass (2295 + 546 steps, to 43761). -/
theorem bufferPost_prefix_spec {im : Image} (hc : CompactCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 42716)
    (leaf : Nat) (hl : leaf < 4096) (hix : s.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 leaf)
    (ht : TopTabAt s) :
    ∃ t, Steps im s 2841 2841 t ∧ t.pc = pcOf 43761 ∧
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
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Wit ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer height chainCount LayerSignature route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap window_flatMap_const
  window_full window_zeros window_take zeros wordsOf layerBytes layerBytes_length layerBytes_merkle layerBytes_chain)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand.OldW (headerBytes wctBytes regionBytes layerRegion tailBytes lowerPathBytes headerBytes_length
  regionBytes_length regionLen regionCell regionCell_length
  wct_prefix wctBytes_length layers_length tailBytes_length)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 layerRegionV6 layerBytesBCV6 bcTopBlockV6 wctBytesV6_length
  witListV6_length layerRegionV6_length layersV6_length headerBytesV5 headerBytesV5_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
open ClaudeWCT.W9.Machine.Expand.OldW (pathSlots layerBase layerBase_ge layerEnd_le layerRegion_length layer_prefix)
theorem window_window' (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem v6_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (headerBytesV5 w) o 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega)]
def layOffV6 (lay : Layer) : Nat := (![0, 4224, 7424, 10560] : Layer → Nat) lay
theorem v6_layer (lay : Layer) (j : Nat) (hj : j + 8 ≤ 64 * (height lay + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 lay)) :
    window (witListV6 N w) (8136 + layOffV6 lay + j) 8 = window (layerRegionV6 N w lay) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega), wctBytesV6_length,
    window_append_right (zeros 8) _ _ _ (by simp [zeros]; omega), show (zeros 8).length = 8 by simp [zeros]]
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegionV6 N w) lay.val (by simp) j 8
    (by rw [hlen, layerRegionV6_length]; omega)
  have hpre : (((List.finRange 4).take lay.val).map fun l => (layerRegionV6 N w l).length).sum = layOffV6 lay := by
    simp only [layerRegionV6_length]
    fin_cases lay <;> decide
  rw [hpre, hlen] at key
  rw [show 8136 + layOffV6 lay + j - 64 - 8064 - 8 = layOffV6 lay + j by omega, key]

end
section lower
variable {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32)
def canon (j : Fin (height lay)) (d : Nat) : List UInt8 :=
  if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) then window (bytesLE 16 (ls.path j)) 0 8
  else if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 then window (bytesLE 16 (ls.path j)) 8 8
  else if d = 32 ∧ j.val = height lay - 1 then bytesLE 4 ctr ++ zeros 4
  else zeros 8
theorem sibOff_vals (b : Nat) : SigGolfCandidate.T3M.sibOff b = 0 ∨ SigGolfCandidate.T3M.sibOff b = 48 := by
  unfold SigGolfCandidate.T3M.sibOff; split <;> simp
theorem win8_of_16 (L : List UInt8) (x a : Nat) (ha : a + 8 ≤ 16) :
    window L (x + a) 8 = window (window L x 16) a 8 := (window_window' L x 16 a 8 ha).symm
theorem block_win (P : List UInt8) (hP : P.length = 16) (b : Bool) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64) :
    window (if b then P ++ zeros 48 else zeros 48 ++ P) d 8 =
      if d = (if b then 0 else 48) then window P 0 8 else if d = (if b then 0 else 48) + 8 then window P 8 8
      else zeros 8 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    by_cases h48 : 48 ≤ d
    · rw [window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros]]
      rcases (show d = 48 ∨ d = 56 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
  · simp only [if_true]
    by_cases h16 : d < 16
    · rw [window_append_left _ _ _ _ (by rw [hP]; omega)]
      rcases (show d = 0 ∨ d = 8 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_right _ _ _ _ (by rw [hP]; omega), hP, window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
end lower
section lowerAB
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_drop (L : List UInt8) (k x n : Nat) : window (L.drop k) x n = window L (k + x) n := by
  unfold window; rw [List.drop_drop]
theorem v6_block (j : Fin (height lay)) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (layerBytesBCV6 lay leaf ls ctr) (64 * (height lay - 1 - j.val) + d) 8 = canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  unfold layerBytesBCV6
  by_cases htop : j.val = height lay - 1
  · rw [show 64 * (height lay - 1 - j.val) + d = d by rw [htop]; simp,
      window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega)]
    have hT : WCT9.topLevel lay = j := Fin.ext (by unfold WCT9.topLevel; simp [htop])
    unfold bcTopBlockV6 canon
    rw [hT, ← htop]
    unfold SigGolfCandidate.T3M.sibOff at hdv ⊢
    split
    · rename_i hb
      simp only [hb, if_true] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (0 : Nat) + 8 = 8 from rfl, show (8 : Nat) ≠ 0 by decide, if_true, if_false]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (32 : Nat) ≠ 0 by decide, show (32 : Nat) ≠ 0 + 8 by decide, if_false, true_and, if_true]
        rw [show bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28 =
          (bytesLE 16 (ls.path j) ++ zeros 16) ++ (bytesLE 4 ctr ++ zeros 28) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 32 - (bytesLE 16 (ls.path j) ++ zeros 16).length = 0 by simp [zeros, bytesLE_length]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 0 by decide, show (40 : Nat) ≠ 0 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
    · rename_i hb
      simp only [hb, if_false] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 0 by simp [zeros, bytesLE_length]]
      · simp only [show (48 : Nat) + 8 ≠ 48 by decide, if_true, if_false]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 + 8 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 8 by simp [zeros, bytesLE_length]]
      · simp only [show (32 : Nat) ≠ 48 by decide, show (32 : Nat) ≠ 48 + 8 by decide, if_false, true_and, if_true]
        rw [show zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j) =
          zeros 32 ++ (bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j)) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros]), show 32 - (zeros 32).length = 0 by simp [zeros]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 48 by decide, show (40 : Nat) ≠ 48 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (zeros 32 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
  · have hjl : j.val + 1 < height lay := by omega
    rw [window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
      ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
      show 64 + (64 * (height lay - 1 - j.val) + d - 64) = 64 * (height lay - 1 - j.val) + (d - d % 16) + d % 16 by
        omega,
      win8_of_16 _ _ _ (by omega), layerBytes_merkle lay leaf ls j (d - d % 16) (by omega),
      window_window' _ _ _ _ _ (by omega), show d - d % 16 + d % 16 = d by omega]
    have hbk := block_win (bytesLE 16 (ls.path j)) (bytesLE_length _ _) (decide (leaf / 2 ^ j.val % 2 = 1)) d hd hd'
    simp only [decide_eq_true_eq] at hbk
    rw [hbk]
    unfold canon SigGolfCandidate.T3M.sibOff
    by_cases hb : leaf / 2 ^ j.val % 2 = 1
    · simp only [hb, if_true]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
    · simp only [hb, if_false]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
end lowerAB
section lowerBC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_split (L : List UInt8) (o a b : Nat) :
    window L o (a + b) = window L o a ++ window L (o + a) b := by
  unfold window
  rw [List.take_add, List.drop_drop]
include hlay hleaf
theorem v7_block (j : Fin (height lay)) (d : Nat) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + d) 8 =
      canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  have hsib := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_sib hlay hleaf ls ctr j
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at hsib
  unfold canon
  rcases hdv with h | h | h | h
  · subst h
    rw [if_pos rfl, show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) = 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 0 from rfl, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_pos rfl, show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      (SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8) = 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 by omega, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · rw [if_pos ⟨rfl, htop⟩]
      have hc := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_ctr hlay hleaf ls ctr
      have hr := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot at hc hr
      rw [← htop] at hc hr
      rw [show (8 : Nat) = 4 + 4 from rfl, window_split, hc,
        show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 =
          16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 0 from rfl,
        ← window_window' _ _ 12 0 4 (by omega), hr, window_zeros _ _ _ (by omega)]
    · rw [if_neg (by omega)]
      have hp := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 =
        16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 0 from rfl, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · have hr := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot at hr
      rw [← htop] at hr
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40 =
          16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 4 by omega,
        ← window_window' _ _ 12 4 8 (by omega), hr, window_zeros _ _ _ (by omega)]
    · have hp := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40 =
        16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 8 by omega, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
end lowerBC
section lowerC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
include hlay hleaf
theorem v7_free (p : Nat) (hp8 : p % 8 = 0) (hp' : p + 8 ≤ 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay)
    (hnot : ∀ j : Fin (height lay), p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val ∧
      p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val + 8 ∧
      p ≠ 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 ∧
      p ≠ 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40)
    (hhi : p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot lay leaf) :
    window (lowerPathBytes lay leaf ls ctr) p 8 = zeros 8 := by
  have hsl : ∀ j : Fin (height lay), ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val % 16 = 0 := fun j => by
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot
    rcases sibOff_vals (leaf / 2 ^ j.val % 2) with h | h <;> rw [h] <;> omega
  have hh : 1 ≤ height lay := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' lay
  unfold lowerPathBytes
  rw [ClaudeWCT.W9.Machine.Expand.OldW.window_map_range _ _ _ _ hp']
  have hz : ∀ i ∈ List.range 8, ClaudeWCT.W9.Machine.Expand.OldW.lowerPathByte lay leaf ls ctr (p + i) = (fun _ => (0 : UInt8)) i := by
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathByte_free ls ctr (fun j => by
      have := hnot j; have := hsl j; omega)]
    have hc := hnot ⟨height lay - 1, by omega⟩
    simp only at hc
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot at hhi ⊢
    rw [if_neg (by omega), if_neg (by omega)]
  rw [List.map_congr_left hz]
  simp [zeros, List.map_const']
end lowerC
theorem wordsOf_getD' (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [SigGolfCandidate.T3M.wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := SigGolfCandidate.T3M.readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
section ident
variable (N : HashOutput) (w : WCT9.Witness)
def v6M (B : Nat) : Word := (wordsOf (witListV6 N w)).getD ((B - WIT) / 8) 0
theorem v6M_eq (x : Nat) (hx : x % 8 = 0) (hx' : x + 8 ≤ 21832) :
    v6M N w (WIT + x) = BitVec.ofNat 64 (readLE (window (witListV6 N w) x 8)) := by
  unfold v6M
  rw [show (WIT + x - WIT) / 8 = x / 8 by omega, wordsOf_getD' _ 2729 (by rw [witListV6_length]) _ (by omega),
    show 8 * (x / 8) = x by omega]
theorem lroute_eq (lay : Layer) (hl : lay.val ≠ 0) (idx : Nat) :
    lroute lay.val idx = (route idx lay).1 := by
  unfold lroute route
  fin_cases lay <;> simp_all [height]
theorem plan_eq (lay : Layer) (r j : Nat) : plan lay.val r j = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay r).getD j 0 := by
  unfold plan; congr 2; ext; simp [Nat.mod_eq_of_lt lay.isLt]
theorem lvSrc_eq (lay : Layer) (hl : lay.val ≠ 0) (j : Nat) (hj : j < height lay) :
    lvSrc lay.val j - SNAP2 = 8136 + layOffV6 lay + 64 * (height lay - 1 - j) := by
  unfold lvSrc SNAP2 layOffV6
  fin_cases lay <;> simp_all [height] <;> omega
theorem lvH_eq (lay : Layer) (hl : lay.val ≠ 0) : lvH lay.val = height lay := by
  unfold lvH; fin_cases lay <;> simp_all [height]
theorem lvDst_eq (lay : Layer) (hl : lay.val ≠ 0) : lvDst lay.val - WIT = ClaudeWCT.W9.Machine.Expand.OldW.layerBase lay + 856 ∧
    pathTop lay.val = 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay ∧
    chDst lay.val - WIT = ClaudeWCT.W9.Machine.Expand.OldW.layerBase lay + 856 + 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay ∧
    chSrc lay.val - SNAP2 = 8136 + layOffV6 lay + 64 * height lay := by
  unfold chDst chSrc pathTop
  unfold lvDst WIT SNAP2 layOffV6 ClaudeWCT.W9.Machine.Expand.OldW.layerBase ClaudeWCT.W9.Machine.Expand.OldW.pathSlots
  fin_cases lay <;> simp_all [height]
end ident
theorem wu_small (X : Nat) (hX : X < 2 ^ 32) : LoadKind.wu.fromWord (BitVec.ofNat 64 X) 0 = BitVec.ofNat 64 X := by
  apply BitVec.eq_of_toNat_eq
  simp only [LoadKind.fromWord, extractWord32, Nat.zero_div, Nat.zero_mul, BitVec.ushiftRight_zero,
    BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : X < 2 ^ 64), Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt (by omega : X < 2 ^ 64)]
section ident2
variable (N : HashOutput) (w : WCT9.Witness)
/-- C4: past the 768-byte path area the top region holds the chain blocks in both layouts. -/
theorem layerRegion_top_tail (p : Nat) (hp : 768 ≤ p) (n : Nat) :
    window (layerRegion N w 0) p n = window (layerRegionV6 N w 0) p n := by
  unfold layerRegion layerRegionV6 ClaudeWCT.W9.Machine.Expand.layerBytesV6
  have h63 : 64 * (height (0 : Layer) + chainCount (0 : Layer)) = 4032 := rfl
  have htl : ((layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)).take 768).length = 768 := by
    rw [List.length_take, layerBytes_length, h63]; omega
  rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos (show (0 : Layer).val = 0 from rfl),
    if_pos (show (0 : Layer).val = 0 from rfl), List.append_assoc,
    window_append_right (ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes _ _) _ _ _
      (by rw [ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes_length]; exact hp),
    window_append_right (List.take 768 _) _ _ _ (by rw [htl]; exact hp),
    ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes_length, htl, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots_top,
    ClaudeWCT.W9.Machine.Expand.OldW.height_top]
theorem rootOff_eq_hi (L : Layer) (hL : L.val ≠ 0) (idx : Nat) :
    rootOff L.val (lroute L.val idx) = ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot L (route idx L).1 := by
  unfold rootOff ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot
  rw [plan_eq, lroute_eq L hL]
  congr 3
  unfold rootJ; fin_cases L <;> simp_all [height]
end ident2
theorem ofNat_readLE_zeros8 : BitVec.ofNat 64 (readLE (zeros 8)) = 0 := by decide
section chainarea
variable (N : HashOutput) (w : WCT9.Witness)
theorem lower_cc (L : Layer) (hL : L.val ≠ 0) : chainCount L = 43 := by
  fin_cases L <;> simp_all [chainCount]
theorem lower_area (L : Layer) (hL : L.val ≠ 0) : ClaudeWCT.W9.Machine.Expand.OldW.chainArea L = 2248 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.chainArea; rw [if_neg hL]
/-- Pairing stage 1: the value of chain `42 - b` (staging chain block `b`) as staged at `WIT`. -/
theorem v6_chainval (L : Layer) (hL : L.val ≠ 0) (b : Nat) (hb : b < 43) (d : Nat) (hd : d = 0 ∨ d = 8) :
    v6M N w (WIT + (8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d))) =
      BitVec.ofNat 64 (readLE (window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue (w.signature.layers L) (42 - b))) d 8)) := by
  have hcc := lower_cc L hL
  have hcs := ClaudeWCT.W9.Machine.Expand.chainSlotsV6_lower L hL
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hh1 := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' L
  rw [v6M_eq N w _ (by omega) (by omega),
    show 8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d) =
      8136 + layOffV6 L + (64 * height L + (64 * b + 48 + d)) by omega,
    v6_layer N w L _ (by omega)]
  unfold layerRegionV6 layerBytesBCV6
  rw [if_neg hL, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
    ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
    show 64 + (64 * height L + (64 * b + 48 + d) - 64) =
      (64 * height L + 64 * (chainCount L - 1 - (42 - b)) + 48) + d by rw [hcc]; omega,
    win8_of_16 _ _ _ (by omega),
    SigGolfCandidate.T3M.layerBytes_chain L _ _ ⟨42 - b, by omega⟩ 48 (by omega),
    window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _)]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lsValue
  rw [dif_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of a pair block of a lower chain area. -/
theorem lc_word {lay : Layer} (ls : LayerSignature lay) (m r : Nat) (hm : m < 21) (hr : r < 104) (h8 : r % 8 = 0) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes ls) (104 * m + r) 8 =
      if r = 16 ∨ r = 24 then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1))) (r - 16) 8
      else if r = 88 ∨ r = 96 then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 2))) (r - 88) 8
      else zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes
  rw [List.append_assoc, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]; omega),
    window_flatMap_const _ _ 104 (ClaudeWCT.W9.Machine.Expand.OldW.pairBytes_length ls) m (by simp; omega) r 8 (by omega)]
  have hidx : ((List.range 21).reverse)[m]'(by simp <;> omega) = 20 - m := by simp <;> omega
  rw [hidx]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.pairBytes
  by_cases h1 : r < 16
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega), window_zeros _ _ _ (by omega),
      if_neg (by omega), if_neg (by omega)]
  by_cases h2 : r < 32
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 16).length = 16 by simp [zeros],
      if_pos (by omega)]
  by_cases h3 : r < 88
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1))).length = 32 by
        simp [zeros, bytesLE_length],
      window_zeros _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1)) ++ zeros 56).length = 88 by
        simp [zeros, bytesLE_length],
      if_neg (by omega), if_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of chain 0's block at the end of a lower chain area. -/
theorem lc_tail {lay : Layer} (ls : LayerSignature lay) (q : Nat) (h1 : 2184 ≤ q) (h2 : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes ls) q 8 =
      if 2232 ≤ q then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls 0)) (q - 2232) 8 else zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes
  rw [List.append_assoc, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]; omega),
    ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]
  by_cases h : 2232 ≤ q
  · rw [if_pos h, window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros],
      show q - 2184 - 48 = q - 2232 by omega]
  · rw [if_neg h, window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega)]
/-- Pairing stage 1: the pair copy + zero fill rebuilds the witness's lower chain area. -/
theorem chOut_eq (L : Layer) (hL : L.val ≠ 0) (q : Nat) (hq : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    chOut (v6M N w) L.val q =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes (w.signature.layers L)) q 8)) := by
  obtain ⟨_, _, _, e4⟩ := lvDst_eq L hL
  have hS : ∀ s, chSrc L.val - SNAP2 + WIT + s = WIT + (8136 + layOffV6 L + 64 * height L + s) := by
    intro s; omega
  unfold chOut
  by_cases hlo : q < 2184
  · obtain ⟨m, r, hm, hr, rfl⟩ : ∃ m r, m < 21 ∧ r < 104 ∧ q = 104 * m + r :=
      ⟨q / 104, q % 104, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
    have hr8 : r % 8 = 0 := by omega
    rw [lc_word _ m r hm hr hr8, show (104 * m + r) / 104 = m by omega, show (104 * m + r) % 104 = r by omega]
    unfold PairCopy.isVal PairCopy.srcOff
    by_cases hv : r = 16 ∨ r = 24 ∨ r = 88 ∨ r = 96
    · rw [if_pos ⟨hlo, hv⟩, hS]
      rcases hv with rfl | rfl | rfl | rfl
      · rw [if_pos rfl, if_pos (Or.inl rfl), show 128 * m + 112 = 64 * (2 * m + 1) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_pos rfl, if_pos (Or.inr rfl), show 128 * m + 120 = 64 * (2 * m + 1) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos (Or.inl rfl),
          show 128 * m + 48 = 64 * (2 * m) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inr rfl),
          show 128 * m + 56 = 64 * (2 * m) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
    · rw [if_neg (fun h => hv h.2), if_neg (by omega), if_neg (by omega), if_neg (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (fun h => hlo h.1), lc_tail _ q (by omega) hq h8]
    by_cases ht : 2232 ≤ q
    · rw [if_pos (by omega), if_pos ht, hS,
        show 2688 + (q - 2184) = 64 * 42 + 48 + (q - 2232) by omega,
        v6_chainval N w L hL 42 (by omega) _ (by omega)]
    · rw [if_neg (by omega), if_neg ht, ofNat_readLE_zeros8]
end chainarea
section ident3
variable (N : HashOutput) (w : WCT9.Witness)
/-- Pairing stage 1: a word of a lower layer region of the final witness after the second pass. -/
theorem zone_low (L : Layer) (hL : L.val ≠ 0) (o : Nat) (h1 : ClaudeWCT.W9.Machine.Expand.OldW.layerBase L ≤ o)
    (h2 : o + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + (16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L + 2248))
    (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)) =
      if o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L < 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L then
        pathOut (v6M N w) L.val (lroute L.val (WCT9.digestIndex N)) (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L)
      else chOut (v6M N w) L.val (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L) := by
  have hW : WIT = 0x800 := rfl
  set leaf := (route (WCT9.digestIndex N) L).1 with hleafdef
  have hleaf : leaf < 2 ^ height L := ClaudeWCT.W9.Machine.Expand.OldW.route_leaf_lt _ _
  have hps : 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L ≤ 16 * 25 ∧ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L % 8 = 0 ∧
      ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L ≥ 20 := by
    fin_cases L <;> simp_all [ClaudeWCT.W9.Machine.Expand.OldW.pathSlots, ClaudeWCT.W9.Machine.Expand.OldW.layerBase]
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hcs := ClaudeWCT.W9.Machine.Expand.chainSlotsV6_lower L hL
  have hh1 := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' L
  have harea := lower_area L hL
  rw [show o = ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) by omega,
    ClaudeWCT.W9.Machine.Expand.OldW.win_layerRegion N w L _ 8 (by omega), Nat.add_sub_cancel_left]
  unfold layerRegion
  rw [if_neg hL]
  by_cases hp : o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L < 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L
  · rw [if_pos hp, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length]; omega)]
    unfold pathOut
    have hro := rootOff_eq_hi L hL (WCT9.digestIndex N)
    rw [← hleafdef] at hro
    by_cases hrt : o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L = rootOff L.val (lroute L.val (WCT9.digestIndex N))
    · rw [if_pos hrt, hrt, hro, ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_hi hL hleaf]
      decide
    rw [if_neg hrt]
    rw [lroute_eq L hL, ← hleafdef]
    cases h : (List.range (lvH L.val)).find? (fun j => decide (lvHit L.val leaf j (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L)))
      with
    | none =>
      simp only
      rw [v7_free hL hleaf _ _ _ (by omega) (by omega) (fun j => by
        have := List.find?_eq_none.mp h j.val (List.mem_range.mpr (by rw [lvH_eq L hL]; exact j.isLt))
        have h' : ¬ lvHit L.val leaf j.val (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) := fun hh => this (decide_eq_true hh)
        unfold lvHit sibS padS at h'
        rw [plan_eq] at h'
        unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot
        rw [sibOff_eq _ (Nat.mod_lt _ (by norm_num))]
        omega) (fun hh => hrt (by rw [hh, ← hro, lroute_eq L hL]))]
      simp [zeros]; rfl
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      rw [lvH_eq L hL] at hj
      have hh : lvHit L.val leaf j (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) := of_decide_eq_true hp'
      unfold lvHit sibS padS at hh
      rw [plan_eq] at hh
      set pj := (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan L leaf).getD j 0 with hpj
      have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hsb := sibOff_eq (leaf / 2 ^ j % 2) hb
      have hpbnd := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_bound L hL leaf hleaf j hj
      have hsbnd := ClaudeWCT.W9.Machine.Expand.OldW.lower_sib_bound L hL leaf hleaf j hj
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at hsbnd
      rw [sibOff_eq _ hb, ← hpj] at hsbnd
      rw [← hpj] at hpbnd
      set d := o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * pj with hd
      have hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) ∨
          d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) + 8 ∨ d = 32 ∨ d = 40 := by
        simp only; rw [hsb]; omega
      have e7 := v7_block hL hleaf (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) hdv
      have e6 := v6_block (leaf := leaf) (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) (by omega) hdv
      simp only at e7 e6
      rw [plan_eq, ← hpj, show o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L = 16 * pj + d by omega, e7,
        show 16 * pj + d - 16 * pj = d by omega,
        show lvSrc L.val j - SNAP2 + WIT + d = WIT + (8136 + layOffV6 L + (64 * (height L - 1 - j) + d)) by
          rw [lvSrc_eq L hL j hj]; omega,
        v6M_eq N w _ (by omega) (by omega)]
      rw [show 8136 + layOffV6 L + (64 * (height L - 1 - j) + d) = 8136 + layOffV6 L + (64 * (height L - 1 - j) + d)
        from rfl, v6_layer N w L _ (by omega)]
      unfold layerRegionV6
      rw [if_neg hL, e6]
  · rw [if_neg hp, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length]; omega),
      ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length, chOut_eq N w L hL _ (by omega) (by omega)]
end ident3
/-- Pairing stage 1: final witness words of the layer regions above the top path area (`[8864, 20104)`) are the
second pass's output (`out2old` at staging offset `8 i + 856`). -/
theorem compact2_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8864 ≤ 8 * i) (h2 : 8 * i < 20104) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) =
      out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) := by
  unfold out2old
  rw [if_neg (show ¬ 8 * i + 856 < 8952 by omega)]
  by_cases htop : 8 * i + 856 < 13176
  · rw [if_pos htop]
    have h66 : height (0 : Layer) + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 0 = 66 := rfl
    have hw7 := ClaudeWCT.W9.Machine.Expand.OldW.win_layerRegion N w 0 (8 * i - 8096) 8
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.pathSlots, ClaudeWCT.W9.Machine.Expand.OldW.chainArea]; omega)
    have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [h66]; omega)
    rw [show ClaudeWCT.W9.Machine.Expand.OldW.layerBase 0 + (8 * i - 8096) = 8 * i by
      simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega] at hw7
    rw [hw7, layerRegion_top_tail N w _ (by omega),
      show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6]; omega,
      v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
  rw [if_neg htop, if_pos (show 8 * i + 856 < 20960 by omega)]
  have hW : WIT = 0x800 := rfl
  have key : ∀ L : Layer, L.val ≠ 0 → zoneLay (8 * i + 856) = L.val →
      ClaudeWCT.W9.Machine.Expand.OldW.layerBase L ≤ 8 * i →
      8 * i + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L +
        (16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L + 2248) →
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) =
        (if 8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT) < pathTop (zoneLay (8 * i + 856)) then
          pathOut (v6M N w) (zoneLay (8 * i + 856)) (lroute (zoneLay (8 * i + 856)) (WCT9.digestIndex N))
            (8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT))
        else chOut (v6M N w) (zoneLay (8 * i + 856)) (8 * i + 856 - (chDst (zoneLay (8 * i + 856)) - WIT))) := by
    intro L hL hz h1 h2
    obtain ⟨e1, e2, e3, e4⟩ := lvDst_eq L hL
    rw [hz, e1, e2, e3, zone_low N w L hL (8 * i) h1 h2 (by omega),
      show 8 * i + 856 - (ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + 856) =
        8 * i - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L by omega,
      show 8 * i + 856 - (ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + 856 +
        16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L) =
        8 * i - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L by
        omega]
  by_cases hz1 : 8 * i + 856 < 15824
  · exact key 1 (by decide) (by unfold zoneLay; rw [if_pos hz1]; rfl)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)
  · by_cases hz2 : 8 * i + 856 < 18392
    · exact key 2 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_pos hz2]; rfl)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)
    · exact key 3 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_neg hz2]; rfl)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)

/-- C4: the second pass leaves the top path area in the old 64-byte stride layout (`layerRegionV6 N w 0`); the
post-pass re-places it. -/
theorem compact2_top_old (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8096 ≤ 8 * i) (h2 : 8 * i < 8864) :
    out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) =
      BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * i - 8096) 8)) := by
  have h66 : height (0 : Layer) + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 0 = 66 := rfl
  have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [h66]; omega)
  unfold out2old
  rw [if_neg (by omega), if_pos (by omega),
    show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6, WIT]; omega,
    v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
/-- Pairing stage 1: the staged rho / digest counter (second-pass offsets 20960 .. 20984) are the witness tail. -/
theorem tail_words (N : HashOutput) (w : WCT9.Witness) (t : Nat) (ht : t < 4) :
    out2old (v6M N w) (WCT9.digestIndex N) (20960 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)) := by
  rw [ClaudeWCT.W9.Machine.Expand.OldW.win_tail N w _ _ (by omega)]
  have hrho : ∀ d, d + 8 ≤ 16 → window (tailBytes w) d 8 = window (witListV6 N w) d 8 := fun d hd => by
    rw [v6_head N w _ (by omega)]
    unfold tailBytes headerBytesV5
    simp only [List.append_assoc]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
  unfold out2old
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [if_pos (by norm_num), show 8 * 0 = 0 from rfl, hrho 0 (by omega), ← v6M_eq N w 0 (by omega) (by omega),
      Nat.add_zero]
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 8 * 1 = 8 from rfl, hrho 8 (by omega),
      ← v6M_eq N w 8 (by omega) (by omega)]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num), show 8 * 2 = 16 from rfl]
    unfold tailBytes
    simp only [List.append_assoc]
    rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
      show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
      window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), show 8 * 3 = 24 from rfl,
      ClaudeWCT.W9.Machine.Expand.OldW.tail_counter_window, v6M_eq N w 16 (by omega) (by omega), v6_head N w _ (by omega)]
    have hh : window (headerBytesV5 w) 16 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
      unfold headerBytesV5
      rw [show bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++
        zeros 28 = bytesLE 16 w.signature.rho ++ (bytesLE 4 w.digestCounter ++ zeros 4 ++ (zeros 8 ++
          bytesLE 4 (w.counters 3) ++ zeros 28)) by simp [zeros, List.append_assoc, List.replicate_add]]
      rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
        show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
        window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (by simp [bytesLE_length, zeros])]
    rw [hh, wu_small _ (by
      rw [SigGolfCandidate.T3M.readLE_append, bytesLE_length]
      rw [SigGolfCandidate.T3M.readLE_bytesLE]
      have := w.digestCounter.isLt
      have hz : readLE (zeros 4) = 0 := by decide
      rw [hz]; omega)]
/-! ### Pairing stage 1: the leaf buffers written by the layout block -/
def layOf (k : Nat) : Layer := Fin.ofNat 4 (3 - Layout.grpK k)
def iK (k : Nat) : Nat := k - 43 * Layout.grpK k
def kOf (lay : Layer) (i : Nat) : Nat := 43 * (3 - lay.val) + i
theorem buf_table : ∀ k < 180, iK k < chainCount (layOf k) ∧
    Layout.slotK k = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot (layOf k) (iK k) ∧
    Layout.sK k = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.chainBlock (layOf k) (iK k) + ClaudeWCT.W9.Machine.Expand.OldW.valueOff (layOf k) (iK k) ∧
    11768 ≤ Layout.sK k ∧ Layout.sK k + 16 ≤ 23008 ∧ Layout.slotK k % 8 = 0 := by
  decide +kernel

theorem buf_table2 : ∀ lay : Layer, ∀ i < chainCount lay, kOf lay i < 180 ∧
    Layout.slotK (kOf lay i) = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i := by
  decide +kernel
theorem hitVal_hit (M : Nat → Word) (k : Nat) (hk : k < 180) (A : Nat)
    (h : Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16) :
    Layout.hitVal M 180 A = M (Layout.sK k + (A - Layout.slotK k)) := by
  have key : ∀ j, k < j → j ≤ 180 → Layout.hitVal M j A = M (Layout.sK k + (A - Layout.slotK k)) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rw [Layout.hitVal_succ M j A (by omega)]
      by_cases hjk : j = k
      · subst hjk; rw [if_pos h]
      · have := Layout.slot_mono k j (by omega) (by omega)
        rw [if_neg (by omega)]
        exact ih (by omega) (by omega)
  exact key 180 hk le_rfl
theorem hitVal_miss (M : Nat → Word) (A : Nat)
    (h : ∀ k < 180, ¬ (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) : Layout.hitVal M 180 A = 0 := by
  have hn : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) = none := by
    rw [List.find?_eq_none]; intro k hk; simpa using h k (List.mem_range.mp hk)
  unfold Layout.hitVal; rw [hn]
theorem bufferMem_low (M : Nat → Word) (A : Nat) (hA : A < 23008) (h1 : A ≠ 1240) : Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
section buffers
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_value (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (ClaudeWCT.W9.Machine.Expand.OldW.chainBlock lay i + ClaudeWCT.W9.Machine.Expand.OldW.valueOff lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hv : ClaudeWCT.W9.Machine.Expand.OldW.lsValue (w.signature.layers lay) i = (w.signature.layers lay).values ⟨i, hi⟩ := by
    simp [ClaudeWCT.W9.Machine.Expand.OldW.lsValue, hi]
  rw [← window_window' _ _ 16 d 8 hd,
    ClaudeWCT.W9.Machine.Expand.OldW.win_chain N w lay ⟨i, hi⟩ _ (by unfold ClaudeWCT.W9.Machine.Expand.OldW.valueOff; split <;> omega)]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.chainCell ClaudeWCT.W9.Machine.Expand.OldW.valueOff
  by_cases hG : ClaudeWCT.W9.Machine.Expand.OldW.isG lay i = true
  · simp only [hG, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _), hv]
  · simp only [hG, if_false, Bool.false_eq_true]
    rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _), hv]
theorem win_slot (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hb := ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot_bounds lay i hi
  rw [← window_window' _ _ 16 d 8 hd, ClaudeWCT.W9.Machine.Expand.OldW.witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, ClaudeWCT.W9.Machine.Expand.OldW.headerBytes_length, ClaudeWCT.W9.Machine.Expand.OldW.wctBytes_length,
      ClaudeWCT.W9.Machine.Expand.OldW.layers_length]
    omega)]
  simp only [List.length_append, ClaudeWCT.W9.Machine.Expand.OldW.headerBytes_length, ClaudeWCT.W9.Machine.Expand.OldW.wctBytes_length,
    ClaudeWCT.W9.Machine.Expand.OldW.layers_length]
  rw [window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.leafBuffersBytes_length]; omega),
    show 80 + 8016 + 12008 = 20104 by decide,
    ClaudeWCT.W9.Machine.Expand.OldW.win_leafBuffersBytes w.signature lay ⟨i, hi⟩]
theorem lb_zero (sig : WCT9.Signature) (lay : Layer) (off : Nat) (h8 : off % 8 = 0)
    (hlen : off + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay)
    (hz : ∀ i < chainCount lay, ¬ (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ off ∧
      off < ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + 16)) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBytes sig lay) off 8 = zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot at hz
  simp only [Nat.add_sub_cancel_left] at hz
  unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBytes
  have hE := ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes_length sig lay
  have hc : 2 ≤ chainCount lay ∧ 16 * chainCount lay + 16 + (if lay = 0 then 80 else if lay.val = 1 then 16 else 32) =
      ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay := by
    fin_cases lay <;> decide
  generalize (if lay = 0 then 80 else if lay.val = 1 then 16 else 32) = Z at hc ⊢
  have htl : ((ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes sig lay).take 16).length = 16 := by
    rw [List.length_take, hE]; omega
  have hdl : ((ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes sig lay).drop 16).length = 16 * chainCount lay - 16 := by
    rw [List.length_drop, hE]
  by_cases h0 : off < 16
  · exfalso; have h := hz 0 (by omega); simp only [if_pos rfl, ↓reduceIte] at h; omega
  by_cases h1 : off < 32
  · rw [window_append_left _ _ _ _ (by simp [zeros, htl, hdl]; omega),
      window_append_left _ _ _ _ (by simp [zeros, htl]; omega),
      window_append_right _ _ _ _ (by rw [htl]; omega), htl, window_zeros _ _ _ (by simp [zeros]; omega)]
  by_cases h2 : 16 * chainCount lay + 16 ≤ off
  · rw [window_append_right _ _ _ _ (by simp [zeros, htl, hdl]; omega), window_zeros _ _ _ (by
      simp only [List.length_append, htl, hdl, zeros, List.length_replicate]; omega)]
  exfalso; have h := hz ((off - 16) / 16) (by omega); rw [if_neg (by omega)] at h; omega

theorem buf_zero (o : Nat) (h1 : 20104 ≤ o) (h2 : o < 23208) (h8 : o % 8 = 0)
    (hz : ∀ lay : Layer, ∀ i < chainCount lay,
      ¬ (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i ≤ o ∧ o < ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i + 16)) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8 = zeros 8 := by
  have go : ∀ lay : Layer, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ o →
      o + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay →
      window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8 = zeros 8 := by
    intro lay hb he
    have hs : ∀ i, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i := by
      intro i; unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot; omega
    rw [show o = ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + (o - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay) by omega,
      ClaudeWCT.W9.Machine.Expand.OldW.win_leafBuffer N w lay _ 8 (by omega)]
    apply lb_zero _ lay _ (by fin_cases lay <;> simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase] at hb ⊢ <;> omega) (by omega)
    intro i hi h
    have := hs i
    exact hz lay i hi ⟨by omega, by omega⟩
  by_cases a3 : o < 20840
  · exact go 3 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega) (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  by_cases a2 : o < 21576
  · exact go 2 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  by_cases a1 : o < 22296
  · exact go 1 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  · exact go 0 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
/-- Pairing stage 1: the leaf buffers and the tail after the layout block. -/
theorem buffer_words (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)))
    (i : Nat) (h1 : 20104 ≤ 8 * i) (h2 : 8 * i < 23240) :
    Buffer.bufferMem M (2904 + 8 * i) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg (by omega)]
  by_cases ht : 23208 ≤ 8 * i
  · rw [if_pos (by omega), show 2904 + 8 * i - 3104 = 23008 + 8 * ((8 * i - 23208) / 8) by omega,
      hT _ (by omega), show 23208 + 8 * ((8 * i - 23208) / 8) = 8 * i by omega]
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases hs : ∃ k, k < 180 ∧ Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16
  · obtain ⟨k, hk, ha, hb⟩ := hs
    obtain ⟨hi, hsl, hsk, hk1, hk2, hk8⟩ := buf_table k hk
    rw [hitVal_hit M k hk _ ⟨ha, hb⟩]
    set d := 2904 + 8 * i - Layout.slotK k with hd
    have hd8 : d = 0 ∨ d = 8 := by omega
    rw [show Layout.sK k + d = 2904 + (ClaudeWCT.W9.Machine.Expand.OldW.chainBlock (layOf k) (iK k) +
        ClaudeWCT.W9.Machine.Expand.OldW.valueOff (layOf k) (iK k) + d) by omega,
      hM _ (by omega) (by omega) (by
        have := (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).1
        omega),
      win_value N w _ _ hi d (by omega),
      show 8 * i = ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot (layOf k) (iK k) + d by omega,
      win_slot N w _ _ hi d (by omega)]
  · have hn : ∀ k < 180, ¬ (Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16) :=
      fun k hk h => hs ⟨k, hk, h⟩
    rw [hitVal_miss M _ hn, buf_zero N w (8 * i) h1 (by omega) (by omega) (fun lay j hj h => by
      obtain ⟨hk, he⟩ := buf_table2 lay j hj
      exact hn _ hk ⟨by omega, by omega⟩), ofNat_readLE_zeros8]
end buffers

section topPost
variable (N : HashOutput) (w : WCT9.Witness)
end topPost
/-! ### C4: the top path area after the post-pass -/
open SigGolfCandidate.T3 (route height LayerSignature)
open SigGolfCandidate.T3M (layerBytes layerBytes_merkle window_append_left window_append_right window_full)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand (layerRegionV6)
/-- The post-pass's table slot is the witness's sibling slot (`topSibSlot`). -/
theorem ppSlot_eq_sib (leaf : Nat) (hl : leaf < 4096) (j : Nat) (hj : j < 12) :
    16 * Buffer.Post.ppSlot leaf j = ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot leaf j := by
  have hs : ∀ b, b < 2 → SigGolfCandidate.T3M.sibOff b = 48 * (1 - b) := fun b hb => by
    unfold SigGolfCandidate.T3M.sibOff; split <;> omega
  unfold Buffer.Post.ppSlot
  by_cases h6 : j < 6
  · rw [if_pos h6, ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot_lo h6]
    unfold slotA ClaudeWCT.W9.Machine.Expand.OldW.topSibA ClaudeWCT.W9.Machine.Expand.OldW.topSlotA
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
  · rw [if_neg h6, ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot_hi (by omega) hj, Nat.mod_eq_of_lt (show leaf / 64 < 64 by omega)]
    unfold slotB ClaudeWCT.W9.Machine.Expand.OldW.topSibB ClaudeWCT.W9.Machine.Expand.OldW.topSlotB
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
/-- The old (pre-C4) top layout holds sibling `j` at `64 (11 - j) + sibOff`. -/
theorem oldTop_sib (leaf : Nat) (ls : LayerSignature 0) (j : Nat) (hj : j < height (0 : Layer)) (d : Nat)
    (hd : d = 0 ∨ d = 8) :
    window (layerBytes 0 leaf ls) (Buffer.Post.ppOld leaf j - 11000 + d) 8 = window (bytesLE 16 (ls.path ⟨j, hj⟩)) d 8 := by
  have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h12 : j < 12 := lt_of_lt_of_eq hj ClaudeWCT.W9.Machine.Expand.OldW.height_top
  have hm := layerBytes_merkle 0 leaf ls ⟨j, hj⟩ (48 * (1 - leaf / 2 ^ j % 2)) (by omega)
  simp only [Fin.val_mk] at hm
  have hin : window (if leaf / 2 ^ j % 2 = 1 then bytesLE 16 (ls.path ⟨j, hj⟩) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path ⟨j, hj⟩)) (48 * (1 - leaf / 2 ^ j % 2)) 16 = bytesLE 16 (ls.path ⟨j, hj⟩) := by
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ j) with h | h
    · rw [h, if_neg (by decide), show 48 * (1 - 0) = (zeros 48).length by simp [zeros],
        window_append_right _ _ _ _ le_rfl, Nat.sub_self, window_full _ _ (bytesLE_length _ _)]
    · rw [h, if_pos rfl, show 48 * (1 - 1) = 0 from rfl, window_append_left _ _ _ _ (by rw [bytesLE_length]),
        window_full _ _ (bytesLE_length _ _)]
  rw [show Buffer.Post.ppOld leaf j - 11000 + d = 64 * (height (0 : Layer) - 1 - j) + 48 * (1 - leaf / 2 ^ j % 2) + d by
      unfold Buffer.Post.ppOld Buffer.Post.ppBit; rw [ClaudeWCT.W9.Machine.Expand.OldW.height_top]; omega,
    ← window_window' _ _ 16 d 8 (by omega), hm, hin]
/-- The top path area after the post-pass is the witness's plan-placed area. -/
theorem postMem_top (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (q : Nat) (hq : q < 96) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (11000 + 8 * q) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8096 + 8 * q) 8)) := by
  have hw := ClaudeWCT.W9.Machine.Expand.OldW.win_topPath N w (8 * q) 8 (by omega)
  rw [show ClaudeWCT.W9.Machine.Expand.OldW.layerBase 0 = 8096 from rfl] at hw
  rw [hw]
  have hl6 : ∀ q < 96, window (layerRegionV6 N w 0) (8 * q) 8 =
      window (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q) 8 := by
    intro q hq
    have h63 : 64 * (height (0 : Layer) + chainCount (0 : Layer)) = 4032 := rfl
    unfold layerRegionV6 ClaudeWCT.W9.Machine.Expand.layerBytesV6
    rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos (show (0 : Layer).val = 0 from rfl), List.append_assoc,
      window_append_left _ _ _ _ (by rw [List.length_take, layerBytes_length, h63]; omega),
      window_take _ _ _ _ (by omega)]
  replace hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window
      (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q) 8)) :=
    fun q hq => (hold q hq).trans (by rw [hl6 q hq])
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  generalize (route (WCT9.digestIndex N) 0).1 = leaf at hl hold ⊢
  generalize w.signature.layers 0 = ls at hold ⊢
  by_cases hs : ∃ j, j < 12 ∧ 16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16
  · obtain ⟨j, hj, h1, h2⟩ := hs
    have hj' : j < height (0 : Layer) := lt_of_lt_of_eq hj ClaudeWCT.W9.Machine.Expand.OldW.height_top.symm
    have he := ppSlot_eq_sib leaf hl j hj
    have hpo := Buffer.Post.ppOld_lt leaf j
    have hpb := Buffer.Post.ppBit_lt leaf j
    have hpo' : 11000 ≤ Buffer.Post.ppOld leaf j := by unfold Buffer.Post.ppOld; omega
    obtain ⟨D, hD8, hDq⟩ : ∃ D, (D = 0 ∨ D = 8) ∧ 8 * q = 16 * Buffer.Post.ppSlot leaf j + D :=
      ⟨8 * q - 16 * Buffer.Post.ppSlot leaf j, by omega, by omega⟩
    rw [hDq, show 11000 + (16 * Buffer.Post.ppSlot leaf j + D) = Buffer.Post.ppNew leaf j + D by
        unfold Buffer.Post.ppNew; omega,
      Buffer.Post.ppPlace_hit _ leaf hl j hj _ hD8,
      bufferMem_low _ _ (by omega) (by omega),
      show Buffer.Post.ppOld leaf j + D = 11000 + 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) by omega,
      hold _ (by omega),
      show 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) = Buffer.Post.ppOld leaf j - 11000 + D by omega,
      oldTop_sib leaf ls j hj' D hD8, he, ← window_window' _ _ 16 D 8 (by omega),
      ClaudeWCT.W9.Machine.Expand.OldW.topPath_sib leaf ls ⟨j, hj'⟩]
  · have hm : ∀ j < 12, ¬ (16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16) :=
      fun j hj h => hs ⟨j, hj, h⟩
    rw [Buffer.Post.ppPlace_miss _ leaf q hq hm,
      ClaudeWCT.W9.Machine.Expand.OldW.topPath_zero leaf ls (by omega) (fun j => by
        have hj : j.val < 12 := lt_of_lt_of_eq j.isLt ClaudeWCT.W9.Machine.Expand.OldW.height_top
        have := hm j.val hj
        rw [← ppSlot_eq_sib leaf hl j.val hj]
        omega)]
    decide

/-- Pairing stage 1: the final witness words `[8096, 23240)` after the buffer pass and the top post-pass. -/
theorem postMem_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)))
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (i : Nat) (h1 : 1012 ≤ i) (h2 : i < 2905) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (2904 + 8 * i) =
      (wordsOf (ClaudeWCT.W9.Machine.Expand.OldW.witList N w)).getD i 0 := by
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  rw [wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq N w) i h2]
  by_cases htop : 8 * i < 8864
  · rw [show 2904 + 8 * i = 11000 + 8 * (i - 1012) by omega, postMem_top N w M hold (i - 1012) (by omega),
      show 8096 + 8 * (i - 1012) = 8 * i by omega]
  rw [Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by omega)]
  by_cases hb : 8 * i < 20104
  · rw [bufferMem_low _ _ (by omega) (by omega)]
    exact hM _ (by omega) hb (by omega)
  · exact buffer_words N w M hM hT i (by omega) (by omega)

end ClaudeWCT.W9.Machine.Expand.Compact2
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsRuns ====
section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runA (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux { noAlias := true } look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
def cE (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldc (a : Nat) : E := .ld (cE a)
def mwc (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def regsOf (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def pres2 (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k cyc : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, cyc, brs, none⟩
def pres (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, k, brs, none⟩
def qI (c i : Nat) : Nat := qIdx.getD (6 * c + i) 0
def chkI (c i s : Nat) : Nat := chkIdx.getD (30 * c + 5 * i + s) 0
def skipI (c i s : Nat) : Nat := skipIdx.getD (30 * c + 5 * i + s) 0
def leafI (c : Nat) : Nat := leafIdx.getD c 0
def lI (c : Nat) : Nat := lIdx.getD c 0
def tI (c : Nat) : Nat := tIdx.getD c 0
def nodeI (c : Nat) : Nat := nodeIdx.getD c 0
def ntI (c : Nat) : Nat := ntIdx.getD c 0
def rI (c : Nat) : Nat := rIdx.getD c 0
def lwuI (c : Nat) : Nat := lwuIdx.getD c 0
def pcI (c l : Nat) : Nat := rI c + 12 + 13 * l
def lcEnd (c i : Nat) : Nat := if i = 5 then lI c else qI c (i + 1)
def hdr8 (c : Nat) : Nat := 2049 + 65536 * c
def hdr6 (c : Nat) : Nat := 1537 + 65536 * c
/-- FTS chain word constant. C4 (FTS coordinate + 1, as b3cc11b's campaign S2): coordinate nibble `c + 1`. -/
def chainK (c i : Nat) : Nat := 0x80 + 4 * i + 65536 * (c + 1)
def nodeK (c : Nat) : Nat := 769 + 65536 * (4 + c)
def slotV (c i : Nat) : Nat := SIG + 16 + 208 * c + 16 * i
def slotP (c l : Nat) : Nat := SIG + 112 + 208 * c + 16 * l
def leafOff (i : Nat) : Nat := if i = 0 then 0 else 16 * (i + 2)
def forOff (c : Nat) : Nat := 32 + 32 * c
def w1E : E := .bin .or (.bin .sll (.reg .x18) (cE 32)) (.reg .x22)
def qE (c i : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (chainK c i))
def idx32E : E := .bin .sll (.reg .x22) (cE 32)
/-- FTS node word base. C4: coordinate nibble `c + 1`; coordinate 0 goes through the arena trampoline
`lui t2,16; or t1,t1,t2; ori t1,t1,1537`, which produces the same expression. -/
def nodeLoE (c : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (cE (65536 * (c + 1)))) (cE 1537)
/-- FTS leaf word. C4: coordinate nibble `c + 1`; for coordinate 0 the arena trampoline ORs `65536` and `1537`
separately. -/
def leafLoE (c : Nat) : E :=
  if c = 0 then
    .bin .or (.bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE 65536)) (cE 1537)
  else .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537 + 65536 * (c + 1)))
def leafX7 (c : Nat) : E := if c = 0 then cE 65536 else cE (65536 * (c + 1) + 1537)
def x29A (off : Nat) : Addr := ⟨some (.reg .x29), BitVec.ofNat 64 off⟩
def nodeLo7 (c index : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 27 * index
def leafLo7 (c index j : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 20 * j + 2 ^ 27 * index
def dE (i : Nat) : E := .bin .sub (cE 4) (.bin .and (.bin .srl (.reg .x25) (cE (3 * i))) (cE 7))
def x18p1 : E := .bin .add (.reg .x18) (cE 1)
def x18m1 : E := .bin .add (.reg .x18) (cE (2 ^ 64 - 1))
def heapLeafE : E := .bin .sll (.bin .add (.reg .x18) (cE 128)) (cE 4)
def sh5 : E := .bin .sll (.reg .x18) (cE 5)
def sh4 : E := .bin .sll (.reg .x18) (cE 4)
def pathE (l : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.bin .add (.reg .x24) (cE 128)) (cE l)) (cE 1)) (cE 4)
def fdw (c : Nat) : Nat := WCT9.childBase c / 64
def fsh (c : Nat) : Nat := [0,0,21,36,0,21,36,0,21].getD c 0
def fhas (c : Nat) : Bool := c % 3 != 1
def fsrcE (c : Nat) : E :=
  if fhas c then .bin .srl (ldc (NBUF + 8 * fdw c)) (cE (fsh c)) else ldc (NBUF + 8 * fdw c)
def fchildE (c : Nat) : E := if c = 3 ∨ c = 6 then .bin .srl (fsrcE c) (cE 21) else .bin .and (fsrcE c) (cE 127)
def fieldE (c : Nat) : E := .bin .and (.bin .srl (fsrcE c) (cE 7)) (cE 1023)
def expF (c : Nat) : PRes :=
  pres [(.x6, .bin .sll (fieldE c) (cE 2)), (.x24, fchildE c), (.x25, fieldE c),
    (.x28, .bin .add (.bin .sll (fieldE c) (cE 2)) (cE TBL))] [] [] (lwuI c) false
    (if fhas c then 13 else 12) []
def expChk (c i s v : Nat) : PRes :=
  if v = 0 then pres [] [] [] (skipI c i s) false 1 [⟨.ne, .reg .x18, .reg .x24, true⟩]
  else if v = 1 then
    pres [(.x6, cE s)] [] [] (skipI c i s) false 3 [⟨.ne, .reg .x26, cE s, true⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
  else
    pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE (slotV c i))]
      [mwc (slotV c i + 8) (ldc (CHAINW + 56)), mwc (slotV c i) (ldc (CHAINW + 48))] [] (skipI c i s) false 11
      [⟨.ne, .reg .x26, cE s, false⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
def expStp (c i s : Nat) : PRes :=
  pres [(.x6, cE (s - 1)), (.x10, cE CHAINW), (.x11, cE 64), (.x12, cE (CHAINW + 48)), (.x29, cE CHAINW)]
    [mwc (CHAINW + 16) (.bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1)))] [] (chkI c i s - 1) true 9 []
def expLc (c i : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE LEAFW)]
    [mwc (LEAFW + leafOff i + 8) (ldc (CHAINW + 56)), mwc (LEAFW + leafOff i) (ldc (CHAINW + 48))] []
    (lcEnd c i) false 8 []
/-- Nested FTS (r1-1): the leaf pad word `off` of coordinate `c`, i.e. `L_{c-1}` from the previous forest pair. -/
def padE (c off : Nat) : E := if c = 0 then cE 0 else ldc (FORW + forOff (c - 1) + off)
def expL (c : Nat) : PRes :=
  pres [(.x6, heapLeafE), (.x7, leafX7 c), (.x10, cE LEAFW), (.x11, cE 128), (.x12, .bin .add heapLeafE (cE HEAPW))]
    [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, padE c 8), (x29A 32, padE c 0)]
    ([.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 40) 8] ++
      (if c = 0 then [] else [.ne ⟨none, BitVec.ofNat 64 (FORW + forOff (c - 1) + 8)⟩ (x29A 32)]) ++
      [.valid (x29A 32) 8]) (tI c - 1) true
    (if c = 0 then 21 else 23) []
def expT (c : Nat) (back : Bool) : PRes :=
  if back then pres [(.x6, cE 128), (.x18, x18p1)] [] [] (leafI c) false 3 [⟨.ltu, x18p1, cE 128, true⟩]
  else pres [(.x6, cE 128), (.x18, cE 127)] [] [] (nodeI c) false 4 [⟨.ltu, x18p1, cE 128, false⟩]
def nodeLd (off : Nat) : E := .ld (.bin .add sh5 (cE (HEAPW + off)))
def nodeAddr (off : Nat) : Addr := ⟨some sh5, BitVec.ofNat 64 (HEAPW + off)⟩
def nodeX7 (c : Nat) : E := cE (65536 * (c + 1))
/-- Packed node tweak (heaps `8..127`): high word `[h < 8] * h`, low word `nodeLo7 + [h < 8] * h - h`. -/
def nodeHiE : E := .bin .mul (.bin .sltu (.reg .x18) (cE 8)) (.reg .x18)
def nodeDE : E := .bin .sub nodeHiE (.reg .x18)
def nodeLoNE (c : Nat) : E := .bin .add (nodeLoE c) nodeDE
def expN (c : Nat) : PRes :=
  pres2 [(.x6, nodeLoNE c), (.x7, nodeDE), (.x10, cE NODEW), (.x11, cE 64), (.x12, cE NOUTW),
    (.x28, .bin .add sh5 (cE HEAPW)), (.x29, nodeHiE)]
    [mwc (NODEW + 24) nodeHiE, mwc (NODEW + 16) (nodeLoNE c), mwc (NODEW + 56) (nodeLd 24),
      mwc (NODEW + 48) (nodeLd 16), mwc (NODEW + 8) (nodeLd 8), mwc NODEW (nodeLd 0)]
    [.ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 NODEW⟩, .ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩,
      .valid (nodeAddr 24) 8, .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 NODEW⟩,
      .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩, .valid (nodeAddr 16) 8, .valid (nodeAddr 8) 8,
      .valid (nodeAddr 0) 8]
    (ntI c - 1) true (if c = 0 then 29 else 25) (if c = 0 then 32 else 28) []
def heapAddr (off : Nat) : Addr := ⟨some sh4, BitVec.ofNat 64 (HEAPW + off)⟩
/-- Nested FTS (r1-1): the fold output half, `16 * [heap < 4]` (heaps 2 and 3 keep the HIGH half). -/
def hiSelE : E := .bin .sll (.bin .sltu (.reg .x18) (cE 4)) (cE 4)
def outE : E := .bin .add hiSelE (cE NOUTW)
def outAddr (off : Nat) : Addr := ⟨some hiSelE, BitVec.ofNat 64 (NOUTW + off)⟩
def outLd (off : Nat) : E := .ld (.bin .add hiSelE (cE (NOUTW + off)))
/-- Fold post-hash kind for `c >= 1`: 0 = heap other than 4 and 2, 1 = heap 4 (pad := R_{c-1}), 2 = heap 2 (pad := 0). -/
def ntDirs (c kd : Nat) (back : Bool) : List Dir :=
  if c = 0 then [.br back] else if kd = 1 then [.br false, .br back] else if kd = 2 then [.br true, .br false, .br back]
  else [.br true, .br true, .br back]
def ntPadMem (c kd : Nat) : SymMem :=
  if c = 0 then [] else if kd = 1 then
    [mwc (NODEW + 40) (ldc (FORW + forOff (c - 1) + 24)), mwc (NODEW + 32) (ldc (FORW + forOff (c - 1) + 16))]
  else if kd = 2 then [mwc (NODEW + 40) (cE 0), mwc (NODEW + 32) (cE 0)] else []
def ntOutObl (c kd : Nat) : List Oblig :=
  if c = 0 ∨ kd = 0 then [.valid (outAddr 8) 8, .valid (outAddr 0) 8]
  else [.ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩, .ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩,
    .valid (outAddr 8) 8, .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩,
    .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩, .valid (outAddr 0) 8]
def ntBrs (c kd : Nat) : List Br :=
  if c = 0 then [] else if kd = 1 then [⟨.ne, .reg .x18, cE 4, false⟩]
  else if kd = 2 then [⟨.ne, .reg .x18, cE 2, false⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
  else [⟨.ne, .reg .x18, cE 2, true⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
def expNT (c kd : Nat) (back : Bool) : PRes :=
  pres [(.x6, cE 1), (.x7, outLd 8), (.x18, x18m1), (.x28, outE),
    (.x29, .bin .add sh4 (cE HEAPW))]
    ([(heapAddr 8, outLd 8), (heapAddr 0, outLd 0)] ++ ntPadMem c kd)
    ([.valid (heapAddr 8) 8, .valid (heapAddr 0) 8] ++ ntOutObl c kd)
    (if back then nodeI c else rI c) false (if c = 0 then 18 else if kd = 0 then 22 else 25)
    (⟨.ne, x18m1, cE 1, back⟩ :: ntBrs c kd)
def expR0 (c : Nat) : PRes :=
  pres [(.x6, ldc (HEAPW + 48)), (.x7, ldc (HEAPW + 56)), (.x28, cE (HEAPW + 32)), (.x29, cE (FORW + forOff c))]
    [mwc (FORW + forOff c + 24) (ldc (HEAPW + 56)), mwc (FORW + forOff c + 16) (ldc (HEAPW + 48)),
      mwc (FORW + forOff c + 8) (ldc (HEAPW + 40)), mwc (FORW + forOff c) (ldc (HEAPW + 32))] [] (pcI c 0) false 12 []
def pathAddr (l off : Nat) : Addr := ⟨some (pathE l), BitVec.ofNat 64 (HEAPW + off)⟩
def pathLd (l off : Nat) : E := .ld (.bin .add (pathE l) (cE (HEAPW + off)))
def expPC (c l : Nat) : PRes :=
  pres [(.x6, pathLd l 0), (.x7, pathLd l 8), (.x28, .bin .add (pathE l) (cE HEAPW)), (.x29, cE (slotP c l))]
    [mwc (slotP c l + 8) (pathLd l 8), mwc (slotP c l) (pathLd l 0)] [.valid (pathAddr l 8) 8, .valid (pathAddr l 0) 8]
    (pcI c (l + 1)) false 13 []
def expSK : PRes :=
  pres [(.x6, ldc 0x90), (.x7, ldc 0x98), (.x28, cE 0x80), (.x29, cE PRIVW)]
    [mwc (PRIVW + 40) (ldc 0x98), mwc (PRIVW + 32) (ldc 0x90), mwc (PRIVW + 8) (ldc 0x88), mwc PRIVW (ldc 0x80)] []
    (fieldIdx.getD 0 0) false 11 []
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` to `FOUT` and the encoding R slot. -/
def expFor : PRes :=
  pres [(.x6, ldc (FORW + forOff 8 + 16)), (.x7, ldc (FORW + forOff 8 + 24)), (.x28, cE PRIVW), (.x29, cE 0x20000)]
    [mwc (0x20290 + 8) (ldc (FORW + forOff 8 + 24)), mwc 0x20290 (ldc (FORW + forOff 8 + 16)),
      mwc (FOUT + 8) (ldc (FORW + forOff 8 + 8)), mwc FOUT (ldc (FORW + forOff 8))] [] 370 false 12 []
def expJ : PRes := pres [] [] [] 370 false 1 []
def runF (c : Nat) : Option PRes := run (coordLook c) [lwuI c] (cbase c) []
def chkDirs (v : Nat) : List Dir := if v = 0 then [.br true] else if v = 1 then [.br false, .br true] else [.br false, .br false]
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runL (c : Nat) : Option PRes := runA (coordLook c) [] (lI c) []
def runT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [leafI c, nodeI c] (tI c) [.br back]
def runN (c : Nat) : Option PRes := runA (coordLook c) [] (nodeI c) []
def runNT (c kd : Nat) (back : Bool) : Option PRes := runA (coordLook c) [nodeI c, rI c] (ntI c) (ntDirs c kd back)
def runR0 (c : Nat) : Option PRes := run (coordLook c) [pcI c 0] (rI c) []
def runPC (c l : Nat) : Option PRes := run (coordLook c) [pcI c (l + 1)] (pcI c l) []
def runSK : Option PRes := run headLook [fieldIdx.getD 0 0] 11175 []
def runFor : Option PRes := run forLook [370] 20715 []
def runJ : Option PRes := run tailLook [370] 20729 []
/-! ### Stage A (campaign X1): coefficient prologue, call sites and the shared GF(2^128) Horner routine HORN -/
def paIdx : List Nat := [11962,13021,14081,15141,16200,17260,18320,19379,20439]
def paI (c : Nat) : Nat := paIdx.getD c 0
def ecI (c : Nat) : Nat := paI c - 1
def hornI : Nat := 11368
def hkI : Nat := 11220
def hbI : Nat := 11226
def hfI : Nat := 11374
def orIdx : E := .bin .or (cE 0) (.reg .x22)
def x7p1 : E := .bin .add (.reg .x7) (cE 1)
def pairWE : E := .bin .or (.bin .sll x7p1 (cE 32)) (.reg .x22)
def expZ (c : Nat) : PRes :=
  pres [(.x6, orIdx), (.x7, cE 0), (.x10, cE PRIVW), (.x11, cE 64), (.x12, cE COEF), (.x29, cE PRIVW)]
    [mwc (PRIVW + 24) orIdx, mwc (PRIVW + 16) (cE (hdr8 c))] [] (ecI c) true 14 []
def expCL (c : Nat) (b : Bool) : PRes :=
  if b then
    pres [(.x6, pairWE), (.x7, x7p1), (.x10, cE PRIVW), (.x11, cE 64), (.x12, .bin .add (.reg .x12) (cE 32)),
      (.x29, cE PRIVW)] [mwc (PRIVW + 24) pairWE] [] (ecI c) true 10 [⟨.ne, x7p1, cE 27, true⟩]
  else
    pres [(.x6, cE 27), (.x7, x7p1), (.x12, .bin .add (.reg .x12) (cE 32)), (.x18, cE 0)] [] [] (leafI c) false 6
      [⟨.ne, x7p1, cE 27, false⟩]
def ptE (i : Nat) : E :=
  .bin .add (.bin .sll (.bin .add (.bin .sll (.reg .x18) (cE 1)) (.reg .x18)) (cE 1)) (cE (i + 1))
def retW (c i : Nat) : Nat := 0x1000 + 4 * (qI c i + 5)
def expQ (c i : Nat) : PRes := pres [(.x1, cE (retW c i)), (.x6, ptE i)] [] [] hornI false 5 []
def expS (c i : Nat) : PRes :=
  pres [(.x6, cE 4), (.x7, cE (chainK c i)), (.x26, dE i), (.x29, cE CHAINW)]
    [mwc (CHAINW + 24) (cE 0), mwc (CHAINW + 16) (qE c i)] [] (chkI c i 0) false (if c = 0 then 17 else 15) []
def expH0 : PRes := pres [(.x7, cE (COEF + 864)), (.x10, cE 0), (.x11, cE 0), (.x28, cE COEF)] [] [] hkI false 6 []
def expHK : PRes :=
  pres [(.x7, .bin .add (.reg .x7) (cE (2 ^ 64 - 16))), (.x12, cE 0), (.x13, cE 0), (.x14, cE 0), (.x15, cE 0),
    (.x16, .reg .x6)] [] [] hbI false 6 []
def sh1 (r : Reg) : E := .bin .sll (.reg r) (cE 1)
def hi63 (r : Reg) : E := .bin .srl (.reg r) (cE 63)
def xr (a b : Reg) : E := .bin .xor (.reg a) (.reg b)
def hbShift : List (Reg × E) :=
  [(.x10, sh1 .x10), (.x11, .bin .or (sh1 .x11) (hi63 .x10)), (.x12, .bin .or (sh1 .x12) (hi63 .x11)),
    (.x16, .bin .srl (.reg .x16) (cE 1)), (.x17, hi63 .x10)]
def expHB (b1 b2 : Bool) : PRes :=
  pres ((if b1 then [] else [(.x13, xr .x13 .x10), (.x14, xr .x14 .x11), (.x15, xr .x15 .x12)]) ++ hbShift) [] []
    (if b2 then hbI else hfI) false ((if b1 then 11 else 14) + (if b2 then 0 else 1))
    [⟨.ne, .bin .srl (.reg .x16) (cE 1), cE 0, b2⟩, ⟨.eq, .bin .and (.reg .x16) (cE 1), cE 0, b1⟩]
def shE (r : Reg) (k : Nat) : E := .bin .sll (.reg r) (cE k)
def foldE : E := .bin .xor (.bin .xor (.bin .xor (.bin .xor (.reg .x13) (shE .x15 1)) (shE .x15 2)) (shE .x15 7)) (.reg .x15)
def c0E : E := .ld (.reg .x7)
def c1E : E := .ld (.bin .add (.reg .x7) (cE 8))
def hfRegs : List (Reg × E) :=
  [(.x10, .bin .xor foldE c0E), (.x11, .bin .xor (.reg .x14) c1E), (.x13, foldE), (.x17, c1E)]
def hfObl : List Oblig := [.valid ⟨some (.reg .x7), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x7), 0⟩ 8]
def expHF (b : Bool) : PRes :=
  if b then pres hfRegs [] hfObl hkI false 12 [⟨.ne, .reg .x7, .reg .x28, true⟩]
  else ⟨⟨regsOf (hfRegs ++ [(.x29, cE CHAINW)]),
      [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)], hfObl⟩,
    0, false, 17, 17, [⟨.ne, .reg .x7, .reg .x28, false⟩], some (.bin .and (.reg .x1) (cE (2 ^ 64 - 2)))⟩
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okF (c : Nat) : Bool := optBeq (runF c) (expF c) && optBeq (runZ c) (expZ c)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s => optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okTail (c : Nat) : Bool :=
  optBeq (runL c) (expL c) && optBeq (runT c true) (expT c true) && optBeq (runT c false) (expT c false) &&
    optBeq (runN c) (expN c) && optBeq (runNT c 0 true) (expNT c 0 true) &&
    optBeq (runNT c (if c = 0 then 0 else 2) false) (expNT c (if c = 0 then 0 else 2) false) &&
    optBeq (runNT c 1 true) (expNT c 1 true) &&
    optBeq (runR0 c) (expR0 c) && (List.range 7).all fun l => optBeq (runPC c l) (expPC c l)
def okCoord (c : Nat) : Bool := okF c && okC c && okQ c && okS c && okChk c && okStp c && okLc c && okTail c
def okGlobal : Bool := optBeq runSK expSK && optBeq runFor expFor && optBeq runJ expJ && okHorn
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-- The unchanged chain and coefficient region excludes the replaced field and leaf hooks. -/
def coordLookW (c n : Nat) : Option (BitVec 32) := (coordCodesW.getD c [])[n - cbase c]?
/-- Witness stack (charge 86): the installed coordinate windows (`coordCodesW`), the FTS G stubs at 21200..21229 and
the C4 arena. -/
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c < n ∧ n < lI c then coordLookW c n
  else if 21200 ≤ n ∧ n < 21230 then ftsStub[n - 21200]? else arenaLook n
structure Fetch (im : Image) : Prop where
  head : LookOK im headLook
  coordinate : ∀ c, c < 9 → LookOK im (coordLook c)
theorem coordLook_ok {im : Image} (h : Fetch im) {c : Nat} (hc : c<9) : LookOK im (coordLook c) := h.coordinate c hc
theorem headLook_ok {im : Image} (h : Fetch im) : LookOK im headLook := h.head
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
/-! Witness stack: FTS G chains 1, 3. The HASH site `lui a0` becomes `jal t3,stub`; the stub copies the header to
`CHAINW+64`, zeroes `CHAINW+80..111`, hashes `CHAINW+48..111` into `CHAINW+32` (interior: the high half lands on the
value slot `CHAINW+48`) or `CHAINW+48` (terminal step, low half), zeroes `CHAINW+32/40` and returns to the site + 6. -/
def stubAt (s : Nat) : Nat := if s = 4 then 21215 else 21200
def stubOut (s : Nat) : Nat := if s = 4 then CHAINW + 48 else CHAINW + 32
def hdrE (s : Nat) : E := .bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1))
def expStpG (c i s : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 24)), (.x10, cE (CHAINW + 48)), (.x11, cE 64), (.x12, cE (stubOut s)),
      (.x28, .c (pcOf (chkI c i s - 5))), (.x29, cE CHAINW)]
    [mwc (CHAINW + 104) (cE 0), mwc (CHAINW + 96) (cE 0), mwc (CHAINW + 88) (cE 0), mwc (CHAINW + 80) (cE 0),
      mwc (CHAINW + 72) (ldc (CHAINW + 24)), mwc (CHAINW + 64) (hdrE s), mwc (CHAINW + 16) (hdrE s)] []
    (stubAt s + 11) true 16 []
def knownG (c i s : Nat) : List (Reg × Word) := [(.x28, pcOf (chkI c i s - 5)), (.x29, BitVec.ofNat 64 CHAINW)]
def runPostG (c i s : Nat) : Option PRes :=
  pathAux scfg (coordLook c) [pcOf (chkI c i s)] 200 (pcOf (stubAt s + 12)) [] (σK (knownG c i s)) []
def expPostG (c i s : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (knownG c i s), [mwc (CHAINW + 40) (cE 0), mwc (CHAINW + 32) (cE 0)], []⟩,
    pcOf (chkI c i s), false, 3, 3, [], none⟩
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s =>
    if WCT9.ftsIsG i then optBeq (runStp c i s) (expStpG c i s) && optBeq (runPostG c i s) (expPostG c i s)
    else optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okCoord (c : Nat) : Bool := optBeq (runZ c) (expZ c) && okC c && okQ c && okS c && okChk c && okStp c && okLc c
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x20eb023,0x20eb423,0x1bb1313,0x1491393,0x730333,0xeeceb06f,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xe0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x203b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x640e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x303b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x40e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x403b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x680e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x503b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x80e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x603b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x6c0e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x703b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xc0e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x803b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x700e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x903b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def entry (c : Nat) : Nat := [22780,22970,23192,23394,23616,23818,24040,24242,24464].getD c 0
def hashPc (c : Nat) : Nat := [22800,23002,23217,23426,23641,23850,24065,24274,24493].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1726
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1111406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def runLeaf (c : Nat) : Option PRes := run (look c) [] (entry c) []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def branchE : E := .bin .and (.reg .x18) (cE 1)
def branchShift (k : Nat) : E := .bin .sll branchE (cE k)
def physicalE (c : Nat) : E := if first c then .reg .x18 else .bin .add (.bin .srl (.reg .x18) (cE 1)) (branchShift 6)
def outOffset (c : Nat) : E := .bin .sll (.bin .add (physicalE c) (cE 128)) (cE 4)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add (branchShift 5) (cE (0x67000+64*(c/2)+off)) else cE (FORW+32*c+off)
def padLoad (c off : Nat) : E := if c=0 then cE 0 else .ld (padAddr c off)
def headerE (c : Nat) : E := .bin .add
  (.bin .add (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537+65536*(c+1)))
def leafRegs (c : Nat) : List (Reg × E) :=
  [(.x6,outOffset c),(.x7,if first c then cE (1537+65536*(c+1)) else branchShift 6),
   (.x10,cE LEAFW),(.x11,cE 128),(.x12,.bin .add (outOffset c) (cE HEAPW)),
   (.x28,if c=0 then .reg .x28 else padAddr c 0),(.x29,cE LEAFW)]
def leafMem (c : Nat) : SymMem :=
  [mwc (LEAFW+24) (cE 0),mwc (LEAFW+16) (headerE c),mwc (LEAFW+40) (padLoad c 8),mwc (LEAFW+32) (padLoad c 0)]
def leafObl (c : Nat) : List Oblig := if c%2=1 then
  [.valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2)+8)⟩ 8,
   .valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2))⟩ 8] else []
def cycles (c : Nat) : Nat := if c=0 then 23 else if c%2=1 then 32 else if c=8 then 29 else 25
def expected (c : Nat) : PRes := pres (leafRegs c) (leafMem c) (leafObl c) (hashPc c) true (cycles c) []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0xe6ceb06f,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x180006f,0x653823,0x1253c23,0x400393,0x796463,0x40006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x203b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x10e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x303b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x650e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x403b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x50e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x503b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x690e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x603b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x90e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x703b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x6d0e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x803b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0xd0e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x903b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x710e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def entry (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
def hashPc (c : Nat) : Nat := [22840, 23058, 23264, 23482, 23688, 23906, 24112, 24330, 24545].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1729
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1911406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def dirs (mode : Nat) : List Dir := if mode=0 then [.br false] else [.br true,.br (mode=2)]
def runNode (c mode : Nat) : Option PRes := runA (look c) [] (entry c) (dirs mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify

def loE (c : Nat) : E := .bin .add (.bin .sll (.reg .x22) (cE 27)) (cE (1537+65536*(c+1)))
def hdrLo (c mode : Nat) : E := if mode=0 then .bin .sub (loE c) (.reg .x18) else loE c
def hdrHi (mode : Nat) : E := if mode=0 then cE 0 else .reg .x18
def padShift : E := .bin .sll (.bin .add (.bin .srl (.reg .x18) (cE 1)) (cE (2^64-2))) (cE 5)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add padShift (cE (0x67000+64*(c/2)+16+off)) else cE (FORW+32*c+16+off)
def padWord (c mode off : Nat) : E := if mode=1 ∧ c≠0 then .ld (padAddr c off) else cE 0

def regs (c mode : Nat) : List (Reg × E) :=
  [(.x6,if mode=1 ∧ c≠0 then padWord c mode 0 else hdrLo c mode),
   (.x7,if mode=1 ∧ c≠0 then padWord c mode 8 else cE (if mode=0 then 8 else 4)),
   (.x10,cE NODEW),(.x11,cE 64),(.x12,cE NOUTW),
   (.x28,if mode=1 ∧ c≠0 then padAddr c 0 else .bin .add sh5 (cE HEAPW))]
def mem (c mode : Nat) : SymMem :=
  [mwc (NODEW+40) (padWord c mode 8),mwc (NODEW+32) (padWord c mode 0),
   mwc (NODEW+24) (hdrHi mode),mwc (NODEW+16) (hdrLo c mode),
   mwc (NODEW+56) (nodeLd 24),mwc (NODEW+48) (nodeLd 16),mwc (NODEW+8) (nodeLd 8),mwc NODEW (nodeLd 0)]
def readObl : List Oblig :=
  [.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 NODEW⟩,.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,
   .valid (nodeAddr 24) 8,.ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 NODEW⟩,
   .ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,.valid (nodeAddr 16) 8,
   .valid (nodeAddr 8) 8,.valid (nodeAddr 0) 8]
def padReadAddr (c off : Nat) : Addr := ⟨some padShift,BitVec.ofNat 64 (0x67000+64*(c/2)+16+off)⟩
def padReadObl (c off : Nat) : List Oblig :=
  ([0,8,48,56,16,24].map fun n=>Oblig.ne (padReadAddr c off) ⟨none,BitVec.ofNat 64 (NODEW+n)⟩) ++
    [.valid (padReadAddr c off) 8]
def obligations (c mode : Nat) : List Oblig :=
  (if mode=1 ∧ c%2=1 then padReadObl c 8 ++ padReadObl c 0 else []) ++ readObl

def branches (mode : Nat) : List Br :=
  if mode=0 then [⟨.ltu,.reg .x18,cE 8,false⟩] else
    [⟨.ltu,.reg .x18,cE 4,mode=2⟩,⟨.ltu,.reg .x18,cE 8,true⟩]
def cycles (c mode : Nat) : Nat :=
  if mode=1 then if c=0 then 32 else if c%2=1 then 38 else 34 else if c=0 then 31 else 29
def expected (c mode : Nat) : PRes :=
  pres (regs c mode) (mem c mode) (obligations c mode) (hashPc c) true (cycles c mode) (branches mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def hookWords : List (BitVec 32) := bv_list% 32 [0x7480a06f,0x1b90906f,0x4a10806f,0x7390706f,0x2240706f,0x4bc0606f,0x7a40506f,0x2410406f,0x5290306f]
def hookLook (c n : Nat) : Option (BitVec 32) := if n=lI c then some (hookWords.getD c 0) else none
def runHook (c : Nat) : Option PRes := run (hookLook c) [entry c] (lI c) []
def expectedHook (c : Nat) : PRes := pres [] [] [] (entry c) false 1 []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the first word after each leaf `ecall` is a hook `jal zero,stub`. The stub copies the HIGH half
of the leaf answer (`a2+16..31`) onto its LOW half (`a2+0..15`) when the physical child is even (heap `128+p`
even), re-executes the displaced instruction and jumps back to the word after the hook. -/
def words0 : List (BitVec 32) := bv_list% 32 [0xa94ff06f,0x8000313,0x696663,0x7f00913,0x80006f,0xaadf406f]
def words1 : List (BitVec 32) := bv_list% 32 [0xfadfe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xfdcf506f]
def words2 : List (BitVec 32) := bv_list% 32 [0xc95fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xd24f606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x991fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xa5cf706f]
def words4 : List (BitVec 32) := bv_list% 32 [0xf1cfe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xfa1f706f]
def words5 : List (BitVec 32) := bv_list% 32 [0xc18fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xcd9f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x900fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xa21f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0xce0fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xf54fa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x9b8fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xc78fb06f]
def stub0 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x5550006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x380106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x3540106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x6540106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0xcd0106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3cd0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x6e90106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3050106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x62d0106f]
def entry (c : Nat) : Nat := [22801, 23003, 23218, 23427, 23642, 23851, 24066, 24275, 24494].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 leaf stub entry of coordinate `c` (in the former nop gaps of `signCode_85`). -/
def stubPc (c : Nat) : Nat := [21942, 21958, 21975, 21991, 22049, 22065, 22082, 22539, 22556].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def dirs (c mode : Nat) : List Dir := if first c then [.br (mode≠2)] else
  if mode=2 then [.br true] else [.br false,.br (mode=1)]
/-- `odd`: the physical child is odd (the stub's `bne` is taken and the LOW half is kept). -/
def runNext (c mode : Nat) (odd : Bool) : Option PRes :=
  run (look c) [leafI c,nodePc c] (entry c) (.br odd :: dirs c mode)
def nextE (c mode : Nat) : E := if mode=2 then cE 127 else if first c then x18p1 else
  if mode=1 then cE 1 else .bin .add (.reg .x18) (cE 2)
def cycles (c mode : Nat) : Nat := if first c then if mode=2 then 5 else 4 else if mode=2 then 4 else 7
def branches (c mode : Nat) : List Br := if first c then [⟨.ltu,x18p1,cE 128,mode≠2⟩] else
  if mode=2 then [⟨.eq,.reg .x18,cE 127,true⟩] else
  [⟨.eq,.reg .x18,cE 126,mode=1⟩,⟨.eq,.reg .x18,cE 127,false⟩]
/-- The stub's parity test: physical parity is raw bit 0 on A coordinates and raw bit 1 on B/C coordinates. -/
def parityE (c : Nat) : E := if first c then .bin .and (.reg .x18) (cE 1) else
  .bin .and (.bin .srl (.reg .x18) (cE 1)) (cE 1)
def a2A (off : Nat) : Addr := ⟨some (.reg .x12),BitVec.ofNat 64 off⟩
def a2Ld (off : Nat) : E := .ld (.bin .add (.reg .x12) (cE off))
def stubMem (odd : Bool) : SymMem := if odd then [] else [(a2A 8,a2Ld 24),(a2A 0,a2Ld 16)]
def stubObl (odd : Bool) : List Oblig := if odd then [] else
  [.valid (a2A 8) 8,.valid (a2A 24) 8,.valid (a2A 0) 8,.valid (a2A 16) 8]
def stubCycles (c : Nat) (odd : Bool) : Nat := (if first c then 4 else 5)+(if odd then 0 else 4)
def expected (c mode : Nat) (odd : Bool) : PRes := pres
  [(.x6,cE (if first c then 128 else if mode=2 then 127 else 126)),(.x18,nextE c mode)]
  (stubMem odd) (stubObl odd) (if mode=2 then nodePc c else leafI c) false (cycles c mode+stubCycles c odd)
  (branches c mode++[⟨.ne,parityE c,cE 0,odd⟩])
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the fold half selector is a hook `jal zero,stub` (A/B: the former `addi t2,zero,8|4`; C: the
displaced `lui t4,0x51`). The stub selects the HIGH half (`t3 += 16`) iff `heap < halfLimit` (A/B tops, as in
#884) or `heap ≥ 16` and even (C1), and jumps back past Ghost's (now dead) `bgeu`/`addi t3` pair.
Stage 2 (merged singleton "Cm"): the C stub (22565..22573, 9 words) has the A/B shape with the first test
`heap = 2` (`addi t1,s2,-2; beq t1,zero,HI`) in place of `heap < halfLimit`, so the singleton's left top node
(heap 2) keeps the HIGH half; heap 3 keeps the LOW half. -/
def words0 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xa0cff06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf2691ee3]
def words1 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xee9fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words2 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xbf1fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words3 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x8cdfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words4 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xe78fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words5 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xb54fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words6 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x85cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words7 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xc1cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words8 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x904fe06f,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf26916e3]
def stub0 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x5e50006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1080106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x4000106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7240106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1790106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x49d0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7950106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x3d50106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0xffe90313,0x30a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x51eb7,0x6e10106f]
def entry (c : Nat) : Nat := [22841, 23059, 23265, 23483, 23689, 23907, 24113, 24331, 24546].getD c 0
def finishPc (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 fold stub entry of coordinate `c`. -/
def stubPc (c : Nat) : Nat := [21950, 21967, 21983, 22000, 22057, 22074, 22090, 22548, 22565].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def limit (c : Nat) : Nat := if first c then 3 else 1
def halfLimit (c : Nat) : Nat := if first c then 8 else 4
/-- The stub's path class of heap `h`: `0` a top heap below `halfLimit` (A/B) or the singleton's heap 2 (C, stage 2)
(HIGH), `1` another heap below 16 (LOW), `2` an odd heap `≥ 16` (LOW), `3` an even heap `≥ 16` (HIGH, C1). -/
def cls (c h : Nat) : Nat :=
  if (c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2) then 0 else if h<16 then 1 else if h%2=1 then 2 else 3
def clsHigh (_c k : Nat) : Bool := decide (k=0 ∨ k=3)
/-- Branch directions of the stub (the same for every coordinate since stage 2). -/
def stubDirs (_c k : Nat) : List Dir :=
  if k=0 then [.br true] else if k=1 then [.br false,.br true] else if k=2 then [.br false,.br false,.br true]
  else [.br false,.br false,.br false]
def dirs (c k : Nat) (back : Bool) : List Dir := stubDirs c k++[.br back]
def runTail (c k : Nat) (back : Bool) : Option PRes :=
  run (look c) [nodePc c,finishPc c] (entry c) (dirs c k back)
def halfOff (high : Bool) : Nat := if high then 16 else 0
def outWord (high : Bool) (off : Nat) : E := ldc (NOUTW+halfOff high+off)
/-- Tail cycles by class (stage 2: the singleton's 18/19/21/22 equal A/B's). -/
def cycles (_c k : Nat) : Nat := if k=0 then 18 else if k=1 then 19 else if k=2 then 21 else 22
def ltB (n : Nat) (d : Bool) : Br := ⟨.ne,.bin .sltu (.reg .x18) (cE n),cE 0,d⟩
def oddB (d : Bool) : Br := ⟨.ne,.bin .and (.reg .x18) (cE 1),cE 0,d⟩
/-- Stage 2 (C stub): `addi t1,s2,-2; beq t1,zero,HI`, i.e. `heap = 2`. -/
def eq2B (d : Bool) : Br := ⟨.eq,.bin .add (.reg .x18) (cE (2^64-2)),cE 0,d⟩
/-- The stub's first test: `heap < halfLimit` on A/B, `heap = 2` on the singleton C. -/
def topB (c : Nat) (d : Bool) : Br := if c=8 then eq2B d else ltB (halfLimit c) d
def stubBranches (c k : Nat) : List Br :=
  if k=0 then [topB c true] else if k=1 then [ltB 16 true,topB c false]
  else if k=2 then [oddB true,ltB 16 false,topB c false]
  else [oddB false,ltB 16 false,topB c false]
def branches (c k : Nat) (back : Bool) : List Br := ⟨.ne,x18m1,cE (limit c),back⟩::stubBranches c k
def expected (c k : Nat) (back : Bool) : PRes :=
  pres [(.x6,cE (limit c)),(.x7,outWord (clsHigh c k) 8),(.x18,x18m1),
    (.x28,cE (NOUTW+halfOff (clsHigh c k))),(.x29,.bin .add sh4 (cE HEAPW))]
    [(heapAddr 8,outWord (clsHigh c k) 8),(heapAddr 0,outWord (clsHigh c k) 0)]
    [.valid (heapAddr 8) 8,.valid (heapAddr 0) 8]
    (if back then nodePc c else finishPc c) false (cycles c k) (branches c k back)
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xe8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x40e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x6c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def entry (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def pathPc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def source (c : Nat) : Nat := HEAPW+(if first c then 64 else 32)
def target (c : Nat) : Nat := if first c then 0x67000+64*(c/2) else FORW+32*(c+1)
def nwords (c : Nat) : Nat := if first c then 8 else 4
def loBit : E := .bin .sll (.bin .and (.reg .x24) (cE 1)) (cE 6)
def physicalE (c : Nat) : E := if first c then .reg .x24 else .bin .add (.bin .srl (.reg .x24) (cE 1)) loBit
def mem (c : Nat) : SymMem := ((List.range (nwords c)).reverse.map fun k=>mwc (target c+8*k) (ldc (source c+8*k)))
def expected (c : Nat) : PRes := pres
  [(.x6,if first c then ldc (source c+48) else loBit),(.x7,ldc (source c+8*(nwords c-1))),
   (.x24,.bin .add (physicalE c) (cE 128)),(.x28,cE (source c)),(.x29,cE (target c))]
  (mem c) [] (pathPc c) false ((words c).length) []
def runFinish (c : Nat) := runA (look c) [pathPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x70e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x90e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xa0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xb0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words1 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x140e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x150e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x160e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x170e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x180e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x190e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x1a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words2 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x210e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x220e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x230e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x240e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x250e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x260e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words3 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x300e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x310e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x320e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x330e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x340e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words4 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x400e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words5 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x480e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x490e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words6 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x550e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x560e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x570e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x580e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x590e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x5a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words7 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x620e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x630e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x650e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x660e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x670e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words8 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x6f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x710e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x730e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x740e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x750e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def basePc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def entry (c level : Nat) : Nat := basePc c+12*level
def look (c n : Nat) : Option (BitVec 32) := if basePc c≤n then (words c)[n-basePc c]? else none
def levels (c : Nat) : Nat := if c<8 ∧ c%2=0 then 6 else 7
def offsetE (level : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.reg .x24) (cE level)) (cE 1)) (cE 4)
def address (level off : Nat) : Addr := ⟨some (offsetE level),BitVec.ofNat 64 (HEAPW+off)⟩
def word (level off : Nat) : E := .ld (.bin .add (offsetE level) (cE (HEAPW+off)))
def target (c level : Nat) : Nat := slotV c 6+16*level
def expected (c level : Nat) : PRes := pres
  [(.x6,word level 0),(.x7,word level 8),(.x28,.bin .add (offsetE level) (cE HEAPW)),(.x29,cE (target c level))]
  [mwc (target c level+8) (word level 8),mwc (target c level) (word level 0)]
  [.valid (address level 8) 8,.valid (address level 0) 8] (entry c (level+1)) false 12 []
def runPath (c level : Nat) := runA (look c) [entry c (level+1)] (entry c level) []
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x7eb7,0xd0e8e93,0xeb023,0xeb423,0x891f506f]
def words1 : List (BitVec 32) := bv_list% 32 [0xda4f606f]
def words2 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x270e8e93,0xeb023,0xeb423,0xb0cf706f]
def words3 : List (BitVec 32) := bv_list% 32 [0x824f806f]
def words4 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x410e8e93,0xeb023,0xeb423,0xd89f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0xaa1f906f]
def words6 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x5b0e8e93,0xeb023,0xeb423,0x809fa06f]
def words7 : List (BitVec 32) := bv_list% 32 [0xd1cfb06f]
def words8 : List (BitVec 32) := bv_list% 32 [0xa5cfc06f]
def entry (c : Nat) : Nat := [22950, 23176, 23374, 23600, 23798, 24024, 24222, 24448, 24660].getD c 0
def nextPc (c : Nat) : Nat := [12238, 13297, 14357, 15417, 16476, 17536, 18596, 19655, 20715].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def target (c : Nat) : Nat := slotP c 6
def expected (c : Nat) : PRes := pres (if first c then [(.x29,cE (target c))] else [])
  (if first c then [mwc (target c+8) (cE 0),mwc (target c) (cE 0)] else []) [] (nextPc c) false (if first c then 5 else 1) []
def runEnd (c : Nat) := run (look c) [nextPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0xe3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb11f406f]
def words1 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x885f506f]
def words2 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd9cf606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb04f706f]
def words4 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x818f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd81f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xa99f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xffcfa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x25c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd14fb06f]
def entry (c : Nat) : Nat := [22765, 22955, 23177, 23379, 23601, 23803, 24025, 24227, 24449].getD c 0
def hookWord (c : Nat) : BitVec 32 := [0x4ec0b06f,0x7740a06f,0x2610906f,0x4f90806f,0x7e10706f,0x27c0706f,0x5640606f,0x7fc0506f,0x2e90406f].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def rawBit (c : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD c 0
def rankBit (c : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD c 0
def look (c n : Nat) : Option (BitVec 32) := if n=cbase c then some (hookWord c) else if entry c ≤ n then (words c)[n-entry c]? else none
def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (ldc (NBUF+8*(bit/64))) (cE (bit%64))) (cE (2^width-1))
def expected (c : Nat) : PRes := pres [(.x6,.bin .sll (fieldE (rankBit c) 10) (cE 2)),
  (.x24,fieldE (rawBit c) 7),(.x25,fieldE (rankBit c) 10),
  (.x28,.bin .add (.bin .sll (fieldE (rankBit c) 10) (cE 2)) (cE TBL))] [] [] (lwuI c) false ((words c).length+1) []
def runField (c : Nat) : Option PRes := run (look c) [lwuI c] (cbase c) []
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def base (expand : Bool) : Nat := if expand then 45056 else 22600
def signWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2869f063,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x20e37,0x160e0e13,0x18e3303,0x3235313,0x31700393,0x22737c63,0xa13,0x208b7,0x16088893,0xfebab7,0xa8a93,0x8bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x206cf863,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x1c6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x88bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x1a6cf063,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0x25cdc93,0x3ffcfc93,0x23300313,0x166cf463,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x126cf863,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x108bc83,0x19cdc93,0x3ffcfc93,0x23300313,0xe6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0x25cdc93,0x3ffcfc93,0x23300313,0xc6cf063,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x188bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x86cf463,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x188bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x46cf863,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x26c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x30900313,0x26a7263,0x20e37,0x160e0e13,0xe3b03,0x21b5b13,0x20e37,0x550e0e13,0x16e3023,0xaf9f406f,0x198993,0xd7dff06f]
def expandWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2a69f263,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x208b7,0x16088893,0x188b303,0x3235313,0x31700393,0x24737e63,0xff9a37,0xb90a0a13,0xa93,0x8bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x226c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x1e6c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x1a6c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x25c5c13,0x3ffc7c13,0x23300313,0x166c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x126c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x19c5c13,0x3ffc7c13,0x23300313,0xe6c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x25c5c13,0x3ffc7c13,0x23300313,0xa6c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x66c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x26c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x26c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x30900313,0x6af463,0x180006f,0x198993,0xd59ff06f]
def words (expand : Bool) : List (BitVec 32) := if expand then expandWords else signWords
 def look (expand : Bool) (n : Nat) : Option (BitVec 32) := if base expand ≤ n then (words expand)[n-base expand]? else none
 def trial (expand : Bool) : Nat := base expand+2
 def next (expand : Bool) : Nat := if expand then 45227 else 22762
 def fail (expand : Bool) : Nat := next expand+2
 def firstField (expand : Bool) : Nat := if expand then 45080 else 22626
 def field (expand : Bool) (k : Nat) : Nat := firstField expand+(if expand then 16 else 14)*k
 def rankLoad (expand : Bool) (k : Nat) : Nat := field expand k+6
 def corrLoad (expand : Bool) (k : Nat) : Nat := field expand k+(if expand then 14 else 12)
 def cap (expand : Bool) : Nat := field expand 9
 def accepted (expand : Bool) : Nat := cap expand+2
 def sumReg (expand : Bool) : Reg := if expand then .x21 else .x20
 def tableReg (expand : Bool) : Reg := if expand then .x20 else .x21
 def rankReg (expand : Bool) : Reg := if expand then .x24 else .x25
 def addrReg (expand : Bool) : Reg := if expand then .x6 else .x28
 def tableBase (expand : Bool) : Nat := if expand then 0xff8b90 else 0xfeb000
 def correctionOffset (expand : Bool) (k : Nat) : Nat := (if expand then 1536 else 1024)+(if SharedLeaf.first k then 0 else 32)
 def fieldAddr (bit : Nat) : Addr := ⟨some (.reg .x17),BitVec.ofNat 64 (8*(bit/64))⟩
 def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (.ld (fieldAddr bit).toE) (cE (bit%64))) (cE (2^width-1))
 def rankE (k : Nat) : E := fieldE (SharedField.rankBit k) 10
 def costBit (k : Nat) : Nat := SharedField.rawBit k+(if SharedLeaf.first k then 0 else 1)
 def costE (k : Nat) : E := fieldE (costBit k) 5
 def gateE : E := .bin .srl (ldc (NBUF+24)) (cE 50)
 def expectedHead (expand reject : Bool) : PRes := pres [(.x6,cE (2^21))] [] []
   (if reject then fail expand else trial expand+3) false 3 [⟨.geu,.reg .x19,cE (2^21),reject⟩]
 def expectedTrial (expand : Bool) : PRes := pres [(.x28,cE DIG),(.x10,cE DIG),(.x11,cE 64),(.x12,cE NBUF)]
   [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] [] (base expand+14) true 9 []
 def expectedGate (expand reject : Bool) : PRes := pres [((if expand then .x17 else .x28),cE NBUF),(.x6,gateE),(.x7,cE 791)] [] []
   (if reject then next expand else base expand+21) false 6 [⟨.geu,gateE,cE 791,reject⟩]
 def expectedInit (expand : Bool) : PRes := pres (if expand then [(.x20,cE (tableBase expand)),(.x21,cE 0)]
   else [(.x20,cE 0),(.x17,cE NBUF),(.x21,cE (tableBase expand))]) [] [] (firstField expand) false (if expand then 3 else 5) []
 def expectedRank (expand : Bool) (k : Nat) (reject : Bool) : PRes := pres [(rankReg expand,rankE k),(.x6,cE 563)] [] [.valid (fieldAddr (SharedField.rankBit k)) 8]
   (if reject then next expand else field expand k+5) false 5 [⟨.geu,rankE k,cE 563,reject⟩]
 def expectedRankAddr (expand : Bool) (k : Nat) : PRes := pres [(addrReg expand,.bin .add (.reg (tableReg expand)) (.reg (rankReg expand)))] [] [] (rankLoad expand k) false 1 []
 def expectedCorrPrep (expand : Bool) (k : Nat) : PRes := pres
   [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6)),(.x24,costE k),
     (addrReg expand,if expand then .bin .add (costE k) (cE (tableBase expand+correctionOffset expand k))
       else .bin .add (.reg (tableReg expand)) (costE k))] [] [.valid (fieldAddr (costBit k)) 8] (corrLoad expand k) false (if expand then 7 else 5) []
 def expectedSum (expand : Bool) (k : Nat) : PRes := pres [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6))] [] [] (field expand (k+1)) false 1 []
 def expectedCap (expand reject : Bool) : PRes := pres [(.x6,cE 777)] [] [] (if reject then next expand else accepted expand) false 2
   [⟨.geu,.reg (sumReg expand),cE 777,reject⟩]
 def expectedNext (expand : Bool) : PRes := pres [(.x19,.bin .add (.reg .x19) (cE 1))] [] [] (trial expand) false 2 []
 def rankLbuWord (expand : Bool) : BitVec 32 := if expand then 0x00034303 else 0x000e4303
 def corrLbuWord (expand : Bool) (k : Nat) : BitVec 32 := if expand then 0x00034303 else if SharedLeaf.first k then 0x400e4303 else 0x420e4303
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

theorem look_of_code {im : Image} (m : Bool)
    (hc : CodeAt im (pcOf (base m)) (words m)) : LookOK im (look m) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hn
    have hb : base m<2^30 := by cases m <;> decide
    have hh:=codeAt_get_word hb hc hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedDigest
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart0 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_0 : okF 0 = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
private theorem component_okTail_0 : okTail 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_okF_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, component_okTail_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_0 : SigGolfCandidate.T3M.Verify.optBeq (runZ 0) (expZ 0) = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_z_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart1 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_1 : okF 1 = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
private theorem component_okTail_1 : okTail 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_okF_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, component_okTail_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_1 : SigGolfCandidate.T3M.Verify.optBeq (runZ 1) (expZ 1) = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_z_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
