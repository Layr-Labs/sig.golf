import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Lv
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactLoop
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def WIT : Nat := 0x800
def SNAP2 : Nat := 0x300000
/-- Nested FTS (r1-1): the final witness base (the frontier's was `WIT`). -/
def WOUT : Nat := 0x4c0
def copyRegs (src dst n ret : Nat) : RegFile :=
  (((RegFile.init.set .x1 (.c (pcOf ret))).set .x10 (.c (BitVec.ofNat 64 src))).set .x11
    (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def zeroRegs (dst n ret : Nat) : RegFile :=
  ((RegFile.init.set .x1 (.c (pcOf ret))).set .x11 (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def copyTab : List (Nat × Nat × Nat × Nat) :=
  [(42142, WIT, SNAP2, 2729), (42154, SNAP2, WIT, 8)] ++
  (List.range 9).map (fun q => (42161 + 7 * q, SNAP2 + 64 + 896 * (8 - q), WIT + 64 + 816 * q, 104)) ++
  [(42224, SNAP2 + 8136, WIT + 7424, 528), (42235, SNAP2 + 8136 + 64 * 66 + 64 * 7, WIT + 11648 + 16 * 25, 344),
   (42408, SNAP2 + 8136 + 64 * 116 + 64 * 6, WIT + 14800 + 16 * 20, 344),
   (42557, SNAP2 + 8136 + 64 * 165 + 64 * 6, WIT + 17872 + 16 * 20, 344)]
theorem run_snap : symRun cfgC cSnap (pcOf 42142) 40 =
    some ⟨⟨copyRegs WIT SNAP2 2729 42149, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
theorem run_zero2 : symRun cfgC cZero2 (pcOf 42149) 40 =
    some ⟨⟨zeroRegs WOUT 2510 42154, [], []⟩, .c (pcOf 42137), .jump, 5, 5⟩ := by kernel_rfl
theorem run_hdr : symRun cfgC cHdr (pcOf 42154) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf 33117), .jump, 1, 1⟩ := by kernel_rfl
theorem run_ctr : symRun cfgC cCtr (pcOf 33117) 40 =
    some ⟨⟨copyRegs (SNAP2 + 32) 1248 2 (33117 + 5), [], []⟩, .c (pcOf 42130), .jump, 5, 5⟩ := by kernel_rfl
theorem run_preg (c : Nat) (hc : c < 9) : symRun cfgC (cPReg c) (pcOf (pregAt c)) 40 =
    some ⟨⟨copyRegs (SNAP2 + 64 + 896 * c) (8560 - 896 * c) 112 (pregAt c + 6), [], []⟩, .c (pcOf 42130), .jump,
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
theorem run_reg (k : Nat) (hk : k < 9) : symRun cfgC (cReg k) (pcOf (regAt k)) 40 =
    some ⟨⟨copyRegs (SNAP2 + 64 + 896 * k) (WIT + 64 + 816 * (8 - k)) 104 (regAt k + 7), [], []⟩,
      .c (pcOf 42130), .jump, 7, 7⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_top : symRun cfgC cTop (pcOf 42224) 40 =
    some ⟨⟨copyRegs (SNAP2 + 8136) (WIT + 7424) 528 42231, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
def chAt (lay : Nat) : Nat := if lay = 1 then 42235 else if lay = 2 then 42408 else 42557
def cCh (lay : Nat) : List (BitVec 32) := if lay = 1 then cCh1 else if lay = 2 then cCh2 else cCh3
def chSrc (lay : Nat) : Nat := SNAP2 + 8136 + 64 * (if lay = 1 then 66 + 7 else if lay = 2 then 116 + 6 else 165 + 6)
def chDst (lay : Nat) : Nat := lvDst lay + 16 * (if lay = 1 then 25 else 20)
theorem run_ch (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : symRun cfgC (cCh lay) (pcOf (chAt lay)) 40 =
    some ⟨⟨copyRegs (chSrc lay) (chDst lay) 344 (chAt lay + 7), [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by
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
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 42137 ∧ t.getReg .x11 = BitVec.ofNat 64 WOUT ∧
      t.getReg .x12 = BitVec.ofNat 64 2510 ∧ t.getReg .x1 = pcOf 42154 ∧
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
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
    have hS : 0x300000 ≤ lvSrc lay L ∧ lvSrc lay L + 64 ≤ 0x300000 + 21832 := by
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
theorem plMem_out (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) (A : Nat) (hA : A < 1216 ∨ 9472 ≤ A) :
    plMem M Q A = M A := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have hb := hslot_bound M Q
    have hd : hdst Q + 160 ≤ 9472 ∧ 1216 ≤ hdst Q := by unfold hdst; omega
    simp only [plMem]
    rw [if_neg (by omega), if_neg (by omega), ih (by omega)]
/-- The nine region copies of P_final: region `c` (112 words) from the staging snapshot to `8560 - 896 c`. -/
def regsMem (M : Nat → Word) (Q : Nat) (A : Nat) : Word :=
  if 0 < Q ∧ 9456 - 896 * Q ≤ A ∧ A < 9456 ∧ A % 8 = 0 then
    M (SNAP2 + 64 + 896 * ((9455 - A) / 896) + (A - (8560 - 896 * ((9455 - A) / 896))))
  else M A
theorem regsMem_succ (M : Nat → Word) (Q : Nat) (hQ : Q < 9) (A : Nat) :
    (if 8560 - 896 * Q ≤ A ∧ A < 8560 - 896 * Q + 8 * 112 ∧ (A - (8560 - 896 * Q)) % 8 = 0 then
      M (SNAP2 + 64 + 896 * Q + (A - (8560 - 896 * Q))) else regsMem M Q A) = regsMem M (Q + 1) A := by
  unfold regsMem
  by_cases h1 : 8560 - 896 * Q ≤ A ∧ A < 8560 - 896 * Q + 8 * 112 ∧ (A - (8560 - 896 * Q)) % 8 = 0
  · rw [if_pos h1, if_pos (by omega), show (9455 - A) / 896 = Q by omega]
  · rw [if_neg h1]
    by_cases h2 : 0 < Q ∧ 9456 - 896 * Q ≤ A ∧ A < 9456 ∧ A % 8 = 0
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
def ctrMem (M : Nat → Word) (A : Nat) : Word :=
  if 1248 ≤ A ∧ A < 1248 + 8 * 2 ∧ (A - 1248) % 8 = 0 then M (SNAP2 + 32 + (A - 1248)) else M A
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem pregs_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (pregAt 0)) :
    ∀ Q ≤ 9, ∃ t, Steps im u (679 * Q) (679 * Q) t ∧ t.pc = pcOf (pregAt Q) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = regsMem M0 Q A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hS : SNAP2 = 0x300000 := rfl
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
    by_cases h1 : 8560 - 896 * Q ≤ A ∧ A < 8560 - 896 * Q + 8 * 112 ∧ (A - (8560 - 896 * Q)) % 8 = 0
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
def chMem (M : Nat → Word) (lay : Nat) (A : Nat) : Word :=
  if chDst lay ≤ A ∧ A < chDst lay + 8 * 344 ∧ (A - chDst lay) % 8 = 0 then M (chSrc lay + (A - chDst lay)) else M A
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
def layLen (lay : Nat) : Nat := 2072 + rowLen lay + 23 * lvH lay + 4
theorem chDst_eq (lay : Nat) : chDst lay = lvDst lay + pathTop lay := by unfold chDst pathTop; rfl
theorem layMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx A : Nat)
    (hA : A < lvDst lay ∨ chDst lay + 8 * 344 ≤ A) : layMem M lay idx A = M A := by
  have hA' := hA
  have hce := chDst_eq lay
  have hro := rootOff_lt lay hl (lroute lay idx) (lroute_lt lay idx)
  rw [chDst_eq] at hA'
  unfold layMem
  rw [if_neg (by omega), lvsMem_out _ lay hl _ (lroute_lt lay idx) _ le_rfl _ (by omega)]
  unfold chMem; rw [if_neg (by omega)]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
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
  have hsrc : chSrc lay % 8 = 0 ∧ 0x300000 + 8136 ≤ chSrc lay ∧ chSrc lay + 8 * 344 ≤ 0x300000 + 21832 := by
    interval_cases lay <;> decide
  have hdst : chDst lay % 8 = 0 ∧ chDst lay + 8 * 344 ≤ 0x800 + 20944 ∧
      lvDst lay % 16 = 0 ∧ 0x800 + 11648 ≤ lvDst lay := by
    interval_cases lay <;> decide
  obtain ⟨u1, s1, p1, r1, m1⟩ := copyPhase hc hcode (run_ch lay ⟨h1, h4⟩) u hpc (by norm_num) (by norm_num)
    hsrc.1 (by omega) hdst.1 (by omega) (Or.inl (by omega))
  have hm1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = chMem M0 lay A := fun A hA => by
    rw [m1 A hA]; unfold chMem; split
    · rw [hM _ (by omega)]
    · rw [hM A hA]
  have hp1 : LPlanAt u1 := fun k hk => by
    rw [hm1 _ (by omega)]; unfold chMem; rw [if_neg (by omega), ← hM _ (by omega)]; exact hp k hk
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
  have hDu : lvDst lay ≤ 0x800 + 17872 := by unfold lvDst; split_ifs <;> omega
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
  have hS : 0x300000 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x300000 + 21832 := by
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
def tailMem (M : Nat → Word) (A : Nat) : Word :=
  if A = WIT + 20968 then LoadKind.wu.fromWord (M (SNAP2 + 16)) 0
  else if A = WIT + 20960 then 0
  else if A = WIT + 20952 then M (SNAP2 + 8)
  else if A = WIT + 20944 then M SNAP2
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
      key 23016 (by norm_num), key 23008 (by norm_num), key 23000 (by norm_num), key 22992 (by norm_num)]
    unfold tailMem
    simp only [show WIT = 0x800 from rfl, show SNAP2 = 0x300000 from rfl, Nat.reduceAdd]
    rfl
def snapMem (M : Nat → Word) (A : Nat) : Word :=
  if SNAP2 ≤ A ∧ A < SNAP2 + 8 * 2729 ∧ (A - SNAP2) % 8 = 0 then M (WIT + (A - SNAP2)) else M A
/-- Zeroing of 2510 words from `WOUT` (to `WIT + 19248`; everything above is rewritten by the layer-3 chain copy
and the tail). -/
def zMem (M : Nat → Word) (A : Nat) : Word :=
  if WOUT ≤ A ∧ A < WOUT + 8 * 2510 ∧ (A - WOUT) % 8 = 0 then 0 else M A
def topMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT + 7424 ≤ A ∧ A < WIT + 7424 + 8 * 528 ∧ (A - (WIT + 7424)) % 8 = 0 then M (SNAP2 + 8136 + (A - (WIT + 7424)))
  else M A
/-- Nested FTS (r1-1): memory after the zeroing, the L3 counter copy, the nine region copies and the nine hold
placements of P_final. -/
def stMem (M : Nat → Word) (A : Nat) : Word := plMem (regsMem (ctrMem (zMem (snapMem M))) 9) 9 A
def run2Mem (M : Nat → Word) (idx : Nat) (A : Nat) : Word :=
  tailMem (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) A
theorem stMem_out (M : Nat → Word) (A : Nat) (hA : A < WOUT ∨ SNAP2 + 8 * 2729 ≤ A) : stMem M A = M A := by
  have hW : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem stMem_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    stMem M (SNAP2 + x) = M (WIT + x) := by
  have hW : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl _ (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show SNAP2 + x - SNAP2 = x by omega]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run2_spec (s : MachineState) (hpc : s.pc = pcOf 42142) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hix : s.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 idx) (hp : LPlanAt s)
    (hfl : ∀ c < 9, ∃ f < 2, s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f) :
    ∃ t, Steps im s 42535 42535 t ∧ t.pc = pcOf 42716 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = run2Mem (fun B => s.getMem (BitVec.ofNat 64 B)) idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨u1, s1, p1, r1, m1⟩ := copyPhase hc (code_cSnap hc) run_snap s hpc (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have e1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = snapMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => by rw [m1 A hA]; rfl
  obtain ⟨u2a, s2a, p2a, x11, x12, x1, r2a, f2a⟩ := zeroSet_spec (code_cZero2 hc) u1 (by rw [p1])
  obtain ⟨u2, s2, p2, r2, m2⟩ := zero_spec hc u2a p2a WOUT 2510 42154 x11 x12 x1 (by norm_num) (by norm_num)
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
def zoneLay (o : Nat) : Nat := if o < 14800 then 1 else if o < 17872 then 2 else 3
def pathOut (M : Nat → Word) (lay r p : Nat) : Word :=
  if p = rootOff lay r then 1#64 else
  match (List.range (lvH lay)).find? (fun j => decide (lvHit lay r j p)) with
  | some j => M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))
  | none => 0
def out2old (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 64 then M (WIT + o)
  else if o < 7424 then
    M (WIT + 64 + 896 * (8 - min ((o - 64) / 816) 8) + (o - 64 - 816 * min ((o - 64) / 816) 8))
  else if o < 11648 then M (WIT + o + 712)
  else if o < 20944 then
    (if o - (lvDst (zoneLay o) - WIT) < pathTop (zoneLay o) then
      pathOut M (zoneLay o) (lroute (zoneLay o) idx) (o - (lvDst (zoneLay o) - WIT))
    else M (chSrc (zoneLay o) - SNAP2 + WIT + (o - (chDst (zoneLay o) - WIT))))
  else if o = 20944 then M WIT
  else if o = 20952 then M (WIT + 8)
  else if o = 20960 then 0
  else LoadKind.wu.fromWord (M (WIT + 16)) 0
/-- Nested FTS (r1-1): output word at offset `o` from the final witness base `WOUT`. Below 8256 (header and the
nine regions) it is the P_final memory; above, the frontier's output shifted by 832. -/
def out2 (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 8256 then stMem M (WOUT + o) else out2old M idx (o - 832)
theorem lay_consts : lvDst 1 = 0x800 + 11648 ∧ lvDst 2 = 0x800 + 14800 ∧ lvDst 3 = 0x800 + 17872 ∧
    chDst 1 = 0x800 + 11648 + 400 ∧ chDst 2 = 0x800 + 14800 + 320 ∧ chDst 3 = 0x800 + 17872 + 320 := by
  unfold lvDst chDst; decide
theorem snap_read (M : Nat → Word) (idx x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) (SNAP2 + x) = M (WIT + x) := by
  have hS : SNAP2 = 0x300000 := rfl
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
theorem lays_low (M : Nat → Word) (idx A : Nat) (hA : A < WIT + 11648) :
    (layMem (layMem (layMem M 1 idx) 2 idx) 3 idx) A = M A := by
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 2 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 1 (by omega) idx A (Or.inl (by omega))]
theorem pre_low (M : Nat → Word) (A : Nat) (hA : WIT + 11648 ≤ A) (hA' : A < WIT + 19248) (h8 : (A - WIT) % 8 = 0) :
    topMem (stMem M) A = 0 := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold topMem
  rw [if_neg (by omega)]
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem pre_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    topMem (stMem M) (SNAP2 + x) = M (WIT + x) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
theorem layMem_zone (P : Nat → Word) (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx : Nat)
    (hP : ∀ x < 8 * 2729, x % 8 = 0 → P (SNAP2 + x) = M (WIT + x))
    (hZ : ∀ A, lvDst lay ≤ A → A < chDst lay → (A - WIT) % 8 = 0 → P A = 0)
    (o : Nat) (h1 : lvDst lay - WIT ≤ o) (h2 : o < chDst lay - WIT + 8 * 344) (h8 : o % 8 = 0) :
    layMem P lay idx (WIT + o) =
      if o - (lvDst lay - WIT) < pathTop lay then pathOut M lay (lroute lay idx) (o - (lvDst lay - WIT))
      else M (chSrc lay - SNAP2 + WIT + (o - (chDst lay - WIT))) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have hce := chDst_eq lay
  have hD : 0x800 + 11648 ≤ lvDst lay ∧ lvDst lay % 16 = 0 ∧ lvDst lay + pathTop lay + 8 * 344 ≤ 0x800 + 20944 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hsrc : 0x300000 + 8136 ≤ chSrc lay ∧ chSrc lay + 8 * 344 ≤ 0x300000 + 21832 ∧ chSrc lay % 8 = 0 := by
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
      unfold chMem
      rw [if_neg (by omega)]
      exact hZ _ (by omega) (by omega) (by omega)
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      have hh : lvHit lay (lroute lay idx) j (o - (lvDst lay - WIT)) := of_decide_eq_true hp'
      unfold lvHit at hh
      have hsp := sibS_padS_lt lay (lroute lay idx) j hl hr hj
      have hm := plan_mod16 lay (lroute lay idx) j
      have hls : 0x300000 + 8136 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x300000 + 21832 ∧ lvSrc lay j % 8 = 0 := by
        unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
      have hpl : 16 * plan lay (lroute lay idx) j ≤ sibS lay (lroute lay idx) j ∧
          sibS lay (lroute lay idx) j + 16 ≤ 16 * plan lay (lroute lay idx) j + 64 ∧
          padS lay (lroute lay idx) j = 16 * plan lay (lroute lay idx) j + 32 := by
        unfold sibS padS
        have : lroute lay idx / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      unfold chMem
      rw [if_neg (by omega)]
      have := hP (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) (by omega)
        (by omega)
      rw [show SNAP2 + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega] at this
      rw [this, show WIT + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j - SNAP2 + WIT + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega]
  · rw [if_neg hp, if_neg (show ¬ WIT + o = lvDst lay + rootOff lay (lroute lay idx) by omega),
      lvsMem_out _ lay hl _ hr _ le_rfl _ (Or.inr (by omega))]
    unfold chMem
    rw [if_pos (by omega)]
    have := hP (chSrc lay - SNAP2 + (WIT + o - chDst lay)) (by omega) (by omega)
    rw [show SNAP2 + (chSrc lay - SNAP2 + (WIT + o - chDst lay)) = chSrc lay + (WIT + o - chDst lay) by omega]
      at this
    rw [this, show WIT + (chSrc lay - SNAP2 + (WIT + o - chDst lay)) =
      chSrc lay - SNAP2 + WIT + (o - (chDst lay - WIT)) by omega]
theorem run2_zone_old (M : Nat → Word) (idx o : Nat) (hlo : 7424 ≤ o) (ho : o < 20976) (h8 : o % 8 = 0) :
    run2Mem M idx (WIT + o) = out2old M idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have hTs : ∀ x < 8 * 2729, x % 8 = 0 → topMem (stMem M) (SNAP2 + x) = M (WIT + x) :=
    fun x hx h => pre_snap M x hx h
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  unfold run2Mem tailMem out2old
  by_cases ht : 20944 ≤ o
  · have hs := fun x hx h => snap_read M idx x hx h
    rcases (show o = 20944 ∨ o = 20952 ∨ o = 20960 ∨ o = 20968 by omega) with rfl | rfl | rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      have := hs 0 (by omega) (by omega); simpa using this
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos rfl]
      exact hs 8 (by omega) (by omega)
    · rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      rw [hs 16 (by omega) (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases hl : o < 11648
    · rw [lays_low _ idx (WIT + o) (by omega), if_neg (show ¬ o < 64 by omega), if_neg (show ¬ o < 7424 by omega),
        if_pos (by omega)]
      unfold topMem
      rw [if_pos (by omega), show SNAP2 + 8136 + (WIT + o - (WIT + 7424)) = SNAP2 + (8136 + (o - 7424)) by omega,
        stMem_snap M _ (by omega) (by omega), show WIT + (8136 + (o - 7424)) = WIT + o + 712 by omega]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have hZ1 : ∀ A, lvDst 1 ≤ A → A < chDst 1 → (A - WIT) % 8 = 0 →
          topMem (stMem M) A = 0 := fun A h1 h2 h3 =>
        pre_low M A (by omega) (by omega) h3
      by_cases hz1 : o < 14800
      · have hzl : zoneLay o = 1 := by unfold zoneLay; rw [if_pos hz1]
        rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega)),
          layMem_out _ 2 (by omega) idx (WIT + o) (Or.inl (by omega))]
        exact layMem_zone (topMem (stMem M)) M 1 (by omega) idx hTs hZ1 o (by omega)
          (by omega) h8
      · have hP2 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (topMem (stMem M)) 1 idx
            (SNAP2 + x) = M (WIT + x) := fun x hx h => by
          rw [layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hTs x hx h
        have hZ2 : ∀ A, lvDst 2 ≤ A → A < chDst 2 → (A - WIT) % 8 = 0 →
            layMem (topMem (stMem M)) 1 idx A = 0 := fun A h1 h2 h3 => by
          rw [layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
          exact pre_low M A (by omega) (by omega) h3
        by_cases hz2 : o < 17872
        · have hzl : zoneLay o = 2 := by unfold zoneLay; rw [if_neg hz1, if_pos hz2]
          rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega))]
          exact layMem_zone (layMem (topMem (stMem M)) 1 idx) M 2 (by omega) idx hP2 hZ2 o (by omega)
            (by omega) h8
        · have hzl : zoneLay o = 3 := by unfold zoneLay; rw [if_neg hz1, if_neg hz2]
          have hP3 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (layMem (topMem (stMem M))
              1 idx) 2 idx (SNAP2 + x) = M (WIT + x) := fun x hx h => by
            rw [layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hP2 x hx h
          have hZ3 : ∀ A, lvDst 3 ≤ A → A < chDst 3 → (A - WIT) % 8 = 0 →
              layMem (layMem (topMem (stMem M)) 1 idx) 2 idx A = 0 := fun A h1 h2 h3 => by
            rw [layMem_out _ 2 (by omega) idx A (Or.inr (by omega)), layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
            exact pre_low M A (by omega) (by omega) h3
          rw [hzl]
          exact layMem_zone (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) M 3 (by omega) idx hP3 hZ3 o
            (by omega) (by omega) h8
theorem run2_zone (M : Nat → Word) (idx o : Nat) (ho : o < 21808) (h8 : o % 8 = 0) :
    run2Mem M idx (WOUT + o) = out2 M idx o := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0x4c0 := rfl
  unfold out2
  by_cases hl : o < 8256
  · rw [if_pos hl]
    unfold run2Mem tailMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), lays_low _ idx _ (by omega)]
    unfold topMem
    rw [if_neg (by omega)]
  · rw [if_neg hl, show WOUT + o = WIT + (o - 832) by omega]
    exact run2_zone_old M idx (o - 832) (by omega) (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand.Compact2
end


namespace ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
/-- Endpoints in a lower-layer leaf input skip its two-word tweak. -/
def lowerIndex (off : Nat) : Nat := off / 16 - (if 16  ≤  off then 1 else 0)
def lowerWord (M : Nat → Word) (src dst A : Nat) : Word :=
  M (src - 64 * lowerIndex (A - dst) + (A - dst) % 16)
/-- Physical memory after the appended four-buffer expansion routine. C2 + C3 (FULL): the top encoding row tweak's
high word (witness offset 24, absolute 1240) is written as LE64(1). -/
def bufferMem (M : Nat → Word) (A : Nat) : Word :=
  if A = 1240 then 1#64
  else if 26112  ≤  A ∧ A < 26144 ∧ A % 8 = 0 then M (A - 3120)
  else if 22992  ≤  A ∧ A < 26112 ∧ A % 8 = 0 then
    if 25232  ≤  A ∧ A < 26096 then M (13680 - 64 * ((A - 25232) / 16) + (A - 25232) % 16)
    else if 24464  ≤  A ∧ A < 25168 ∧ (A < 24480 ∨ 24496  ≤  A) then lowerWord M 16832 24464 A
    else if 23728  ≤  A ∧ A < 24432 ∧ (A < 23744 ∨ 23760  ≤  A) then lowerWord M 19904 23728 A
    else if 22992  ≤  A ∧ A < 23696 ∧ (A < 23008 ∨ 23024  ≤  A) then lowerWord M 22976 22992 A
    else 0
  else M A

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cEntry : List (BitVec 32) := [0x34c0106f]
/-- C3 (FULL, E6): the footer copy starts with `jal` to the trampoline `cETail` (LE64(1) at 1240, `a0`), which
returns to `cInitB`. -/
def cInitJ : List (BitVec 32) := [2287988847]
def cETail : List (BitVec 32) := [1052307,1305492515,25911,2634351891,2000683119]
def cInitB : List (BitVec 32) := [26039,1610974611,340739,6664227,8729347,6665251,17117955,6666275,25506563,6667299,25911,2634351891,26039,1610974611]
def cClear : List (BitVec 32) := [0x53023,0x850513,0xfeb56ce3]
def cHead3 : List (BitVec 32) := [25911,2617574675,26039,2634384787,45090323,340739,8729475,6664227,7713827,4228187411,33916307,4294313491]
def cHead2 : List (BitVec 32) := [21815,3691316499,26039,3406136723,45090323,340739,8729475,6664227,7713827,4228187411,33916307,4294313491]
def cHead1 : List (BitVec 32) := [17719,470091027,26039,4177888659,45090323,340739,8729475,6664227,7713827,4228187411,33916307,4294313491]
def cHead0 : List (BitVec 32) := [13623,1459946771,26039,688227731,56624659]
def cPair : List (BitVec 32) := [0x53303,0x853383,0x65b023,0x75b423,0xfc050513,0x1058593,0xfff60613,0xfe0612e3]
def cFinish : List (BitVec 32) := [0x100293,0x513]
def pairPc (k : Nat) : Nat := [43982,44002,44022,44035].getD k 0
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem code_cEntry : CodeAt im (pcOf 42716) cEntry := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cInitJ : CodeAt im (pcOf 43951) cInitJ := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cETail : CodeAt im (pcOf 43472) cETail := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cInitB : CodeAt im (pcOf 43953) cInitB := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cClear : CodeAt im (pcOf 43967) cClear := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead3 : CodeAt im (pcOf 43970) cHead3 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead2 : CodeAt im (pcOf 43990) cHead2 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead1 : CodeAt im (pcOf 44010) cHead1 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead0 : CodeAt im (pcOf 44030) cHead0 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cFinish : CodeAt im (pcOf 44043) cFinish := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cPair (k : Nat) (hk : k < 4) : CodeAt im (pcOf (pairPc k)) cPair := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
end
sym_block REntry := symRun cfgC cEntry (pcOf 42716) 40
sym_block RInitJ := symRun cfgC cInitJ (pcOf 43951) 40
sym_block RETail := symRun cfgC cETail (pcOf 43472) 40
sym_block RInitB := symRun cfgC cInitB (pcOf 43953) 40
sym_block RClear := symRun cfgC cClear (pcOf 43967) 40
sym_block RHead3 := symRun cfgC cHead3 (pcOf 43970) 40
sym_block RHead2 := symRun cfgC cHead2 (pcOf 43990) 40
sym_block RHead1 := symRun cfgC cHead1 (pcOf 44010) 40
sym_block RHead0 := symRun cfgC cHead0 (pcOf 44030) 40
sym_block RFinish := symRun cfgC cFinish (pcOf 44043) 40
sym_block RPair0 := symRun cfgC cPair (pcOf 43982) 40
sym_block RPair1 := symRun cfgC cPair (pcOf 44002) 40
sym_block RPair2 := symRun cfgC cPair (pcOf 44022) 40
sym_block RPair3 := symRun cfgC cPair (pcOf 44035) 40
def pairRes (k : Nat) : Result := [RPair0.res,RPair1.res,RPair2.res,RPair3.res].getD k RPair0.res
theorem pairRun (k : Nat) (hk : k < 4) : symRun cfgC cPair (pcOf (pairPc k)) 40 = some (pairRes k) := by
  interval_cases k <;> kernel_rfl

def pairResult (p : Nat) : Result :=
  { RPair0.res with pc := (.ite .ne (.bin .add (.reg .x12) (.c 18446744073709551615#64)) (.c 0) (.c (pcOf p)) (.c (pcOf (p+8)))) }
theorem run_pair (k : Nat) (hk : k < 4) : symRun cfgC cPair (pcOf (pairPc k)) 40 =
    some (pairResult (pairPc k)) := by
  interval_cases k <;> kernel_rfl

theorem ofNat_sub64 (src : Nat) (hs : 64  ≤  src) :
    BitVec.ofNat 64 src + 18446744073709551552#64 = BitVec.ofNat 64 (src-64) := by
  rw [show (18446744073709551552#64 : BitVec 64) = BitVec.ofNat 64 (2^64-64) from rfl,
    ofNat_add_ofNat, show src + (2^64-64) = (src-64)+2^64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]

section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem pair_iter (k : Nat) (hk : k < 4) (s : MachineState) (hpc : s.pc = pcOf (pairPc k))
    (src dst n : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (n+1))
    (hn : n+1 < 2^32) (hsl : 64  ≤  src) (hs : src % 8 = 0) (hs' : src+16  ≤  MEMORY_BYTES)
    (hd : dst % 8 = 0) (hd' : dst+16  ≤  MEMORY_BYTES) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = (if n=0 then pcOf (pairPc k+8) else pcOf (pairPc k)) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src-64) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst+16) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst+8 then s.getMem (BitVec.ofNat 64 (src+8))
        else if A = dst then s.getMem (BitVec.ofNat 64 src) else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound (run_pair k hk) (code_cPair hc k hk) s hpc (by
    simp [pairResult, RPair0.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat,
      ofNat_add_ofNat]
    omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairResult, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [Compact.ofNat_sub_one n]
    by_cases h0 : n=0
    · subst n; simp
    · have hne : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [hne,h0]
  · simpa [pairResult, RPair0.res, rv_simp, h10] using ofNat_sub64 src hsl
  · simp [pairResult, RPair0.res, rv_simp, h11, ofNat_add_ofNat]
  · simpa [pairResult, RPair0.res, rv_simp, h12] using Compact.ofNat_sub_one n
  · intro A hA
    have key0 := ofNat_inj hA (show dst < 2^64 by omega)
    have key8 := ofNat_inj hA (show dst+8 < 2^64 by omega)
    simp only [Result.toState_getMem, pairResult, RPair0.res, memEval_cons, memEval_nil,
      Addr.eval, E.eval, BinOp.eval, h10,h11,BitVec.add_zero,ofNat_add_ofNat,key0,key8]
end
def clearMem (M : Nat → Word) (dst i A : Nat) : Word :=
  if dst  ≤  A ∧ A < dst+8*i ∧ (A-dst)%8=0 then 0 else M A
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem clear_iter (s : MachineState) (hpc : s.pc = pcOf 43967) (dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 dst)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (dst+8*(n+1)))
    (hd : dst%8=0) (hbound : dst+8*(n+1)  ≤  MEMORY_BYTES) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if n=0 then pcOf 43970 else pcOf 43967) ∧
      t.getReg .x10 = BitVec.ofNat 64 (dst+8) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst+8*(n+1)) ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A) = if A=dst then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RClear (code_cClear hc) s hpc (by
    simp [RClear.res, rv_simp, accessValid_iff, h10, BitVec.toNat_ofNat]
    omega), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RClear.res, E.eval, CmpOp.eval, BinOp.eval,h10,h11,ofNat_add_ofNat]
    have he : BitVec.ult (BitVec.ofNat 64 (dst+8)) (BitVec.ofNat 64 (dst+8*(n+1))) = decide (n≠0) := by
      simp only [BitVec.ult,BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dst+8 < 2^64 by omega),
        Nat.mod_eq_of_lt (show dst+8*(n+1) < 2^64 by omega)]
      simp only [decide_eq_decide]
      omega
    rw [he]
    by_cases hn : n=0 <;> simp [hn]
  · simp [RClear.res,rv_simp,h10,ofNat_add_ofNat]
  · simp [RClear.res,rv_simp,h11]
  · intro A hA
    have key := ofNat_inj hA (show dst < 2^64 by omega)
    simp only [Result.toState_getMem, RClear.res, memEval_cons,memEval_nil,Addr.eval,E.eval,h10,
      BitVec.add_zero,key]
    rfl
theorem clear_loop (s : MachineState) (hpc : s.pc = pcOf 43967) (dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 dst) (h11 : s.getReg .x11 = BitVec.ofNat 64 (dst+8*n))
    (hn : 0<n) (hd : dst%8=0) (hbound : dst+8*n  ≤  MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3*i) (3*i) t ∧
      t.pc = (if i<n then pcOf 43967 else pcOf 43970) ∧
      t.getReg .x10 = BitVec.ofNat 64 (dst+8*i) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst+8*n) ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A) = clearMem (fun B => s.getMem (BitVec.ofNat 64 B)) dst i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s,Steps.refl s,by simpa [hn] using hpc,by simpa using h10,h11,?_⟩
    intro A _; unfold clearMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t,st,pt,t10,t11,mt⟩ := ih (by omega)
    obtain ⟨u,su,pu,u10,u11,mu⟩ := clear_iter hc t (by rw [pt,if_pos (by omega)])
      (dst+8*i) (n-i-1) t10 (by rw [t11]; congr 1 <;> omega) (by omega) (by omega)
    refine ⟨u,(st.trans su).of_eq (by omega) (by omega),?_,?_,?_,?_⟩
    · rw [pu]; by_cases hz : n-i-1=0
      · rw [if_pos hz,if_neg (by omega)]
      · rw [if_neg hz,if_pos (by omega)]
    · rw [u10]; congr 1 <;> omega
    · rw [u11]; congr 1 <;> omega
    · intro A hA
      rw [mu A hA,mt A hA]
      unfold clearMem
      by_cases ha : A=dst+8*i
      · subst A; rw [if_pos rfl,if_pos (by omega)]
      · rw [if_neg ha]
        by_cases hin : dst ≤ A ∧ A<dst+8*i ∧ (A-dst)%8=0
        · rw [if_pos hin,if_pos (by omega)]
        · rw [if_neg hin,if_neg (by omega)]
end

def pairsMem (M : Nat → Word) (src dst i A : Nat) : Word :=
  if dst  ≤  A ∧ A < dst+16*i ∧ (A-dst)%8=0 then
    M (src-64*((A-dst)/16)+(A-dst)%16) else M A
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem pair_loop (k : Nat) (hk : k<4) (s : MachineState) (hpc : s.pc = pcOf (pairPc k))
    (src dst n : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (hn : 0<n) (hn' : n<2^32) (hsl : 64*n ≤ src) (hov : src+16 ≤ dst)
    (hs : src%8=0) (hs' : src+16 ≤ MEMORY_BYTES) (hd : dst%8=0) (hd' : dst+16*n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (8*i) (8*i) t ∧
      t.pc = (if i<n then pcOf (pairPc k) else pcOf (pairPc k+8)) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src-64*i) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst+16*i) ∧ t.getReg .x12 = BitVec.ofNat 64 (n-i) ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A) =
        pairsMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst i A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s,Steps.refl s,by simpa [hn] using hpc,by simpa using h10,
      by simpa using h11,by simpa using h12,?_⟩
    intro A _; unfold pairsMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t,st,pt,t10,t11,t12,mt⟩ := ih (by omega)
    obtain ⟨u,su,pu,u10,u11,u12,mu⟩ := pair_iter hc k hk t
      (by rw [pt,if_pos (by omega)]) (src-64*i) (dst+16*i) (n-i-1)
      t10 t11 (by rw [t12]; congr 1 <;> omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    refine ⟨u,(st.trans su).of_eq (by omega) (by omega),?_,?_,?_,?_,?_⟩
    · rw [pu]; by_cases hz : n-i-1=0
      · rw [if_pos hz,if_neg (by omega)]
      · rw [if_neg hz,if_pos (by omega)]
    · rw [u10]; congr 1 <;> omega
    · rw [u11]; congr 1 <;> omega
    · rw [u12]; congr 1 <;> omega
    · intro A hA
      have hsrc0 : t.getMem (BitVec.ofNat 64 (src-64*i)) = s.getMem (BitVec.ofNat 64 (src-64*i)) := by
        rw [mt _ (by omega)]; unfold pairsMem; rw [if_neg (by omega)]
      have hsrc8 : t.getMem (BitVec.ofNat 64 (src-64*i+8)) = s.getMem (BitVec.ofNat 64 (src-64*i+8)) := by
        rw [mt _ (by omega)]; unfold pairsMem; rw [if_neg (by omega)]
      rw [mu A hA,hsrc0,hsrc8,mt A hA]
      unfold pairsMem
      by_cases ha8 : A=dst+16*i+8
      · subst A
        rw [if_pos rfl,if_pos (by omega)]
        congr 2 <;> omega
      · rw [if_neg ha8]
        by_cases ha0 : A=dst+16*i
        · subst A
          rw [if_pos rfl,if_pos (by omega)]
          congr 2 <;> omega
        · rw [if_neg ha0]
          by_cases hin : dst ≤ A ∧ A<dst+16*i ∧ (A-dst)%8=0
          · rw [if_pos hin,if_pos (by omega)]
          · rw [if_neg hin,if_neg (by omega)]
end


def putPair (M : Nat → Word) (src dst A : Nat) : Word :=
  if A=dst+8 then M (src+8) else if A=dst then M src else M A
def footerMem (M : Nat → Word) (A : Nat) : Word :=
  if A=1240 then 1#64 else
  if A=26136 then M 23016 else if A=26128 then M 23008
  else if A=26120 then M 23000 else if A=26112 then M 22992 else M A
def expandedMem (M : Nat → Word) : Nat → Word :=
  let z := clearMem (footerMem M) 22992 390
  let b3 := pairsMem (putPair z 22976 22992) 22912 23024 42
  let b2 := pairsMem (putPair b3 19904 23728) 19840 23760 42
  let b1 := pairsMem (putPair b2 16832 24464) 16768 24496 42
  pairsMem b1 13680 25232 54
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem entry_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 43951 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_,symRun_sound REntry (code_cEntry hc) s hpc (by simp [REntry.res,rv_simp]),?_,?_⟩
  · simp [REntry.res,rv_simp]
  · intro A hA; rfl
theorem init_spec (s : MachineState) (hpc : s.pc=pcOf 43951) :
    ∃ t, Steps im s 20 20 t ∧ t.pc=pcOf 43967 ∧
      t.getReg .x10=BitVec.ofNat 64 22992 ∧ t.getReg .x11=BitVec.ofNat 64 26112 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=footerMem (fun B=>s.getMem (BitVec.ofNat 64 B)) A := by
  have sJ := symRun_sound RInitJ (code_cInitJ hc) s hpc (by simp [RInitJ.res,rv_simp])
  generalize hu : Result.toState _ s = u at sJ
  have pu : u.pc = pcOf 43472 := by rw [← hu]; simp [RInitJ.res,rv_simp]
  have mu : ∀ a, u.getMem a = s.getMem a := by intro a; rw [← hu]; rfl
  have sT := symRun_sound RETail (code_cETail hc) u pu (by simp [RETail.res,rv_simp,accessValid_iff])
  generalize hv : Result.toState _ u = v at sT
  have pv : v.pc = pcOf 43953 := by rw [← hv]; simp [RETail.res,rv_simp]
  have vx10 : v.getReg .x10 = 22992#64 := by rw [← hv]; simp [RETail.res,rv_simp]
  have mv : ∀ A < 2^64, v.getMem (BitVec.ofNat 64 A) =
      if A = 1240 then 1#64 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← hv]
    simp only [RETail.res,rv_simp,Result.toState_getMem,memEval_cons,memEval_nil,Addr.eval,E.eval,mu]
    have k := ofNat_inj hA (show 1240<2^64 by decide)
    by_cases q : A = 1240
    · subst q; simp
    · rw [if_neg (fun h => q (k.mp h)), if_neg q]
  have sB := symRun_sound RInitB (code_cInitB hc) v pv (by simp [RInitB.res,rv_simp,accessValid_iff,vx10,MEMORY_BYTES])
  generalize hw : Result.toState _ v = w at sB
  refine ⟨w, (sJ.trans (sT.trans sB)).of_eq (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [← hw]; simp [RInitB.res,rv_simp]
  · rw [← hw]; simp [RInitB.res,rv_simp]
  · rw [← hw]; simp [RInitB.res,rv_simp]
  · intro A hA
    rw [← hw]
    simp only [RInitB.res,rv_simp,Result.toState_getMem,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,
      vx10,footerMem]
    rw [show (22992#64 : Word) + 24#64 = BitVec.ofNat 64 23016 from rfl,
      show (22992#64 : Word) + 16#64 = BitVec.ofNat 64 23008 from rfl,
      show (22992#64 : Word) + 8#64 = BitVec.ofNat 64 23000 from rfl,
      show (22992#64 : Word) = BitVec.ofNat 64 22992 from rfl,
      mv 23016 (by decide), mv 23008 (by decide), mv 23000 (by decide), mv 22992 (by decide), mv A hA]
    have k0 := ofNat_inj hA (show 26112<2^64 by decide)
    have k1 := ofNat_inj hA (show 26120<2^64 by decide)
    have k2 := ofNat_inj hA (show 26128<2^64 by decide)
    have k3 := ofNat_inj hA (show 26136<2^64 by decide)
    simp only [k0,k1,k2,k3, show ¬ (23016 = 1240) by decide, show ¬ (23008 = 1240) by decide,
      show ¬ (23000 = 1240) by decide, show ¬ (22992 = 1240) by decide, if_false]
    by_cases q : A = 1240
    · subst q; simp
    · simp only [q, if_false]

theorem head3_spec (s : MachineState) (hpc : s.pc=pcOf 43970) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 43982 ∧
      t.getReg .x10=BitVec.ofNat 64 22912 ∧ t.getReg .x11=BitVec.ofNat 64 23024 ∧
      t.getReg .x12=BitVec.ofNat 64 42 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=putPair (fun B=>s.getMem (BitVec.ofNat 64 B)) 22976 22992 A := by
  refine ⟨_,symRun_sound RHead3 (code_cHead3 hc) s hpc (by simp [RHead3.res,rv_simp,accessValid_iff]),?_,?_,?_,?_,?_⟩
  · simp [RHead3.res,rv_simp]
  · simp [RHead3.res,rv_simp]
  · simp [RHead3.res,rv_simp]
  · simp [RHead3.res,rv_simp]
  · intro A hA
    have k0 := ofNat_inj hA (show 22992<2^64 by decide)
    have k1 := ofNat_inj hA (show 23000<2^64 by decide)
    simp only [RHead3.res,rv_simp,Result.toState_getMem,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,putPair]
    simpa only [k0,k1]

theorem head2_spec (s : MachineState) (hpc : s.pc=pcOf 43990) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 44002 ∧
      t.getReg .x10=BitVec.ofNat 64 19840 ∧ t.getReg .x11=BitVec.ofNat 64 23760 ∧
      t.getReg .x12=BitVec.ofNat 64 42 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=putPair (fun B=>s.getMem (BitVec.ofNat 64 B)) 19904 23728 A := by
  refine ⟨_,symRun_sound RHead2 (code_cHead2 hc) s hpc (by simp [RHead2.res,rv_simp,accessValid_iff]),?_,?_,?_,?_,?_⟩
  · simp [RHead2.res,rv_simp]
  · simp [RHead2.res,rv_simp]
  · simp [RHead2.res,rv_simp]
  · simp [RHead2.res,rv_simp]
  · intro A hA
    have k0 := ofNat_inj hA (show 23728<2^64 by decide)
    have k1 := ofNat_inj hA (show 23736<2^64 by decide)
    simp only [RHead2.res,rv_simp,Result.toState_getMem,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,putPair]
    simpa only [k0,k1]

theorem head1_spec (s : MachineState) (hpc : s.pc=pcOf 44010) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 44022 ∧
      t.getReg .x10=BitVec.ofNat 64 16768 ∧ t.getReg .x11=BitVec.ofNat 64 24496 ∧
      t.getReg .x12=BitVec.ofNat 64 42 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=putPair (fun B=>s.getMem (BitVec.ofNat 64 B)) 16832 24464 A := by
  refine ⟨_,symRun_sound RHead1 (code_cHead1 hc) s hpc (by simp [RHead1.res,rv_simp,accessValid_iff]),?_,?_,?_,?_,?_⟩
  · simp [RHead1.res,rv_simp]
  · simp [RHead1.res,rv_simp]
  · simp [RHead1.res,rv_simp]
  · simp [RHead1.res,rv_simp]
  · intro A hA
    have k0 := ofNat_inj hA (show 24464<2^64 by decide)
    have k1 := ofNat_inj hA (show 24472<2^64 by decide)
    simp only [RHead1.res,rv_simp,Result.toState_getMem,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,putPair]
    simpa only [k0,k1]

theorem head0_spec (s : MachineState) (hpc : s.pc=pcOf 44030) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=pcOf 44035 ∧
      t.getReg .x10=BitVec.ofNat 64 13680 ∧ t.getReg .x11=BitVec.ofNat 64 25232 ∧
      t.getReg .x12=BitVec.ofNat 64 54 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_,symRun_sound RHead0 (code_cHead0 hc) s hpc (by simp [RHead0.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [RHead0.res,rv_simp]
  · simp [RHead0.res,rv_simp]
  · simp [RHead0.res,rv_simp]
  · simp [RHead0.res,rv_simp]
  · intro A hA; rfl
theorem finish_spec (s : MachineState) (hpc : s.pc=pcOf 44043) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 44045 ∧
      t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      ∀ A < 2^64, t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_,symRun_sound RFinish (code_cFinish hc) s hpc (by simp [RFinish.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [RFinish.res,rv_simp]
  · simp [RFinish.res,rv_simp]
  · simp [RFinish.res,rv_simp]
  · intro A hA; rfl
end

def MemEq (M N : Nat → Word) : Prop := ∀ A < 2^64, M A=N A
theorem clearMem_congr {M N : Nat → Word} (h : MemEq M N) (dst i : Nat) :
    MemEq (clearMem M dst i) (clearMem N dst i) := by
  intro A hA; unfold clearMem; split_ifs <;> first | rfl | exact h A hA
theorem pairsMem_congr {M N : Nat → Word} (h : MemEq M N) (src dst i : Nat) (hs : src+16<2^64) :
    MemEq (pairsMem M src dst i) (pairsMem N src dst i) := by
  intro A hA; unfold pairsMem; split_ifs
  · apply h; have := Nat.mod_lt (A-dst) (show 0<16 by decide); omega
  · exact h A hA
theorem putPair_congr {M N : Nat → Word} (h : MemEq M N) (src dst : Nat) (hs : src+16<2^64) :
    MemEq (putPair M src dst) (putPair N src dst) := by
  intro A hA; unfold putPair; split_ifs
  · exact h _ (by omega)
  · exact h _ (by omega)
  · exact h A hA
theorem footerMem_congr {M N : Nat → Word} (h : MemEq M N) : MemEq (footerMem M) (footerMem N) := by
  intro A hA; unfold footerMem; split_ifs <;> first | rfl | (apply h; omega)
section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem buffer_expanded_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2674 2674 t ∧ t.pc=pcOf 44045 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (expandedMem (fun A=>s.getMem (BitVec.ofNat 64 A))) := by
  obtain ⟨s1,h1,p1,m1⟩ := entry_spec hc s hpc
  obtain ⟨s2,h2,p2,r210,r211,m2⟩ := init_spec hc s1 p1
  have mm2 : MemEq (fun A=>s2.getMem (BitVec.ofNat 64 A)) (footerMem (fun A=>s.getMem (BitVec.ofNat 64 A))) :=
    fun A hA => (m2 A hA).trans (footerMem_congr m1 A hA)
  obtain ⟨s3,h3,p3,r310,r311,m3⟩ := clear_loop hc s2 p2 22992 390 r210 r211
    (by decide) (by decide) (by decide) 390 le_rfl
  have mm3 := fun A hA => (m3 A hA).trans (clearMem_congr mm2 22992 390 A hA)
  obtain ⟨s4,h4,p4,r410,r411,r412,m4⟩ := head3_spec hc s3 (by simpa using p3)
  have mm4 := fun A hA => (m4 A hA).trans (putPair_congr mm3 22976 22992 (by decide) A hA)
  obtain ⟨s5,h5,p5,r510,r511,r512,m5⟩ := pair_loop hc 0 (by decide) s4 p4 22912 23024 42
    r410 r411 r412 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 42 le_rfl
  have mm5 := fun A hA => (m5 A hA).trans (pairsMem_congr mm4 22912 23024 42 (by decide) A hA)
  obtain ⟨s6,h6,p6,r610,r611,r612,m6⟩ := head2_spec hc s5 (by simpa [pairPc] using p5)
  have mm6 := fun A hA => (m6 A hA).trans (putPair_congr mm5 19904 23728 (by decide) A hA)
  obtain ⟨s7,h7,p7,r710,r711,r712,m7⟩ := pair_loop hc 1 (by decide) s6 p6 19840 23760 42
    r610 r611 r612 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 42 le_rfl
  have mm7 := fun A hA => (m7 A hA).trans (pairsMem_congr mm6 19840 23760 42 (by decide) A hA)
  obtain ⟨s8,h8,p8,r810,r811,r812,m8⟩ := head1_spec hc s7 (by simpa [pairPc] using p7)
  have mm8 := fun A hA => (m8 A hA).trans (putPair_congr mm7 16832 24464 (by decide) A hA)
  obtain ⟨s9,h9,p9,r910,r911,r912,m9⟩ := pair_loop hc 2 (by decide) s8 p8 16768 24496 42
    r810 r811 r812 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 42 le_rfl
  have mm9 := fun A hA => (m9 A hA).trans (pairsMem_congr mm8 16768 24496 42 (by decide) A hA)
  obtain ⟨s10,h10,p10,r1010,r1011,r1012,m10⟩ := head0_spec hc s9 (by simpa [pairPc] using p9)
  have mm10 := fun A hA => (m10 A hA).trans (mm9 A hA)
  obtain ⟨s11,h11,p11,r1110,r1111,r1112,m11⟩ := pair_loop hc 3 (by decide) s10 p10 13680 25232 54
    r1010 r1011 r1012 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 54 le_rfl
  have mm11 := fun A hA => (m11 A hA).trans (pairsMem_congr mm10 13680 25232 54 (by decide) A hA)
  obtain ⟨s12,h12,p12,r125,r1210,m12⟩ := finish_spec hc s11 (by simpa [pairPc] using p11)
  refine ⟨s12,?_,p12,r125,r1210,?_⟩
  · exact (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans
      (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans h12))))))))))).of_eq (by decide) (by decide)
  · intro A hA
    exact (m12 A hA).trans (mm11 A hA)
end

theorem bufferMem_outside (M : Nat → Word) (A : Nat) (h1 : A ≠ 1240)
    (h : A < 22992 ∨ 26144 ≤ A ∨ A % 8 ≠ 0) : bufferMem M A = M A := by
  unfold bufferMem
  rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

theorem expandedMem_outside (M : Nat → Word) (A : Nat) (h1 : A ≠ 1240)
    (h : A < 22992 ∨ 26144 ≤ A ∨ A % 8 ≠ 0) : expandedMem M A = M A := by
  unfold expandedMem
  rw [pairsMem, if_neg (by omega)]
  rw [pairsMem, if_neg (by omega)]
  rw [putPair, if_neg (by omega), if_neg (by omega)]
  rw [pairsMem, if_neg (by omega)]
  rw [putPair, if_neg (by omega), if_neg (by omega)]
  rw [pairsMem, if_neg (by omega)]
  rw [putPair, if_neg (by omega), if_neg (by omega)]
  rw [clearMem, if_neg (by omega)]
  rw [footerMem, if_neg h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]


theorem expandedMem_eq_bufferMem_aligned (M : Nat → Word) (q : Nat) (hq : q < 394) :
    expandedMem M (22992 + 8*q) = bufferMem M (22992 + 8*q) := by
  interval_cases q <;> rfl

theorem expandedMem_eq_bufferMem (M : Nat → Word) (A : Nat) :
    expandedMem M A = bufferMem M A := by
  by_cases h1 : A = 1240
  · subst h1; rfl
  by_cases hout : A < 22992 ∨ 26144 ≤ A ∨ A % 8 ≠ 0
  · rw [expandedMem_outside M A h1 hout, bufferMem_outside M A h1 hout]
  · have hq : (A - 22992) / 8 < 394 := by omega
    have he : A = 22992 + 8 * ((A - 22992) / 8) := by omega
    have h := expandedMem_eq_bufferMem_aligned M ((A - 22992) / 8) hq
    rwa [← he] at h

theorem buffer_spec {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2674 2674 t ∧ t.pc=pcOf 44045 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (bufferMem (fun A=>s.getMem (BitVec.ofNat 64 A))) := by
  obtain ⟨t,st,pt,t5,t10,mt⟩ := buffer_expanded_spec hc s hpc
  refine ⟨t,st,pt,t5,t10,?_⟩
  intro A hA
  exact (mt A hA).trans (expandedMem_eq_bufferMem _ A)

end ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
