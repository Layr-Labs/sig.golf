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
def copyRegs (src dst n ret : Nat) : RegFile :=
  (((RegFile.init.set .x1 (.c (pcOf ret))).set .x10 (.c (BitVec.ofNat 64 src))).set .x11
    (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def zeroRegs (dst n ret : Nat) : RegFile :=
  ((RegFile.init.set .x1 (.c (pcOf ret))).set .x11 (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def copyTab : List (Nat × Nat × Nat × Nat) :=
  [(42142, WIT, SNAP2, 2729), (42154, SNAP2, WIT, 8)] ++
  (List.range 9).map (fun q => (42161 + 7 * q, SNAP2 + 64 + 896 * (8 - q), WIT + 64 + 880 * q, 112)) ++
  [(42224, SNAP2 + 8136, WIT + 8000, 528), (42235, SNAP2 + 8136 + 64 * 66 + 64 * 7, WIT + 12224 + 16 * 23, 344),
   (42408, SNAP2 + 8136 + 64 * 116 + 64 * 6, WIT + 15344 + 16 * 19, 344),
   (42557, SNAP2 + 8136 + 64 * 165 + 64 * 6, WIT + 18400 + 16 * 19, 344)]
theorem run_snap : symRun cfgC cSnap (pcOf 42142) 40 =
    some ⟨⟨copyRegs WIT SNAP2 2729 42149, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
theorem run_zero2 : symRun cfgC cZero2 (pcOf 42149) 40 =
    some ⟨⟨zeroRegs WIT 2686 42154, [], []⟩, .c (pcOf 42137), .jump, 5, 5⟩ := by kernel_rfl
theorem run_hdr : symRun cfgC cHdr (pcOf 42154) 40 =
    some ⟨⟨copyRegs SNAP2 WIT 8 42161, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
theorem run_reg (k : Nat) (hk : k < 9) : symRun cfgC (cReg k) (pcOf (regAt k)) 40 =
    some ⟨⟨copyRegs (SNAP2 + 64 + 896 * k) (WIT + 64 + 880 * (8 - k)) 112 (regAt k + 7), [], []⟩,
      .c (pcOf 42130), .jump, 7, 7⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_top : symRun cfgC cTop (pcOf 42224) 40 =
    some ⟨⟨copyRegs (SNAP2 + 8136) (WIT + 8000) 528 42231, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
def chAt (lay : Nat) : Nat := if lay = 1 then 42235 else if lay = 2 then 42408 else 42557
def cCh (lay : Nat) : List (BitVec 32) := if lay = 1 then cCh1 else if lay = 2 then cCh2 else cCh3
def chSrc (lay : Nat) : Nat := SNAP2 + 8136 + 64 * (if lay = 1 then 66 + 7 else if lay = 2 then 116 + 6 else 165 + 6)
def chDst (lay : Nat) : Nat := lvDst lay + 16 * (if lay = 1 then 23 else 19)
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
theorem zeroSet_spec {im : Image} (hcode : CodeAt im (pcOf 42149) cZero2) (s : MachineState)
    (hpc : s.pc = pcOf 42149) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 42137 ∧ t.getReg .x11 = BitVec.ofNat 64 WIT ∧
      t.getReg .x12 = BitVec.ofNat 64 2686 ∧ t.getReg .x1 = pcOf 42154 ∧
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
def pathTop (lay : Nat) : Nat := 16 * (if lay = 1 then 23 else 19)
theorem sibS_padS_lt (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    sibS lay r j + 16 ≤ pathTop lay ∧ padS lay r j + 16 ≤ pathTop lay := by
  have h := (plan_ok lay r j hl hr hj).2
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold sibS padS pathTop; split_ifs at h ⊢ <;> constructor <;> omega
theorem pathTop_le (lay : Nat) : pathTop lay ≤ 16 * 23 := by unfold pathTop; split_ifs <;> omega
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
    ∀ L ≤ lvH lay, ∃ t, Steps im u (23 * L) (23 * L) t ∧ t.pc = pcOf (lvAt lay L) ∧
      RegsExcept u t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = lvsMem M0 lay r L A := by
  have hD : 0x800 + 12224 ≤ lvDst lay ∧ lvDst lay + 16 * 23 ≤ 0x800 + 21456 := by
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
def regsMem (M : Nat → Word) (Q : Nat) (A : Nat) : Word :=
  if 0 < Q ∧ WIT + 64 ≤ A ∧ A < WIT + 64 + 880 * (Q - 1) + 896 ∧ (A - WIT) % 8 = 0 then
    M (SNAP2 + 64 + 896 * (8 - min ((A - WIT - 64) / 880) (Q - 1)) +
      (A - WIT - 64 - 880 * min ((A - WIT - 64) / 880) (Q - 1)))
  else M A
theorem regsMem_succ (M : Nat → Word) (Q : Nat) (hQ : Q < 9) (A : Nat) :
    (if WIT + 64 + 880 * Q ≤ A ∧ A < WIT + 64 + 880 * Q + 8 * 112 ∧ (A - (WIT + 64 + 880 * Q)) % 8 = 0 then
      M (SNAP2 + 64 + 896 * (8 - Q) + (A - (WIT + 64 + 880 * Q))) else regsMem M Q A) = regsMem M (Q + 1) A := by
  unfold regsMem
  have hW : WIT = 0x800 := rfl
  by_cases h1 : WIT + 64 + 880 * Q ≤ A ∧ A < WIT + 64 + 880 * Q + 8 * 112 ∧ (A - (WIT + 64 + 880 * Q)) % 8 = 0
  · rw [if_pos h1, if_pos (show 0 < Q + 1 ∧ WIT + 64 ≤ A ∧ A < WIT + 64 + 880 * (Q + 1 - 1) + 896 ∧
        (A - WIT) % 8 = 0 by omega)]
    have hq : min ((A - WIT - 64) / 880) (Q + 1 - 1) = Q := by
      rw [show Q + 1 - 1 = Q by omega]; apply Nat.min_eq_right; omega
    rw [hq, show A - WIT - 64 - 880 * Q = A - (WIT + 64 + 880 * Q) by omega]
  · rw [if_neg h1]
    by_cases h2 : 0 < Q ∧ WIT + 64 ≤ A ∧ A < WIT + 64 + 880 * (Q - 1) + 896 ∧ (A - WIT) % 8 = 0
    · rw [if_pos h2, if_pos (show 0 < Q + 1 ∧ WIT + 64 ≤ A ∧ A < WIT + 64 + 880 * (Q + 1 - 1) + 896 ∧
          (A - WIT) % 8 = 0 by omega)]
      have hlt : A < WIT + 64 + 880 * Q := by omega
      have e1 : min ((A - WIT - 64) / 880) (Q - 1) = (A - WIT - 64) / 880 := Nat.min_eq_left (by omega)
      have e2 : min ((A - WIT - 64) / 880) (Q + 1 - 1) = (A - WIT - 64) / 880 := Nat.min_eq_left (by omega)
      rw [e1, e2]
    · rw [if_neg h2, if_neg (by omega)]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem regs_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf 42161) :
    ∀ Q ≤ 9, ∃ t, Steps im u (680 * Q) (680 * Q) t ∧ t.pc = pcOf (42161 + 7 * Q) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = regsMem M0 Q A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  intro Q hQ
  induction Q with
  | zero => exact ⟨u, Steps.refl u, by simpa using hpc, RegsExcept.refl u _, fun A hA => by
      rw [hM A hA]; unfold regsMem; rw [if_neg (by omega)]⟩
  | succ Q ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hk : 8 - Q < 9 := by omega
    have hpt : t.pc = pcOf (regAt (8 - Q)) := by rw [pt]; unfold regAt; congr 1; omega
    have hrun := run_reg (8 - Q) hk
    rw [show regAt (8 - Q) + 7 = 42161 + 7 * (Q + 1) by unfold regAt; omega,
      show 8 - (8 - Q) = Q by omega] at hrun
    obtain ⟨t', st', pt', rt', mt'⟩ := copyPhase hc (code_cReg hc (8 - Q) hk) (by
      rw [show regAt (8 - Q) + 7 = 42161 + 7 * (Q + 1) by unfold regAt; omega]; exact hrun) t hpt
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold regAt; congr 1; omega,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, ← regsMem_succ M0 Q (by omega) A]
    by_cases h1 : WIT + 64 + 880 * Q ≤ A ∧ A < WIT + 64 + 880 * Q + 8 * 112 ∧ (A - (WIT + 64 + 880 * Q)) % 8 = 0
    · rw [if_pos h1, if_pos h1, mt _ (by omega)]
      unfold regsMem
      rw [if_neg (by omega)]
    · rw [if_neg h1, if_neg h1, mt A hA]
end
def chMem (M : Nat → Word) (lay : Nat) (A : Nat) : Word :=
  if chDst lay ≤ A ∧ A < chDst lay + 8 * 344 ∧ (A - chDst lay) % 8 = 0 then M (chSrc lay + (A - chDst lay)) else M A
def layMem (M : Nat → Word) (lay idx : Nat) (A : Nat) : Word :=
  lvsMem (chMem M lay) lay (lroute lay idx) (lvH lay) A
def layLen (lay : Nat) : Nat := 2072 + rowLen lay + 23 * lvH lay
theorem chDst_eq (lay : Nat) : chDst lay = lvDst lay + pathTop lay := by unfold chDst pathTop; rfl
theorem layMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx A : Nat)
    (hA : A < lvDst lay ∨ chDst lay + 8 * 344 ≤ A) : layMem M lay idx A = M A := by
  have hA' := hA
  have hce := chDst_eq lay
  rw [chDst_eq] at hA'
  unfold layMem
  rw [lvsMem_out _ lay hl _ (lroute_lt lay idx) _ le_rfl _ (by omega)]
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
  have hdst : chDst lay % 8 = 0 ∧ chDst lay + 8 * 344 ≤ 0x800 + 21456 ∧
      lvDst lay % 16 = 0 ∧ 0x800 + 12224 ≤ lvDst lay := by
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
    (by rw [p2]; interval_cases lay <;> rfl) (lroute lay idx) (lroute_lt lay idx) x19 x20 hp2 (lvH lay) le_rfl
  refine ⟨u3, ((s1.trans s2).trans s3).of_eq (by unfold layLen; ring) (by unfold layLen; ring), p3,
    ((r1.trans r2).trans r3).mono (by decide), fun A hA => ?_⟩
  rw [m3 A hA]; rfl
end
def tailMem (M : Nat → Word) (A : Nat) : Word :=
  if A = WIT + 21480 then LoadKind.wu.fromWord (M (SNAP2 + 16)) 0
  else if A = WIT + 21472 then 0
  else if A = WIT + 21464 then M (SNAP2 + 8)
  else if A = WIT + 21456 then M SNAP2
  else M A
set_option maxRecDepth 20000 in
theorem tail_spec {im : Image} (hcode : CodeAt im (pcOf 42705) cTail) (s : MachineState) (hpc : s.pc = pcOf 42705) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 42718 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x5, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = tailMem (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound RTail hcode s hpc (by simp [RTail.res, rv_simp]), ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · simp [Result.toState_pc, RTail.res, E.eval]
  · simp [RTail.res, rv_simp]
  · simp [RTail.res, rv_simp]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · have key : ∀ c : Nat, c < 2 ^ 64 → (BitVec.ofNat 64 A = BitVec.ofNat 64 c ↔ A = c) := fun c hc => ofNat_inj hA hc
    simp only [Result.toState_getMem, RTail.res, memEval_cons, memEval_nil, Addr.eval, E.eval, UnOp.eval,
      key 23528 (by norm_num), key 23520 (by norm_num), key 23512 (by norm_num), key 23504 (by norm_num)]
    unfold tailMem
    simp only [show WIT = 0x800 from rfl, show SNAP2 = 0x300000 from rfl, Nat.reduceAdd]
    rfl
def snapMem (M : Nat → Word) (A : Nat) : Word :=
  if SNAP2 ≤ A ∧ A < SNAP2 + 8 * 2729 ∧ (A - SNAP2) % 8 = 0 then M (WIT + (A - SNAP2)) else M A
def zMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT ≤ A ∧ A < WIT + 8 * 2686 ∧ (A - WIT) % 8 = 0 then 0 else M A
def hdrMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT ≤ A ∧ A < WIT + 8 * 8 ∧ (A - WIT) % 8 = 0 then M (SNAP2 + (A - WIT)) else M A
def topMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT + 8000 ≤ A ∧ A < WIT + 8000 + 8 * 528 ∧ (A - (WIT + 8000)) % 8 = 0 then M (SNAP2 + 8136 + (A - (WIT + 8000)))
  else M A
def run2Mem (M : Nat → Word) (idx : Nat) (A : Nat) : Word :=
  tailMem (layMem (layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx) 2 idx) 3 idx) A
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run2_spec (s : MachineState) (hpc : s.pc = pcOf 42142) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hix : s.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 idx) (hp : LPlanAt s) :
    ∃ t, Steps im s 43166 43166 t ∧ t.pc = pcOf 42718 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = run2Mem (fun B => s.getMem (BitVec.ofNat 64 B)) idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨u1, s1, p1, r1, m1⟩ := copyPhase hc (code_cSnap hc) run_snap s hpc (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have e1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = snapMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => by rw [m1 A hA]; rfl
  obtain ⟨u2a, s2a, p2a, x11, x12, x1, r2a, f2a⟩ := zeroSet_spec (code_cZero2 hc) u1 (by rw [p1])
  obtain ⟨u2, s2, p2, r2, m2⟩ := zero_spec hc u2a p2a WIT 2686 42154 x11 x12 x1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  have e2 : ∀ A < 2 ^ 64, u2.getMem (BitVec.ofNat 64 A) =
      zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [m2 A hA]; unfold zeroed zMem; split
    · rfl
    · rw [f2a A hA (fun h => h), e1 A hA]
  obtain ⟨u3, s3, p3, r3, m3⟩ := copyPhase hc (code_cHdr hc) run_hdr u2 p2 (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) =
      hdrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B)))) A := fun A hA => by
    rw [m3 A hA]; unfold hdrMem; split
    · rw [e2 _ (by omega)]
    · rw [e2 A hA]
  obtain ⟨u4, s4, p4, r4, m4⟩ := regs_spec hc u3 _ e3 p3 9 le_rfl
  obtain ⟨u5, s5, p5, r5, m5⟩ := copyPhase hc (code_cTop hc) run_top u4 (by rw [p4]) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e5 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      topMem (regsMem (hdrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))))) 9) A := fun A hA => by
    rw [m5 A hA]; unfold topMem; split
    · rw [m4 _ (by omega)]
    · rw [m4 A hA]
  obtain ⟨u6, s6, p6, x22, x18, r6, f6⟩ := idx_spec (code_cIdx hc) u5 p5
  have hp6 : LPlanAt u6 := fun k hk => by
    rw [f6 _ (by omega) (fun h => h), e5 _ (by omega)]
    unfold topMem regsMem hdrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hp k hk
  have h60 : u6.getMem (BitVec.ofNat 64 0x60) = s.getMem (BitVec.ofNat 64 0x60) := by
    rw [f6 _ (by omega) (fun h => h), e5 _ (by omega)]
    unfold topMem regsMem hdrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have x22' : u6.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [x22, show (96#64 : Word) = BitVec.ofNat 64 0x60 from rfl, e5 _ (by omega)]
    unfold topMem regsMem hdrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hix
  have e6 : ∀ A < 2 ^ 64, u6.getMem (BitVec.ofNat 64 A) =
      topMem (regsMem (hdrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))))) 9) A := fun A hA => by
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
  obtain ⟨u10, s10, p10, x5, x10, r10, m10⟩ := tail_spec (code_cTail hc) u9 (by rw [p9]; rfl)
  refine ⟨u10, ((((((((((s1.trans s2a).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans
    s9).trans s10).of_eq (by unfold layLen rowLen lvH; norm_num) (by unfold layLen rowLen lvH; norm_num), p10, x5, x10,
    fun A hA => ?_⟩
  rw [m10 A hA]
  unfold run2Mem tailMem
  beta_reduce
  have g : ∀ B < 2 ^ 64, u9.getMem (BitVec.ofNat 64 B) =
      layMem (layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))))) 9))
        1 idx) 2 idx) 3 idx B := m9
  rw [g _ (by omega), g _ (by omega), g _ (by omega), g A hA]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
def zoneLay (o : Nat) : Nat := if o < 15344 then 1 else if o < 18400 then 2 else 3
def pathOut (M : Nat → Word) (lay r p : Nat) : Word :=
  match (List.range (lvH lay)).find? (fun j => decide (lvHit lay r j p)) with
  | some j => M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))
  | none => 0
def out2 (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 64 then M (WIT + o)
  else if o < 8000 then
    M (WIT + 64 + 896 * (8 - min ((o - 64) / 880) 8) + (o - 64 - 880 * min ((o - 64) / 880) 8))
  else if o < 12224 then M (WIT + o + 136)
  else if o < 21456 then
    (if o - (lvDst (zoneLay o) - WIT) < pathTop (zoneLay o) then
      pathOut M (zoneLay o) (lroute (zoneLay o) idx) (o - (lvDst (zoneLay o) - WIT))
    else M (chSrc (zoneLay o) - SNAP2 + WIT + (o - (chDst (zoneLay o) - WIT))))
  else if o = 21456 then M WIT
  else if o = 21464 then M (WIT + 8)
  else if o = 21472 then 0
  else LoadKind.wu.fromWord (M (WIT + 16)) 0
theorem lay_consts : lvDst 1 = 0x800 + 12224 ∧ lvDst 2 = 0x800 + 15344 ∧ lvDst 3 = 0x800 + 18400 ∧
    chDst 1 = 0x800 + 12224 + 368 ∧ chDst 2 = 0x800 + 15344 + 304 ∧ chDst 3 = 0x800 + 18400 + 304 := by
  unfold lvDst chDst; decide
theorem snap_read (M : Nat → Word) (idx x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    (layMem (layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx) 2 idx) 3 idx) (SNAP2 + x) =
      M (WIT + x) := by
  have hS : SNAP2 = 0x300000 := rfl
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]
  unfold topMem regsMem hdrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show SNAP2 + x - SNAP2 = x by omega]
theorem lays_low (M : Nat → Word) (idx A : Nat) (hA : A < WIT + 12224) :
    (layMem (layMem (layMem M 1 idx) 2 idx) 3 idx) A = M A := by
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 2 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 1 (by omega) idx A (Or.inl (by omega))]
theorem pre_low (M : Nat → Word) (A : Nat) (hA : WIT + 12224 ≤ A) (hA' : A < WIT + 21488) (h8 : (A - WIT) % 8 = 0) :
    topMem (regsMem (hdrMem (zMem (snapMem M))) 9) A = 0 := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold topMem regsMem hdrMem zMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem pre_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    topMem (regsMem (hdrMem (zMem (snapMem M))) 9) (SNAP2 + x) = M (WIT + x) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold topMem regsMem hdrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show SNAP2 + x - SNAP2 = x by omega]
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
  have hD : 0x800 + 12224 ≤ lvDst lay ∧ lvDst lay % 16 = 0 ∧ lvDst lay + pathTop lay + 8 * 344 ≤ 0x800 + 21456 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hsrc : 0x300000 + 8136 ≤ chSrc lay ∧ chSrc lay + 8 * 344 ≤ 0x300000 + 21832 ∧ chSrc lay % 8 = 0 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hr := lroute_lt lay idx
  have hpt : pathTop lay % 16 = 0 := by unfold pathTop; split <;> omega
  unfold layMem
  by_cases hp : o - (lvDst lay - WIT) < pathTop lay
  · rw [if_pos hp]
    unfold lvsMem pathOut
    rw [if_pos (by omega), show WIT + o - lvDst lay = o - (lvDst lay - WIT) by omega]
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
  · rw [if_neg hp, lvsMem_out _ lay hl _ hr _ le_rfl _ (Or.inr (by omega))]
    unfold chMem
    rw [if_pos (by omega)]
    have := hP (chSrc lay - SNAP2 + (WIT + o - chDst lay)) (by omega) (by omega)
    rw [show SNAP2 + (chSrc lay - SNAP2 + (WIT + o - chDst lay)) = chSrc lay + (WIT + o - chDst lay) by omega]
      at this
    rw [this, show WIT + (chSrc lay - SNAP2 + (WIT + o - chDst lay)) =
      chSrc lay - SNAP2 + WIT + (o - (chDst lay - WIT)) by omega]
theorem run2_zone (M : Nat → Word) (idx o : Nat) (ho : o < 21488) (h8 : o % 8 = 0) :
    run2Mem M idx (WIT + o) = out2 M idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have hTs : ∀ x < 8 * 2729, x % 8 = 0 → topMem (regsMem (hdrMem (zMem (snapMem M))) 9) (SNAP2 + x) = M (WIT + x) :=
    fun x hx h => pre_snap M x hx h
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  unfold run2Mem tailMem out2
  by_cases ht : 21456 ≤ o
  · have hs := fun x hx h => snap_read M idx x hx h
    rcases (show o = 21456 ∨ o = 21464 ∨ o = 21472 ∨ o = 21480 by omega) with rfl | rfl | rfl | rfl
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
    by_cases hl : o < 12224
    · rw [lays_low _ idx (WIT + o) (by omega)]
      by_cases h64 : o < 64
      · rw [if_pos h64]
        unfold topMem regsMem hdrMem zMem snapMem
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
          show SNAP2 + (WIT + o - WIT) - SNAP2 = o by omega]
      · rw [if_neg h64]
        by_cases h8k : o < 8000
        · rw [if_pos h8k]
          unfold topMem regsMem hdrMem zMem snapMem
          rw [if_neg (by omega), if_pos (by omega), show (9 : Nat) - 1 = 8 from rfl,
            show WIT + o - WIT - 64 = o - 64 by omega, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          rw [show WIT + (SNAP2 + 64 + 896 * (8 - min ((o - 64) / 880) 8) + (o - 64 - 880 * min ((o - 64) / 880) 8) -
            SNAP2) = WIT + 64 + 896 * (8 - min ((o - 64) / 880) 8) + (o - 64 - 880 * min ((o - 64) / 880) 8) by omega]
        · rw [if_neg h8k, if_pos (by omega)]
          unfold topMem regsMem hdrMem zMem snapMem
          rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          rw [show WIT + (SNAP2 + 8136 + (WIT + o - (WIT + 8000)) - SNAP2) = WIT + o + 136 by omega]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have hZ1 : ∀ A, lvDst 1 ≤ A → A < chDst 1 → (A - WIT) % 8 = 0 →
          topMem (regsMem (hdrMem (zMem (snapMem M))) 9) A = 0 := fun A h1 h2 h3 =>
        pre_low M A (by omega) (by omega) h3
      by_cases hz1 : o < 15344
      · have hzl : zoneLay o = 1 := by unfold zoneLay; rw [if_pos hz1]
        rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega)),
          layMem_out _ 2 (by omega) idx (WIT + o) (Or.inl (by omega))]
        exact layMem_zone (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) M 1 (by omega) idx hTs hZ1 o (by omega)
          (by omega) h8
      · have hP2 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx
            (SNAP2 + x) = M (WIT + x) := fun x hx h => by
          rw [layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hTs x hx h
        have hZ2 : ∀ A, lvDst 2 ≤ A → A < chDst 2 → (A - WIT) % 8 = 0 →
            layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx A = 0 := fun A h1 h2 h3 => by
          rw [layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
          exact pre_low M A (by omega) (by omega) h3
        by_cases hz2 : o < 18400
        · have hzl : zoneLay o = 2 := by unfold zoneLay; rw [if_neg hz1, if_pos hz2]
          rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega))]
          exact layMem_zone (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx) M 2 (by omega) idx hP2 hZ2 o (by omega)
            (by omega) h8
        · have hzl : zoneLay o = 3 := by unfold zoneLay; rw [if_neg hz1, if_neg hz2]
          have hP3 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9))
              1 idx) 2 idx (SNAP2 + x) = M (WIT + x) := fun x hx h => by
            rw [layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hP2 x hx h
          have hZ3 : ∀ A, lvDst 3 ≤ A → A < chDst 3 → (A - WIT) % 8 = 0 →
              layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx) 2 idx A = 0 := fun A h1 h2 h3 => by
            rw [layMem_out _ 2 (by omega) idx A (Or.inr (by omega)), layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
            exact pre_low M A (by omega) (by omega) h3
          rw [hzl]
          exact layMem_zone (layMem (layMem (topMem (regsMem (hdrMem (zMem (snapMem M))) 9)) 1 idx) 2 idx) M 3 (by omega) idx hP3 hZ3 o
            (by omega) (by omega) h8
end ClaudeWCT.W9.Machine.Expand.Compact2
end
