import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE gateE grpE fieldE fieldLen capE idxE)
set_option maxRecDepth 100000
def ECBASE : Nat := 0xffe000
def efsi (k : Nat) : Nat := ClaudeWCT.W9.Machine.Sign.SearchM.fsi k + 29890
def esci (k : Nat) : Nat := ClaudeWCT.W9.Machine.Sign.SearchM.sci k + 29890
def resHead (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst (2 ^ 21)), (.x7, cst ECBASE)], [], []⟩, if d then pcOf 40897 else pcOf 41062, false,
    if d then 3 else 4, if d then 3 else 4, [⟨.ltu, .reg .x19, cst (2 ^ 21), d⟩], none⟩
def resTrial : PRes :=
  ⟨⟨rfs [(.x6, ctrE), (.x10, cst DIG), (.x11, cst 64), (.x12, cst NBUF), (.x28, cst DIG)],
    [mw (DIG + 24) ctrE, mw (DIG + 16) (cst 0)], []⟩, pcOf 40909, true, 12, 12, [], none⟩
def resGate (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, gateE), (.x22, .ld (cst NBUF)), (.x28, cst NBUF)], [], []⟩,
    if d then pcOf 41060 else pcOf 40917, false, 7, 7, [⟨.eq, gateE, .c 0, d⟩], none⟩
def resCost0 : PRes := ⟨⟨rfs [(.x20, cst 0), (.x21, cst ECOST)], [], []⟩, pcOf (efsi 0), false, 3, 3, [], none⟩
def resField (k : Nat) (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst 16200), (.x24, ClaudeWCT.W9.Machine.Sign.SearchM.childE k), (.x25, fieldE k), (.x28, cst 131072)], [], []⟩,
    if d then pcOf 41060 else pcOf (esci k), false, fieldLen k, fieldLen k,
    [⟨.geu, fieldE k, cst 16200, d⟩], none⟩
def resSc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x21) (.reg .x25))], [], []⟩, pcOf (esci k + 1), false, 1, 1, [], none⟩
def resSc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (esci k + 3), false, 1, 1, [], none⟩
def resCc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x7) (.reg .x24))], [], []⟩, pcOf (esci k + 4), false, 1, 1, [], none⟩
def resCc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (efsi (k + 1)), false, 1, 1, [], none⟩
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 41060 else pcOf 41054, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
def resFinal : PRes :=
  ⟨⟨rfs [(.x22, idxE), (.x28, cst IDXV)], [mw IDXV idxE], []⟩, pcOf 1421, false, 7, 7, [], none⟩
def resNext : PRes :=
  ⟨⟨rfs [(.x19, .bin .add (.reg .x19) (cst 1))], [], []⟩, pcOf 40893, false, 2, 2, [], none⟩
def resFail : PRes :=
  ⟨⟨rfs [(.x5, cst 1), (.x10, cst 1)], [], []⟩, pcOf 41064, true, 2, 2, [], none⟩
theorem chk_head : (optBeq (run expLook [40897, 41062] 40893 [.br true]) (resHead true) &&
    optBeq (run expLook [40897, 41062] 40893 [.br false]) (resHead false)) = true := by decide +kernel
theorem chk_trial : optBeq (run expLook [] 40897 []) resTrial = true := by decide +kernel
theorem chk_gate : (optBeq (run expLook [41060, 40917] 40910 [.br true]) (resGate true) &&
    optBeq (run expLook [41060, 40917] 40910 [.br false]) (resGate false)) = true := by decide +kernel
theorem chk_cost0 : optBeq (run expLook [efsi 0] 40917 []) resCost0 = true := by decide +kernel
theorem chk_fields : (List.range 9).all (fun k =>
    optBeq (run expLook [41060, esci k] (efsi k) [.br true]) (resField k true) &&
    optBeq (run expLook [41060, esci k] (efsi k) [.br false]) (resField k false) &&
    optBeq (run expLook [esci k + 1] (esci k) []) (resSc1 k) &&
    optBeq (run expLook [esci k + 3] (esci k + 2) []) (resSc3 k) &&
    expLook (esci k + 1) == some 0x00034303) = true := by
  decide +kernel
theorem chk_childs : (List.range 9).all (fun k =>
    optBeq (run expLook [esci k + 4] (esci k + 3) []) (resCc1 k) &&
    optBeq (run expLook [efsi (k + 1)] (esci k + 5) []) (resCc3 k) &&
    expLook (esci k + 4) == some 0xd8034303) = true := by
  decide +kernel
theorem chk_cap : (optBeq (run expLook [41060, 41054] 41052 [.br true]) (resCap true) &&
    optBeq (run expLook [41060, 41054] 41052 [.br false]) (resCap false)) = true := by decide +kernel
theorem chk_final : optBeq (run expLook [1421] 41054 []) resFinal = true := by decide +kernel
theorem chk_next : optBeq (run expLook [40893] 41060 []) resNext = true := by decide +kernel
theorem chk_fail : optBeq (run expLook [] 41062 []) resFail = true := by decide +kernel
theorem efsi_nine : efsi 9 = 41052 := by decide
theorem esci_lt : ∀ k, k < 9 → esci k + 6 = efsi (k + 1) ∧ efsi k < esci k ∧ esci k + 5 < 41052 := by decide +kernel
theorem run_head (d : Bool) : run expLook [40897, 41062] 40893 [.br d] = some (resHead d) := by
  have h := chk_head
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_trial : run expLook [] 40897 [] = some resTrial := optBeq_eq chk_trial
theorem run_gate (d : Bool) : run expLook [41060, 40917] 40910 [.br d] = some (resGate d) := by
  have h := chk_gate
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_cost0 : run expLook [efsi 0] 40917 [] = some resCost0 := optBeq_eq chk_cost0
theorem chk_fields_k {k : Nat} (hk : k < 9) :
    (optBeq (run expLook [41060, esci k] (efsi k) [.br true]) (resField k true) &&
    optBeq (run expLook [41060, esci k] (efsi k) [.br false]) (resField k false) &&
    optBeq (run expLook [esci k + 1] (esci k) []) (resSc1 k) &&
    optBeq (run expLook [esci k + 3] (esci k + 2) []) (resSc3 k) &&
    expLook (esci k + 1) == some 0x00034303) = true :=
  List.all_eq_true.mp chk_fields k (List.mem_range.mpr hk)
theorem chk_childs_k {k : Nat} (hk : k < 9) :
    (optBeq (run expLook [esci k + 4] (esci k + 3) []) (resCc1 k) &&
    optBeq (run expLook [efsi (k + 1)] (esci k + 5) []) (resCc3 k) &&
    expLook (esci k + 4) == some 0xd8034303) = true :=
  List.all_eq_true.mp chk_childs k (List.mem_range.mpr hk)
theorem run_cc1 (k : Nat) (hk : k < 9) : run expLook [esci k + 4] (esci k + 3) [] = some (resCc1 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem run_cc3 (k : Nat) (hk : k < 9) : run expLook [efsi (k + 1)] (esci k + 5) [] = some (resCc3 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu2 (k : Nat) (hk : k < 9) : expLook (esci k + 4) = some 0xd8034303 := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_field (k : Nat) (hk : k < 9) (d : Bool) :
    run expLook [41060, esci k] (efsi k) [.br d] = some (resField k d) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.1.1.1.2
  · exact optBeq_eq h.1.1.1.1
theorem run_sc1 (k : Nat) (hk : k < 9) : run expLook [esci k + 1] (esci k) [] = some (resSc1 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1.2
theorem run_sc3 (k : Nat) (hk : k < 9) : run expLook [esci k + 3] (esci k + 2) [] = some (resSc3 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu (k : Nat) (hk : k < 9) : expLook (esci k + 1) = some 0x00034303 := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_cap (d : Bool) : run expLook [41060, 41054] 41052 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_final : run expLook [1421] 41054 [] = some resFinal := optBeq_eq chk_final
theorem run_next : run expLook [40893] 41060 [] = some resNext := optBeq_eq chk_next
theorem run_fail : run expLook [] 41062 [] = some resFail := optBeq_eq chk_fail
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
abbrev srchRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x22, .x24, .x25, .x28]
def SrchW (A : Nat) : Prop := A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV
structure ESrchPre (rho : Digest) (m : Message) (s : MachineState) : Prop where
  pc : s.pc = pcOf 40893
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
  cost : ExpCostAt s
def ESrchPost (s0 : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt 41062 t
  | some (c, N), t => t.pc = pcOf 1421 ∧ t.getReg .x5 = 0 ∧ WCT9.producerAdmissible N = true ∧ OutAt t NBUF N ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex N) ∧
      t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N) ∧ RegsExcept s0 t srchRegs ∧ Frame s0 t SrchW ∧
      c.toNat < 2 ^ 21 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE gateE grpE fieldE fieldLen capE idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval gateE_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000 in
theorem expCostBytes_chk : costChk 0 expCostBytes = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem expCostBytes_length : expCostBytes.length = 16384 := by decide +kernel
theorem expCostBytes_getD (f : Nat) (hf : f < 16384) : (expCostBytes.getD f 0).toNat = costByte f := by
  have := costChk_getD expCostBytes 0 expCostBytes_chk f (by rw [expCostBytes_length]; exact hf)
  rwa [Nat.zero_add] at this
theorem ecost_byte {s : MachineState} (hc : ExpCostAt s) {f : Nat} (hf : f < 16384) :
    s.getByte (BitVec.ofNat 64 (ECOST + f)) = BitVec.ofNat 8 (costByte f) := by
  rw [getByte_eq_word s _ (by unfold ECOST; omega)]
  rw [show (ECOST + f) / 8 * 8 = ECOST + 8 * (f / 8) by unfold ECOST; omega,
    show (ECOST + f) % 8 = f % 8 by unfold ECOST; omega, hc (f / 8) (by omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  apply BitVec.eq_of_toNat_eq
  rw [← expCostBytes_getD f hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (Nat.mod_lt _ (by decide)), show 8 * (f / 8) + f % 8 = f by omega]
theorem outS {s : MachineState} {a : BitVec 256} (h : OutAt s NBUF a) :
    ClaudeWCT.W9.Machine.Sign.OutAt s ClaudeWCT.W9.Machine.Sign.NBUF a := fun k hk => h k hk
section pieces
variable {im : Image}
theorem head_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 40893) (i : Nat)
    (hi : i ≤ 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ t.pc = (if i < 2 ^ 21 then pcOf 40897 else pcOf 41062) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) ∧ t.getReg .x7 = BitVec.ofNat 64 ECBASE := by
  have hbr : ∀ b ∈ (resHead (decide (i < 2 ^ 21))).brs, b.holds s := by
    intro b hb
    simp only [resHead, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h19, BitVec.ult, toNat_ofNat_lt (by omega : i < 2 ^ 64),
      toNat_ofNat_lt (by decide : 2 ^ 21 < 2 ^ 64)]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_head _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl, by rw [hr]; rfl⟩
  · simp only [resHead]; split <;> decide
  · rw [hp]; simp only [resHead]; by_cases h : i < 2 ^ 21 <;> simp [h]
theorem trial_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 40897) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 12 12 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 40909 ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 (i * 2 ^ 32) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 24 ∨ A = DIG + 16) := by
  obtain ⟨hs, hp, he, hr, hm⟩ := piece hl run_trial s hpc rfl (by intro b hb; cases hb) rfl
  have hctr : ctrE.eval s = BitVec.ofNat 64 (i * 2 ^ 32) := by
    simp only [ctrE, cst, E.eval, BinOp.eval, h19, toNat_ofNat_lt (by decide : (32 : Nat) < 2 ^ 64)]
    exact ofNat_shl i 32
  refine ⟨_, hs, he rfl, hp, by rw [hr]; rfl, by rw [hr]; rfl, by rw [hr]; rfl, ?_, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_neg (by decide),
      memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl]; rfl
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hctr]
  · intro A hA hn
    simp only [not_or] at hn
    rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), if_neg hn.1, memEval_cons_ofNat _ _ _ _ _ hA (by decide),
      if_neg hn.2]; rfl
theorem gate_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 40910) (a : BitVec 256)
    (ha : OutAt s NBUF a) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = (if a.toNat / 2 ^ 235 % 2 ^ 21 < 1092 then pcOf 40917 else pcOf 41060) ∧
      t.getReg .x22 = a.extractLsb' 0 64 ∧ RegsExcept s t [.x6, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  have hg := gateE_eval s a (outS ha)
  have hbr : ∀ b ∈ (resGate (decide ¬ (a.toNat / 2 ^ 235 % 2 ^ 21 < 1092))).brs, b.holds s := by
    intro b hb
    simp only [resGate, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hg]
    by_cases h0 : a.toNat / 2 ^ 235 % 2 ^ 21 < 1092
    · simp only [h0, if_true, not_true_eq_false, decide_false]; decide
    · simp only [h0, if_false, not_false_eq_true, decide_true]; decide
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_gate _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · rw [hp]; simp only [resGate]
    by_cases h0 : a.toNat / 2 ^ 235 % 2 ^ 21 < 1092
    · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
    · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
  · rw [hr]
    have h0 := ha 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    show s.getMem (BitVec.ofNat 64 NBUF) = _
    exact h0
theorem cost0_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 40917) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (efsi 0) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x21 = BitVec.ofNat 64 ECOST ∧ RegsExcept s t [.x20, .x21] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_cost0 s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, by rw [hr]; rfl, by rw [hr]; rfl, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
theorem field_spec (hl : LookOK im expLook) (k : Nat) (hk : k < 9) (s : MachineState)
    (hpc : s.pc = pcOf (efsi k)) (a : BitVec 256) (ha : OutAt s NBUF a) :
    ∃ t c, Steps im s c c t ∧ c ≤ 9 ∧
      t.pc = (if WCT9.field a ⟨k, hk⟩ < 16200 then pcOf (esci k) else pcOf 41060) ∧
      t.getReg .x25 = BitVec.ofNat 64 (WCT9.field a ⟨k, hk⟩) ∧
      t.getReg .x24 = BitVec.ofNat 64 (childN a k) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  have hf := fieldE_eval s a (outS ha) k hk
  have hfd : WCT9.field a ⟨k, hk⟩ = a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 14 := rfl
  have hlt : a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 14 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hbr : ∀ b ∈ (resField k (decide ¬ (WCT9.field a ⟨k, hk⟩ < 16200))).brs, b.holds s := by
    intro b hb
    simp only [resField, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, hf, BitVec.ult, toNat_ofNat_lt hlt,
      toNat_ofNat_lt (by decide : 16200 < 2 ^ 64), hfd]
    rw [decide_not]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_field k hk _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · simp only [resField, fieldLen]; split <;> omega
  · rw [hp]; simp only [resField]
    by_cases h : WCT9.field a ⟨k, hk⟩ < 16200 <;> simp [h]
  · rw [hr]; exact hf
  · rw [hr]; exact childE_eval s a (outS ha) k hk
theorem decode_lbu : decodeInstruction 0x00034303 = some (.base (.LBU .x6 .x6 0)) := by rfl
theorem lbu_step (hl : LookOK im expLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (esci k + 1)) (f : Nat) (hf : f < 16384) (h6 : u.getReg .x6 = BitVec.ofNat 64 (ECOST + f))
    (hc : ExpCostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (esci k + 2) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte f) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (esci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : expLook ((u.pc.toNat - 0x1000) / 4) = some 0x00034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (esci k + 1) - 0x1000) / 4 = esci k + 1 by omega]
    exact look_lbu k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 0)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu
  have hcl : classify (.base (.LBU .x6 .x6 0)) = some (.load .bu .x6 .x6 (signExtend12 0)) := rfl
  have e : u.getReg .x6 + signExtend12 0 = BitVec.ofNat 64 (ECOST + f) := by
    rw [h6]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have hacc : accessValid (u.getReg .x6 + signExtend12 0) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show ECOST + f < 2 ^ 64 by unfold ECOST; omega), MEMORY_BYTES]
    unfold ECOST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    simp only [LoadKind.read, e, ecost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt f
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem sc_spec (hl : LookOK im expLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (esci k))
    (f S : Nat) (hf : f < 16384) (hS : S + 256 < 2 ^ 64) (h21 : s.getReg .x21 = BitVec.ofNat 64 ECOST)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 f) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : ExpCostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (esci k + 3) ∧ t.getReg .x20 = BitVec.ofNat 64 (S + costByte f) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_sc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resSc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (ECOST + f) := by
    rw [hr1]; show s.getReg .x21 + s.getReg .x25 = _; rw [h21, h25, ofNat_add_ofNat]
  have hcu : ExpCostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step hl k hk u hp1 f hf u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_sc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
theorem decode_lbu2 : decodeInstruction 0xd8034303 = some (.base (.LBU .x6 .x6 3456)) := by rfl
theorem lbu_step2 (hl : LookOK im expLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (esci k + 4)) (c : Nat) (hc' : c < 128) (h6 : u.getReg .x6 = BitVec.ofNat 64 (ECBASE + c))
    (hc : ExpCostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (esci k + 5) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte (16256 + c)) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (esci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : expLook ((u.pc.toNat - 0x1000) / 4) = some 0xd8034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (esci k + 4) - 0x1000) / 4 = esci k + 4 by omega]
    exact look_lbu2 k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 3456)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu2
  have hcl : classify (.base (.LBU .x6 .x6 3456)) = some (.load .bu .x6 .x6 (signExtend12 3456)) := rfl
  have hse : signExtend12 3456 = BitVec.ofNat 64 (2 ^ 64 - 640) := by decide
  have hf : 16256 + c < 16384 := by omega
  have e : u.getReg .x6 + signExtend12 3456 = BitVec.ofNat 64 (ECOST + (16256 + c)) := by
    rw [h6, hse, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    unfold ECBASE ECOST; omega
  have hacc : accessValid (u.getReg .x6 + signExtend12 3456) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show ECOST + (16256 + c) < 2 ^ 64 by unfold ECOST; omega), MEMORY_BYTES]
    unfold ECOST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    simp only [LoadKind.read, e, ecost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt (16256 + c)
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem cc_spec (hl : LookOK im expLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (esci k + 3))
    (c S : Nat) (hc' : c < 128) (hS : S + 256 < 2 ^ 64) (h7 : s.getReg .x7 = BitVec.ofNat 64 ECBASE)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : ExpCostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (efsi (k + 1)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (S + costByte (16256 + c)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_cc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resCc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (ECBASE + c) := by
    rw [hr1]; show s.getReg .x7 + s.getReg .x24 = _; rw [h7, h24, ofNat_add_ofNat]
  have hcu : ExpCostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step2 hl k hk u hp1 c hc' u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_cc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
theorem fields_from (hl : LookOK im expLook) (a : BitVec 256) :
    ∀ n k, k + n = 9 → ∀ v : MachineState, v.pc = pcOf (efsi k) → OutAt v NBUF a → ExpCostAt v →
      v.getReg .x21 = BitVec.ofNat 64 ECOST → v.getReg .x7 = BitVec.ofNat 64 ECBASE →
      v.getReg .x20 = BitVec.ofNat 64 (psum a k) →
      ∃ t c, Steps im v c c t ∧ c ≤ 15 * n ∧ RegsExcept v t [.x6, .x20, .x24, .x25, .x28] ∧
        Frame v t (fun _ => False) ∧
        (if ∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16200
          then t.pc = pcOf 41052 ∧ t.getReg .x20 = BitVec.ofNat 64 (psum a 9) else t.pc = pcOf 41060) := by
  intro n
  induction n with
  | zero =>
    intro k hk v hv _ _ _ _ h20
    have hk9 : k = 9 := by omega
    subst hk9
    refine ⟨v, 0, Steps.refl v, le_refl _, RegsExcept.refl _ _, Frame.refl _ _, ?_⟩
    rw [if_pos (fun k' hk' hle => by omega)]
    exact ⟨by rw [hv, efsi_nine], h20⟩
  | succ n ih =>
    intro k hk v hv ha hc h21 h7 h20
    have hk9 : k < 9 := by omega
    obtain ⟨t1, c1, s1, hc1, p1, x25, x24, r1, f1⟩ := field_spec hl k hk9 v hv a ha
    by_cases hf : WCT9.field a ⟨k, hk9⟩ < 16200
    · rw [if_pos hf] at p1
      have hc1' : ExpCostAt t1 := fun j hj => by rw [f1.get (by unfold ECOST; omega) (fun h => h)]; exact hc j hj
      obtain ⟨t2, s2, p2, x20', r2, f2⟩ := sc_spec hl k hk9 t1 p1 (WCT9.field a ⟨k, hk9⟩) (psum a k)
        (fieldN_lt a k) (by have := psum_le a k; omega) (by rw [r1.get (by decide)]; exact h21) x25
        (by rw [r1.get (by decide)]; exact h20) hc1'
      have hc2' : ExpCostAt t2 := fun j hj => by rw [f2.get (by unfold ECOST; omega) (fun h => h)]; exact hc1' j hj
      obtain ⟨t2b, s2b, p2b, x20b, r2b, f2b⟩ := cc_spec hl k hk9 t2 p2 (childN a k)
        (psum a k + costByte (WCT9.field a ⟨k, hk9⟩)) (childN_lt a k)
        (by have := psum_le a k; have := costByte_lt (WCT9.field a ⟨k, hk9⟩); omega)
        (by rw [r2.get (by decide), r1.get (by decide)]; exact h7)
        (by rw [r2.get (by decide)]; exact x24) x20' hc2'
      have ha2 : OutAt t2b NBUF a := fun j hj => by
        rw [f2b.get (by simp only [NBUF]; omega) (fun h => h), f2.get (by simp only [NBUF]; omega) (fun h => h),
          f1.get (by simp only [NBUF]; omega) (fun h => h)]
        exact ha j hj
      have hc2 : ExpCostAt t2b := fun j hj => by rw [f2b.get (by unfold ECOST; omega) (fun h => h)]; exact hc2' j hj
      obtain ⟨t, c, s3, hc3, r3, f3, p3⟩ := ih (k + 1) (by omega) t2b p2b ha2 hc2
        (by rw [r2b.get (by decide), r2.get (by decide), r1.get (by decide)]; exact h21)
        (by rw [r2b.get (by decide), r2.get (by decide), r1.get (by decide)]; exact h7)
        (by rw [x20b, psum_succ]; rfl)
      refine ⟨t, c1 + 3 + 3 + c, ((s1.trans s2).trans s2b).trans s3, by omega,
        (((r1.trans r2).trans r2b).trans r3).mono (by decide),
        (((f1.trans f2).trans f2b).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hiff : (∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16200) ↔
          (∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16200) := by
        constructor
        · intro h k' hk' hle; exact h k' hk' (by omega)
        · intro h k' hk' hle
          by_cases he : k' = k
          · subst he; exact hf
          · exact h k' hk' (by omega)
      by_cases hall : ∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16200
      · rw [if_pos hall] at p3; rw [if_pos (hiff.2 hall)]; exact p3
      · rw [if_neg hall] at p3; rw [if_neg (fun h => hall (hiff.1 h))]; exact p3
    · rw [if_neg hf] at p1
      refine ⟨t1, c1, s1, by omega, r1.mono (by decide), f1, ?_⟩
      rw [if_neg (fun h => hf (h k hk9 le_rfl))]; exact p1
theorem cap_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41052) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 712 then pcOf 41054 else pcOf 41060) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 713 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 713 < 2 ^ 64 by decide)]
    by_cases h : S < 713 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 712))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 712
    · simp only [show S < 713 by omega, if_true, h0, not_true_eq_false, decide_false]; decide
    · simp only [show ¬ S < 713 by omega, if_false, h0, not_false_eq_true, decide_true]; decide
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 712
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
theorem checks_spec (hl : LookOK im expLook) (u : MachineState) (hpc : u.pc = pcOf 40910) (a : BitVec 256)
    (ha : OutAt u NBUF a) (hc : ExpCostAt u) (h7 : u.getReg .x7 = BitVec.ofNat 64 ECBASE) :
    ∃ t c, Steps im u c c t ∧ c ≤ 147 ∧ RegsExcept u t [.x6, .x7, .x20, .x21, .x22, .x24, .x25, .x28] ∧
      Frame u t (fun _ => False) ∧
      (if WCT9.producerAdmissible a = true then t.pc = pcOf 41054 ∧ t.getReg .x22 = a.extractLsb' 0 64
        else t.pc = pcOf 41060) := by
  obtain ⟨t1, s1, p1, x22, r1, f1⟩ := gate_spec hl u hpc a ha
  have hadm := WCT9.admissible_iff a
  have hprod := WCT9.producerAdmissible_iff a
  by_cases hg : a.toNat / 2 ^ 235 % 2 ^ 21 < 1092
  · rw [if_pos hg] at p1
    obtain ⟨t2, s2, p2, x20, x21, r2, f2⟩ := cost0_spec hl t1 p1
    have ha2 : OutAt t2 NBUF a := fun j hj => by
      rw [f2.get (by simp only [NBUF]; omega) (fun h => h), f1.get (by simp only [NBUF]; omega) (fun h => h)]
      exact ha j hj
    have hc2 : ExpCostAt t2 := fun j hj => by
      rw [f2.get (by unfold ECOST; omega) (fun h => h), f1.get (by unfold ECOST; omega) (fun h => h)]; exact hc j hj
    obtain ⟨t3, c3, s3, hc3, r3, f3, p3⟩ := fields_from hl a 9 0 rfl t2 p2 ha2 hc2 x21
      (by rw [r2.get (by decide), r1.get (by decide)]; exact h7) (by rw [x20]; rfl)
    have h22 : ∀ {t : MachineState}, RegsExcept t2 t [.x6, .x20, .x24, .x25, .x28] →
        t.getReg .x22 = a.extractLsb' 0 64 := fun h => by rw [h.get (by decide), r2.get (by decide)]; exact x22
    have hall : (∀ k' (hk' : k' < 9), 0 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 16200) ↔
        ∀ c : WCT9.Coord, WCT9.field a c < 16200 :=
      ⟨fun h c => h c.val c.isLt (Nat.zero_le _), fun h k' hk' _ => h ⟨k', hk'⟩⟩
    by_cases hf : ∀ c : WCT9.Coord, WCT9.field a c < 16200
    · rw [if_pos (hall.2 hf)] at p3
      obtain ⟨p3, x20'⟩ := p3
      have hS := psum_le a 9
      obtain ⟨t4, s4, p4, r4, f4⟩ := cap_spec hl t3 p3 (psum a 9) (by omega) x20'
      refine ⟨t4, 7 + 3 + c3 + 2, ((s1.trans s2).trans s3).trans s4, by omega,
        (((r1.trans r2).trans r3).trans r4).mono (by decide),
        (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h), ?_⟩
      have hjc : psum a 9 = WCT9.jointCost a := psum_nine a hf
      by_cases hA : WCT9.producerAdmissible a = true
      · rw [if_pos hA]
        have hcap := (hprod.1 hA).2
        rw [if_pos (by rw [hjc]; exact hcap)] at p4
        exact ⟨p4, by rw [r4.get (by decide)]; exact h22 r3⟩
      · rw [if_neg hA]
        have hcap : ¬ psum a 9 ≤ 712 := fun h => hA (hprod.2 ⟨hadm.2 ⟨hg, hf⟩, by rw [← hjc]; exact h⟩)
        rw [if_neg hcap] at p4; exact p4
    · rw [if_neg (fun h => hf (hall.1 h))] at p3
      refine ⟨t3, 7 + 3 + c3, (s1.trans s2).trans s3, by omega, ((r1.trans r2).trans r3).mono (by decide),
        ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hA : ¬ WCT9.producerAdmissible a = true := fun h => hf ((hadm.1 (hprod.1 h).1).2)
      rw [if_neg hA]; exact p3
  · rw [if_neg hg] at p1
    refine ⟨t1, 7, s1, by omega, r1.mono (by decide), f1, ?_⟩
    have hA : ¬ WCT9.producerAdmissible a = true := fun h => hg ((hadm.1 (hprod.1 h).1).1)
    rw [if_neg hA]; exact p1
theorem final_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41054) (a : BitVec 256)
    (h22 : s.getReg .x22 = a.extractLsb' 0 64) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 1421 ∧ t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      RegsExcept s t [.x22, .x28] ∧ Frame s t (fun A => A = IDXV) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_final s hpc rfl (by intro b hb; cases hb) rfl
  have hidx : idxE.eval s = BitVec.ofNat 64 (WCT9.digestIndex a) := by
    simp only [idxE, cst, E.eval, h22]
    rw [srl_eval _ 33 (by decide), sll_eval _ 0 (by decide)]
    exact shl0_shr33 a
  refine ⟨_, hs, hp, by rw [hr]; exact hidx, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide) (by decide), if_pos rfl, hidx]
  · intro A hA hn
    rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide), if_neg hn]; rfl
theorem next_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41060) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 40893 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_next s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]
  show s.getReg .x19 + BitVec.ofNat 64 1 = _
  rw [h19, ofNat_add_ofNat]
theorem fail_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41062) :
    ∃ t, Steps im s 2 2 t ∧ fetch im t = some (.base .ECALL) ∧ FailedAt 41062 t := by
  obtain ⟨hs, hp, he, hr, -⟩ := piece hl run_fail s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, he rfl, ⟨hp, by rw [hr]; rfl, by rw [hr]; rfl⟩⟩
end pieces
structure LInv (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 40893
  hi : i ≤ 2 ^ 21
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t srchRegs
  frame : Frame s0 t SrchW
theorem outAt_writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    OutAt (writeHash t a) NBUF a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
theorem costAt_frame {s t : MachineState} (h : ExpCostAt s) (hf : Frame s t SrchW) : ExpCostAt t := fun j hj => by
  rw [hf.get (by unfold ECOST; omega) (by unfold SrchW ECOST; simp only [DIG, NBUF, IDXV]; omega)]; exact h j hj
section loop
variable {im : Image} {sk : BitVec 256}
theorem loop (hl : LookOK im expLook) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : ESrchPre rho m s0) :
    ∀ F i t, i + F = 2 ^ 21 → LInv s0 i t →
      TBSim im sk t (F * 200 + 100) (WCT9.digestSearch rho m i F) (ESrchPost s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, k1, s1, hk1, p1, -, -, -⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, s2, -, hf⟩ := fail_spec hl t1 p1
    exact (ClaudeWCT.W9.Machine.Sign.TBSim.pure_steps' (sk := sk) (s1.trans s2) (Q := ESrchPost s0) (a := none) hf).mono
      (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 21 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, x7h⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_pos hi] at p1
    obtain ⟨u, s2, hfu, p2, h10, h11, h12, h16, h24, r2, f2⟩ :=
      trial_spec hl t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u srchRegs :=
      ((hI.regs.trans r1).trans r2).mono (by decide)
    have fu : Frame s0 u SrchW := ((hI.frame.trans f1).trans f2).mono (fun A _ hA => by
      simp only [or_false] at hA
      rcases hA with hA | hA
      · exact hA
      · unfold SrchW; rcases hA with hA | hA <;> simp [hA])
    have mem : ∀ A, A < 2 ^ 64 → ¬ SrchW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ SrchW A := by
      intro A hA; simp only [SrchW, DIG, NBUF, IDXV] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput', digestInput_length']) h10 (by decide)
        (by decide) h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput', hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : WCT9.digestSearch rho m i (F + 1) =
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 i, output))
          else WCT9.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (ClaudeWCT.W9.Machine.Sign.TBSim.publicHash_bind' hfu h5 hv hq
      (W := 176 + (F * 200 + 100)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput']; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf 40910 := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : OutAt (writeHash u a) NBUF a := outAt_writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    have fuw : Frame s0 (writeHash u a) SrchW := (fu.trans fw).mono (fun A _ hA => by
      rcases hA with hA | hA
      · exact hA
      · unfold SrchW; right; right; left; exact hA)
    obtain ⟨v, c, sv, hcv, rv, fv, pv⟩ := checks_spec hl (writeHash u a) pw a hN (costAt_frame hpre.cost fuw)
      (by rw [getReg_writeHash, r2.get (by decide)]; exact x7h)
    have rv' : RegsExcept s0 v srchRegs :=
      ((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono
        (by decide)
    have fv' : Frame s0 v SrchW := (fuw.trans fv).mono (fun A _ hA => by
      simp only [or_false] at hA; exact hA)
    have hNv : OutAt v NBUF a := fun j hj => by
      rw [fv.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
    have x19v : v.getReg .x19 = BitVec.ofNat 64 i := by
      rw [rv.get (by decide), getReg_writeHash, r2.get (by decide), r1.get (by decide), hI.x19]
    by_cases hadm : WCT9.producerAdmissible a = true
    · rw [if_pos hadm] at pv
      simp only [hadm, ↓reduceIte]
      obtain ⟨w, sw, pw', x22w, idxw, rw', fw'⟩ := final_spec hl v pv.1 a pv.2
      refine (ClaudeWCT.W9.Machine.Sign.TBSim.pure_steps' (sv.trans sw) ?_).mono (by omega) (fun _ _ h => h)
      refine ⟨pw', by rw [rw'.get (by decide), rv'.get (by decide), hpre.x5], hadm, ?_, idxw, x22w, ?_, ?_,
        by rw [hc]; exact hi, by rw [hc, rw'.get (by decide), x19v]⟩
      · intro j hj; rw [fw'.get (by simp only [NBUF]; omega) (by simp only [IDXV, NBUF]; omega)]; exact hNv j hj
      · exact (rv'.trans rw').mono (by decide)
      · exact (fv'.trans fw').mono (fun A _ hA => by
          rcases hA with hA | hA
          · exact hA
          · unfold SrchW; right; right; right; exact hA)
    · rw [if_neg hadm] at pv
      simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, sw, pw', x19w, rw', fw'⟩ := next_spec hl v pv i hi x19v
      have hI' : LInv s0 (i + 1) w :=
        ⟨pw', by omega, x19w, (rv'.trans rw').mono (by decide),
          (fv'.trans fw').mono (fun A _ hA => by simp only [or_false] at hA; exact hA)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i + 1) w (by omega) hI')).mono (by omega) (fun _ _ h => h)
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
theorem esearch_tbsim {im : Image} (hc : NewCodeAt im) {sk : BitVec 256} {s0 : MachineState} {rho : Digest}
    {m : Message} (hpre : ESrchPre rho m s0) :
    TBSim im sk s0 (2 ^ 21 * 200 + 100) (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) (ESrchPost s0) := by
  have h := ESearch.loop (sk := sk) (expLook_ok hc) hpre (2 ^ 21) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩
  unfold WCT9.digestAttemptLimit
  exact h
end ClaudeWCT.W9.Machine.Expand
