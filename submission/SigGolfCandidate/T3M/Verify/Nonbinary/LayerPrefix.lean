import SigGolfCandidate.Choice.MachineSelect

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
abbrev prefixHead := Choice.MachineSelect.head
abbrev prefixChoose := Choice.MachineSelect.choose
abbrev prefixReadLow := Choice.MachineSelect.readLow
abbrev prefixReadHigh := Choice.MachineSelect.readHigh
def prefixSetupWordsOf (a : Nat) : List (BitVec 32) :=
  [0x0e84b303,
   BitVec.ofNat 32 ((4096 - (a - 11808)) % 4096 * 2 ^ 20 + 10 * 2 ^ 15 + 8 * 2 ^ 7 + 0x13)]
def prefixTailWordsOf (_a : Nat) : List (BitVec 32) :=
  [0x3a8de93,0xc81713,0x677733,0x49070067]
def prefixWordsOf (a : Nat) : List (BitVec 32) :=
  prefixSetupWordsOf a ++ prefixHead ++ prefixChoose ++
    prefixReadLow ++ prefixTailWordsOf a ++ prefixReadHigh ++ prefixTailWordsOf a
def aVals : List Nat := [13664,13680,13712,13728,13760,13776,13808,13824,13856]
sym_block setupBase := symRun { noAlias := true } (prefixSetupWordsOf 13760) (pcOf 1070) 200
def prefixSetupRegs (a : Nat) : RegFile :=
  setupBase.res.st.regs.set .x8 (.bin .add (.reg .x10) (.c (BitVec.ofNat 64 (2 ^ 64 - (a - 11808)))))
def prefixSetupRes (a : Nat) (p : Word) : Result :=
  { setupBase.res with pc := .c (p + 4 + 4), st := { setupBase.res.st with regs := prefixSetupRegs a } }
theorem prefix_setup_run (a : Nat) (ha : a ∈ aVals) (p : Word) :
    symRun { noAlias := true } (prefixSetupWordsOf a) p 200 = some (prefixSetupRes a p) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem prefix_setup_spec {image : Image} (s : MachineState) (a p : Nat) (ha : a ∈ aVals)
    (hpc : s.pc = pcOf p) (hcode : CodeAt image (pcOf p) (prefixSetupWordsOf a))
    (h9 : s.getReg .x9 = 0xffbf10#64) (h10 : s.getReg .x10 = BitVec.ofNat 64 a)
    (hmask : s.getMem 0xffbff8#64 = 520192#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (p+2) ∧
      t.getReg .x8 = 11808#64 ∧ t.getReg .x6 = 520192#64 ∧
      RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  have hm : s.getMem (s.getReg .x9 + 232#64) = 520192#64 := by
    rw [h9]; exact hmask
  have ho : (prefixSetupRes a (pcOf p)).obligs s := by
    simp [Result.obligs, prefixSetupRes, prefixSetupRegs, setupBase.res,
      rv_simp, h9, accessValid_iff, MEMORY_BYTES]
  have hal : 13600 ≤ a ∧ a ≤ 13856 := by
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  let t := (prefixSetupRes a (pcOf p)).toState s
  refine ⟨t, symRun_sound (prefix_setup_run a ha (pcOf p)) hcode s hpc ho, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, prefixSetupRes, setupBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  · simp only [t, Result.toState_getReg, prefixSetupRes, prefixSetupRegs, RegFile.get,
      RegFile.set, E.eval, BinOp.eval, h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp [t, prefixSetupRes, prefixSetupRegs, setupBase.res, rv_simp, RegFile.set, hm]
  · intro r hr; cases r <;> simp at hr <;>
      simp [t, prefixSetupRes, prefixSetupRegs, setupBase.res, rv_simp] <;> rfl
  · intro A hA hn
    simp [t, prefixSetupRes, prefixSetupRegs, setupBase.res, rv_simp]

sym_block prefixBase := symRun { noAlias := true } (prefixTailWordsOf 13760) (pcOf 1078) 200
def prefixRegs (_a : Nat) : RegFile := prefixBase.res.st.regs
def prefixRes (_a : Nat) : Result := prefixBase.res
end SigGolfCandidate.T3M.Verify.Nonbinary
