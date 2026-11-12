import SigGolfCandidate.OuterNodeMachineCheck
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachineCounter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks
theorem b_failure_obligs (s : MachineState) : b_failure.res.obligs s := by
  simp [b_failure.res,Result.obligs,Oblig.all]
theorem b_failure_values (s : MachineState) (n : Nat) (hn : n < 2048)
    (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    (b_failure.res.toState s).getReg .x6=BitVec.ofNat 64 (n+1) ∧
    (b_failure.res.toState s).getReg .x7=BitVec.ofNat 64 ((n+1)/2048) ∧
    (b_failure.res.toState s).pc=(if (n+1)/2048=0 then pcOf 246503 else pcOf 246511) := by
  have hb : n+1<2^64 := by omega
  have hq : (n+1)/2048<2^64 := by omega
  have heq : BitVec.ofNat 64 ((n+1)/2048)=0#64 ↔ (n+1)/2048=0 := ofNat_inj hq (by decide)
  simp [Result.toState_getReg,Result.toState_pc,b_failure.res,RegFile.get,E.eval,BinOp.eval,CmpOp.eval,ha,
    ofNat_add_ofNat,ofNat_shr (n+1) 11 hb,heq]
theorem c_failure_obligs (s : MachineState) : c_failure.res.obligs s := by
  simp [c_failure.res,Result.obligs,Oblig.all]
theorem c_failure_values (s : MachineState) (n : Nat) (hn : n < 4096)
    (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    (c_failure.res.toState s).getReg .x6=BitVec.ofNat 64 (n+1) ∧
    (c_failure.res.toState s).getReg .x7=BitVec.ofNat 64 ((n+1)/4096) ∧
    (c_failure.res.toState s).pc=(if (n+1)/4096=0 then pcOf 235815 else pcOf 235827) := by
  have hb : n+1<2^64 := by omega
  have hq : (n+1)/4096<2^64 := by omega
  have heq : BitVec.ofNat 64 ((n+1)/4096)=0#64 ↔ (n+1)/4096=0 := ofNat_inj hq (by decide)
  simp [Result.toState_getReg,Result.toState_pc,c_failure.res,RegFile.get,E.eval,BinOp.eval,CmpOp.eval,ha,
    ofNat_add_ofNat,ofNat_shr (n+1) 12 hb,heq]
theorem b_failure_run {im : Image} (hc : CodeAt im (pcOf 246508) b_failureCode) (s : MachineState)
    (hp : s.pc=pcOf 246508) (n : Nat) (hn : n < 2048) (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x6,.x7] ∧
      t.getReg .x6=BitVec.ofNat 64 (n+1) ∧ t.getReg .x7=BitVec.ofNat 64 ((n+1)/2048) ∧
      t.pc=(if (n+1)/2048=0 then pcOf 246503 else pcOf 246511) ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨b_failure.res.toState s,symRun_sound b_failure hc s hp (b_failure_obligs s),?_,
    (b_failure_values s n hn ha).1,(b_failure_values s n hn ha).2.1,
    (b_failure_values s n hn ha).2.2,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro a;rfl

theorem b_last_value (s : MachineState) (ha : s.getReg .x6=2048#64) :
    (b_last.res.toState s).getReg .x6=2047#64 := by
  simp [Result.toState_getReg,b_last.res,RegFile.get,E.eval,BinOp.eval,ha]

theorem b_last_run {im : Image} (hc : CodeAt im (pcOf 246511) b_lastCode) (s : MachineState)
    (hp : s.pc=pcOf 246511) (ha : s.getReg .x6=2048#64) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 246512 ∧ RegsExcept s t [.x6] ∧
      t.getReg .x6=2047#64 ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨b_last.res.toState s,symRun_sound b_last hc s hp (by simp [b_last.res,Result.obligs,Oblig.all]),rfl,?_,
    b_last_value s ha,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro a;rfl

theorem c_failure_run {im : Image} (hc : CodeAt im (pcOf 235824) c_failureCode) (s : MachineState)
    (hp : s.pc=pcOf 235824) (n : Nat) (hn : n < 4096) (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x6,.x7] ∧
      t.getReg .x6=BitVec.ofNat 64 (n+1) ∧ t.getReg .x7=BitVec.ofNat 64 ((n+1)/4096) ∧
      t.pc=(if (n+1)/4096=0 then pcOf 235815 else pcOf 235827) ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨c_failure.res.toState s,symRun_sound c_failure hc s hp (c_failure_obligs s),?_,
    (c_failure_values s n hn ha).1,(c_failure_values s n hn ha).2.1,
    (c_failure_values s n hn ha).2.2,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro a;rfl

theorem c_last_value (s : MachineState) (ha : s.getReg .x6=4096#64) :
    (c_last.res.toState s).getReg .x6=4095#64 := by
  simp [Result.toState_getReg,c_last.res,RegFile.get,E.eval,BinOp.eval,ha]

theorem c_last_run {im : Image} (hc : CodeAt im (pcOf 235827) c_lastCode) (s : MachineState)
    (hp : s.pc=pcOf 235827) (ha : s.getReg .x6=4096#64) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 235828 ∧ RegsExcept s t [.x6] ∧
      t.getReg .x6=4095#64 ∧ (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨c_last.res.toState s,symRun_sound c_last hc s hp (by simp [c_last.res,Result.obligs,Oblig.all]),rfl,?_,
    c_last_value s ha,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro a;rfl

#print axioms b_failure_run
#print axioms c_last_run
#print axioms b_failure_values
#print axioms c_failure_values
end OuterNodeMachineCounter
