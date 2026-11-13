import SigGolfCandidate.OuterNodeMachineCounter
import SigGolfCandidate.OuterNodeRelocate
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeCounterRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks OuterNodeRelocate

theorem runB {im : Image} (pc : Word) (hc : CodeAt im pc b_failureCode) (s : MachineState)
    (hp : s.pc=pc) (n : Nat) (hn : n<4096) (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x6,.x7] ∧
      t.getReg .x6=BitVec.ofNat 64 (n+1) ∧
      t.pc=(if n+1<4096 then pc-20#64 else pc+12#64) ∧ (∀ a,t.getMem a=s.getMem a) := by
  have hb : n+1<2^64 := by omega
  have hq : (n+1)/4096<2^64 := by omega
  have he : BitVec.ofNat 64 ((n+1)/4096)=0#64 ↔ n+1<4096 := by
    rw [ofNat_inj hq (by decide)]
    omega
  refine ⟨(bFailureAt pc).toState s,symRun_sound (b_failure_at pc) hc s hp
    (OuterNodeMachineCounter.b_failure_obligs s),?_,?_,?_,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · exact (OuterNodeMachineCounter.b_failure_values s n hn ha).1
  · simp [Result.toState_pc,bFailureAt,b_failure.res,RegFile.get,E.eval,BinOp.eval,CmpOp.eval,ha,
      ofNat_add_ofNat,ofNat_shr (n+1) 12 hb,he]
  · intro a;rfl

theorem runC {im : Image} (pc : Word) (hc : CodeAt im pc c_failureCode) (s : MachineState)
    (hp : s.pc=pc) (n : Nat) (hn : n<4096) (ha : s.getReg .x6=BitVec.ofNat 64 n) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x6,.x7] ∧
      t.getReg .x6=BitVec.ofNat 64 (n+1) ∧
      t.pc=(if n+1<4096 then pc-36#64 else pc+12#64) ∧ (∀ a,t.getMem a=s.getMem a) := by
  have hb : n+1<2^64 := by omega
  have hq : (n+1)/4096<2^64 := by omega
  have he : BitVec.ofNat 64 ((n+1)/4096)=0#64 ↔ n+1<4096 := by
    rw [ofNat_inj hq (by decide)]
    omega
  refine ⟨(cFailureAt pc).toState s,symRun_sound (c_failure_at pc) hc s hp
    (OuterNodeMachineCounter.c_failure_obligs s),?_,?_,?_,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · exact (OuterNodeMachineCounter.c_failure_values s n hn ha).1
  · simp [Result.toState_pc,cFailureAt,c_failure.res,RegFile.get,E.eval,BinOp.eval,CmpOp.eval,ha,
      ofNat_add_ofNat,ofNat_shr (n+1) 12 hb,he]
  · intro a;rfl

#print axioms runB
#print axioms runC
end OuterNodeCounterRun
