import SigGolfCandidate.OuterNodeMachineCounter
import SigGolfCandidate.OuterNodeRelocate
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace OuterNodeLastRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks OuterNodeRelocate

theorem run {im : Image} (pc : Word) (hc : CodeAt im pc b_lastCode) (s : MachineState)
    (hp : s.pc=pc) (n : Nat) (hn : n+1<2^64) (ha : s.getReg .x6=BitVec.ofNat 64 (n+1)) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pc+4#64 ∧ RegsExcept s t [.x6] ∧
      t.getReg .x6=BitVec.ofNat 64 n ∧ (∀ a,t.getMem a=s.getMem a) := by
  let r : Result:={b_last.res with pc:=.c (pc+4#64)}
  refine ⟨r.toState s,symRun_sound (b_last_at pc) hc s hp (by simp [b_last.res,Result.obligs,Oblig.all]),
    rfl,?_,?_,?_⟩
  · intro reg hr;cases reg <;> simp at hr <;> rfl
  · change (b_last.res.toState s).getReg .x6=_
    simp only [Result.toState_getReg,b_last.res,RegFile.get,E.eval,BinOp.eval,ha]
    rw [show 18446744073709551615#64 = -1#64 from by decide, ←BitVec.sub_eq_add_neg]
    rw [←ofNat_add_ofNat]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · intro a;rfl

#print axioms run
end OuterNodeLastRun
