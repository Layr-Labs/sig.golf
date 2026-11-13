import SigGolfCandidate.OuterNodeMachineSave
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachineCheck
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks

theorem b_check_obligs (s : MachineState) (output : Nat) (ha : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : output < 2^20) (hl : 2048 ≤ output) (hm : output % 8 = 0) : b_check.res.obligs s := by
  simp [b_check.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem b_check_values (s : MachineState) :
    (b_check.res.toState s).getReg .x7=(s.getMem (s.getReg .x12+24#64) >>> 59) ∧
    (b_check.res.toState s).pc=(if s.getMem (s.getReg .x12+24#64) >>> 59=0 then pcOf 246512 else pcOf 246508) := by
  simp [Result.toState_getReg,Result.toState_pc,b_check.res,RegFile.get,E.eval,Addr.eval,BinOp.eval,CmpOp.eval]

theorem b_check_run {im : Image} (hc : CodeAt im (pcOf 246505) b_checkCode) (s : MachineState)
    (hp : s.pc=pcOf 246505) (output : Nat) (ha : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : output < 2^20) (hl : 2048 ≤ output) (hm : output % 8 = 0) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x7] ∧
      t.getReg .x7=(s.getMem (s.getReg .x12+24#64) >>> 59) ∧
      t.pc=(if s.getMem (s.getReg .x12+24#64) >>> 59=0 then pcOf 246512 else pcOf 246508) ∧
      (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨b_check.res.toState s,symRun_sound b_check hc s hp (b_check_obligs s output ha hi hl hm),?_,
    (b_check_values s).1,(b_check_values s).2,?_⟩
  · intro r hr
    cases r <;> simp at hr <;> rfl
  · intro a;rfl

#print axioms b_check_run
end OuterNodeMachineCheck
