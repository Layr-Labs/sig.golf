import SigGolfCandidate.OuterNodeMachineCCheck
import SigGolfCandidate.OuterNodeRelocate
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeCheckRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks OuterNodeRelocate

theorem runB {im : Image} (pc : Word) (hc : CodeAt im pc b_checkCode) (s : MachineState)
    (hp : s.pc=pc) (output : Nat) (ha : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : output<2^20) (hl : 2048≤output) (hm : output%8=0) :
    ∃ t,Steps im s 3 3 t ∧ RegsExcept s t [.x7] ∧
      t.pc=(if s.getMem (s.getReg .x12+24#64) >>> 61=0 then pc+28#64 else pc+12#64) ∧
      (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨(bCheckAt pc).toState s,symRun_sound (b_check_at pc) hc s hp
    (OuterNodeMachineCheck.b_check_obligs s output ha hi hl hm),?_,?_,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · simp [Result.toState_pc,bCheckAt,b_check.res,RegFile.get,E.eval,Addr.eval,BinOp.eval,CmpOp.eval]
  · intro a;rfl

theorem runC {im : Image} (pc : Word) (hc : CodeAt im pc c_checkCode) (s : MachineState)
    (hp : s.pc=pc) (input output heap : Nat)
    (ha : s.getReg .x10=BitVec.ofNat 64 input) (hb : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : input<2^20) (hil : 2048 ≤ input) (him : input%8=0)
    (ho : output<2^20) (hol : 2048≤output) (hom : output%8=0)
    (hh : heap=2 ∨ heap=3) (hmem : s.getMem (BitVec.ofNat 64 (input+24))=BitVec.ofNat 64 heap) :
    let off : Word:=if heap=3 then 8 else 24
    ∃ t,Steps im s 7 7 t ∧ RegsExcept s t [.x7] ∧
      t.pc=(if s.getMem (s.getReg .x12+off) >>> 60=0 then pc+44#64 else pc+28#64) ∧
      (∀ a,t.getMem a=s.getMem a) := by
  refine ⟨(cCheckAt pc).toState s,symRun_sound (c_check_at pc) hc s hp
    (OuterNodeMachineCCheck.obligs s input output heap ha hb hi hil him ho hol hom hh hmem),?_,?_,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · have he : s.getMem (s.getReg .x10+24#64)=BitVec.ofNat 64 heap := by
      simpa only [ha,ofNat_add_ofNat] using hmem
    rcases hh with rfl|rfl <;>
      simp [Result.toState_pc,cCheckAt,c_check.res,RegFile.get,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,he,
        OuterNodeMachineCCheck.sub16_add24]
  · intro a;rfl

#print axioms runB
#print axioms runC
end OuterNodeCheckRun
