import SigGolfCandidate.OuterNodeMachineCheck
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachineCCheck
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks

theorem sub16_add24 (x : Word) : x-16#64+24#64=x+8#64 := by
  rw [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem values_two (s : MachineState) (hh : s.getMem (s.getReg .x10+24#64)=2#64) :
    (c_check.res.toState s).getReg .x7=(s.getMem (s.getReg .x12+24#64) >>> 60) ∧
    (c_check.res.toState s).pc=(if s.getMem (s.getReg .x12+24#64) >>> 60=0 then pcOf 235828 else pcOf 235824) := by
  simp [Result.toState_getReg,Result.toState_pc,c_check.res,RegFile.get,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,hh]

theorem values_three (s : MachineState) (hh : s.getMem (s.getReg .x10+24#64)=3#64) :
    (c_check.res.toState s).getReg .x7=(s.getMem (s.getReg .x12+8#64) >>> 60) ∧
    (c_check.res.toState s).pc=(if s.getMem (s.getReg .x12+8#64) >>> 60=0 then pcOf 235828 else pcOf 235824) := by
  simp [Result.toState_getReg,Result.toState_pc,c_check.res,RegFile.get,E.eval,Addr.eval,BinOp.eval,CmpOp.eval,hh,sub16_add24]


theorem obligs (s : MachineState) (input output heap : Nat)
    (ha : s.getReg .x10=BitVec.ofNat 64 input) (hb : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : input < 2^20) (hil : 2048 ≤ input) (him : input % 8 = 0)
    (ho : output < 2^20) (hol : 2048 ≤ output) (hom : output % 8 = 0)
    (hh : heap=2 ∨ heap=3) (hmem : s.getMem (BitVec.ofNat 64 (input+24))=BitVec.ofNat 64 heap) :
    c_check.res.obligs s := by
  rcases hh with rfl|rfl
  all_goals
    simp [c_check.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,BinOp.eval,UnOp.eval,LoadKind.fromWord,
      ha,hb,ofNat_add_ofNat,hmem,sub16_add24,memAccessValid_iff,BitVec.toNat_ofNat,BitVec.toNat_sub,MEMORY_BYTES]
    omega


theorem values (s : MachineState) (heap : Nat) (hh : heap=2 ∨ heap=3)
    (hmem : s.getMem (s.getReg .x10+24#64)=BitVec.ofNat 64 heap) :
    let off : Word:=if heap=3 then 8 else 24
    (c_check.res.toState s).getReg .x7=(s.getMem (s.getReg .x12+off) >>> 60) ∧
    (c_check.res.toState s).pc=(if s.getMem (s.getReg .x12+off) >>> 60=0 then pcOf 235828 else pcOf 235824) := by
  rcases hh with rfl|rfl
  · simpa using values_two s hmem
  · simpa using values_three s hmem

theorem run {im : Image} (hc : CodeAt im (pcOf 235817) c_checkCode) (s : MachineState)
    (hp : s.pc=pcOf 235817) (input output heap : Nat)
    (ha : s.getReg .x10=BitVec.ofNat 64 input) (hb : s.getReg .x12=BitVec.ofNat 64 output)
    (hi : input < 2^20) (hil : 2048 ≤ input) (him : input % 8 = 0)
    (ho : output < 2^20) (hol : 2048 ≤ output) (hom : output % 8 = 0)
    (hh : heap=2 ∨ heap=3) (hmem : s.getMem (BitVec.ofNat 64 (input+24))=BitVec.ofNat 64 heap) :
    let off : Word:=if heap=3 then 8 else 24
    ∃ t,Steps im s 7 7 t ∧ RegsExcept s t [.x7] ∧
      t.getReg .x7=(s.getMem (s.getReg .x12+off) >>> 60) ∧
      t.pc=(if s.getMem (s.getReg .x12+off) >>> 60=0 then pcOf 235828 else pcOf 235824) ∧
      (∀ a,t.getMem a=s.getMem a) := by
  have hmem' : s.getMem (s.getReg .x10+24#64)=BitVec.ofNat 64 heap := by
    simpa only [ha,ofNat_add_ofNat] using hmem
  have hv:=values s heap hh hmem'
  refine ⟨c_check.res.toState s,symRun_sound c_check hc s hp (obligs s input output heap ha hb hi hil him ho hol hom hh hmem),?_,
    hv.1,hv.2,?_⟩
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro a;rfl

#print axioms run
#print axioms obligs
#print axioms values_two
#print axioms values_three
end OuterNodeMachineCCheck
