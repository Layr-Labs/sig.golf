import SigGolfCandidate.OuterNodeMachineBlocks
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachineSave
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks

theorem b_save_obligs (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) : b_save.res.obligs s := by
  have hbig : input+40<2^64 := by omega
  simp [b_save.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hbig,MEMORY_BYTES]
  omega


theorem b_save_values (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) :
    (b_save.res.toState s).getMem 1152=s.getReg .x6 ∧
    (b_save.res.toState s).getMem 1160=s.getReg .x7 ∧
    (b_save.res.toState s).getMem (BitVec.ofNat 64 (input+40))=0 ∧
    (b_save.res.toState s).getReg .x6=0 := by
  have hbig : input+40<2^64 := by omega
  have hmod : (input+40)%18446744073709551616=input+40 := Nat.mod_eq_of_lt hbig
  have hne1 : 1152≠input+40 := by omega
  have hne2 : 1160≠input+40 := by omega
  simp [Result.toState_getMem,Result.toState_getReg,b_save.res,memEval_cons,memEval_nil,Addr.eval,E.eval,ha,
    ofNat_add_ofNat,ofNat_eq_iff,hmod,hne1,hne2,RegFile.get]

theorem c_save_obligs (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) : c_save.res.obligs s :=
  b_save_obligs s input ha hi hl hm


theorem b_save_frame (s : MachineState) (a : Word)
    (ha : a≠1152#64 ∧ a≠1160#64 ∧ a≠s.getReg .x10+40#64) :
    (b_save.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [b_save.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact ha.2.2
  · exact ha.2.1
  · exact ha.1

theorem b_save_run {im : Image} (hc : CodeAt im (pcOf 246499) b_saveCode) (s : MachineState)
    (hp : s.pc=pcOf 246499) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 246503 ∧ RegsExcept s t [.x6] ∧
      t.getMem 1152=s.getReg .x6 ∧ t.getMem 1160=s.getReg .x7 ∧
      t.getMem (BitVec.ofNat 64 (input+40))=0 ∧ t.getReg .x6=0 := by
  refine ⟨b_save.res.toState s,symRun_sound b_save hc s hp (b_save_obligs s input ha hi hl hm),rfl,?_,
    b_save_values s input ha hi hl⟩
  intro r hr
  cases r <;> simp at hr <;> rfl

#print axioms b_save_run
#print axioms b_save_frame
#print axioms b_save_obligs
#print axioms b_save_values
end OuterNodeMachineSave
