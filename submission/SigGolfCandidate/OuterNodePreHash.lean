import SigGolfCandidate.OuterNodeRelocate
import SigGolfCandidate.OuterNodeMachineSave
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodePreHash
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks OuterNodeRelocate

theorem obligs (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) : b_preHash.res.obligs s := by
  simp [b_preHash.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,ha,ofNat_add_ofNat,
    memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES]
  omega

theorem value (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input) :
    (b_preHash.res.toState s).getMem (BitVec.ofNat 64 (input+32))=s.getReg .x6 := by
  simp [Result.toState_getMem,b_preHash.res,memEval_cons,Addr.eval,E.eval,ha,ofNat_add_ofNat]

theorem frame (s : MachineState) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (a : Word) (hne : a≠BitVec.ofNat 64 (input+32)) :
    (b_preHash.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [b_preHash.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  subst p
  simpa [Addr.eval,E.eval,ha,ofNat_add_ofNat] using hne

theorem runB {im : Image} (pc : Word) (hc : CodeAt im pc b_preHashCode) (s : MachineState)
    (hs : s.pc=pc) (input : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pc+4#64 ∧ RegsExcept s t [] ∧ fetch im t=some (.base .ECALL) ∧
      t.getMem (BitVec.ofNat 64 (input+32))=s.getReg .x6 ∧
      (∀ a,a≠BitVec.ofNat 64 (input+32)→t.getMem a=s.getMem a) := by
  let r : Result:={b_preHash.res with pc:=.c (pc+4#64)}
  refine ⟨r.toState s,symRun_sound (b_preHash_at pc) hc s hs (obligs s input ha hi hl hm),rfl,?_,
    symRun_ecall (b_preHash_at pc) hc s (obligs s input ha hi hl hm) (by rfl),value s input ha,frame s input ha⟩
  intro reg _
  cases reg <;> rfl

#print axioms runB
end OuterNodePreHash
