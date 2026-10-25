import SigGolfCandidate.T3M_Verify_Spec

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The relocated legacy table entry always takes the rejection exit. -/
def aliasRejectSpec (n : Nat) : Spec :=
  ⟨[(.x5,.c 1),(.x10,.c 1)],[],3431,true,n,[],none,n⟩

theorem alias_reject_check :
    specB [] [] [] (runAt [] [] 245834 []) (aliasRejectSpec 8) [] [] [] = true := by decide +kernel

theorem alias_reject (s : MachineState) (hp : s.pc = pcOf 245834) :
    ∃ t, Steps image s 8 8 t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  obtain ⟨t,ht⟩ := spec_run alias_reject_check s hp (by simp [KnownOK]) (by simp [aliasRejectSpec]) (by simp)
  exact ⟨t,ht.steps,ht.ecall rfl,ht.regs (.x5,.c 1) (by simp [aliasRejectSpec]),
    ht.regs (.x10,.c 1) (by simp [aliasRejectSpec])⟩

end SigGolfCandidate.T3M.Verify.Nonbinary
