import SigGolfCandidate.OuterNodeMachineBlocks
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeRelocate
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks

theorem b_save_at (pc : Word) :
    symRun {noAlias:=true} b_saveCode pc 40=some {b_save.res with pc:=.c (pc+16#64)} := by
  change some {b_save.res with pc:=.c (pc+4#64+4#64+4#64+4#64)}=_
  simp only [BitVec.add_assoc]
  rfl


def bCheckAt (pc : Word) : Result := {b_check.res with pc := (E.ite .eq (b_check.res.st.regs.get .x7) (.c 0) (.c (pc+28#64)) (.c (pc+12#64)))}
theorem b_check_at (pc : Word) : symRun {noAlias:=true} b_checkCode pc 40=some (bCheckAt pc) := by
  change some {b_check.res with pc := (E.ite .eq (b_check.res.st.regs.get .x7) (.c 0) (.c (pc+4#64+4#64+20#64)) (.c (pc+4#64+4#64+4#64)))} = _
  simp only [bCheckAt,BitVec.add_assoc]
  rfl

def cCheckAt (pc : Word) : Result := {c_check.res with pc := (E.ite .eq (c_check.res.st.regs.get .x7) (.c 0) (.c (pc+44#64)) (.c (pc+28#64)))}
theorem c_check_at (pc : Word) : symRun {noAlias:=true} c_checkCode pc 40=some (cCheckAt pc) := by
  change some {c_check.res with pc := (E.ite .eq (c_check.res.st.regs.get .x7) (.c 0) (.c (pc+4#64+4#64+4#64+4#64+4#64+4#64+20#64)) (.c (pc+4#64+4#64+4#64+4#64+4#64+4#64+4#64)))} = _
  simp only [cCheckAt,BitVec.add_assoc]
  rfl

def bFailureAt (pc : Word) : Result := {b_failure.res with pc := (E.ite .eq (b_failure.res.st.regs.get .x7) (.c 0) (.c (pc-20#64)) (.c (pc+12#64)))}
theorem b_failure_at (pc : Word) : symRun {noAlias:=true} b_failureCode pc 40=some (bFailureAt pc) := by
  change some {b_failure.res with pc := (E.ite .eq (b_failure.res.st.regs.get .x7) (.c 0) (.c (pc+4#64+4#64+(-28#64))) (.c (pc+4#64+4#64+4#64)))} = _
  simp only [bFailureAt,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

def cFailureAt (pc : Word) : Result := {c_failure.res with pc := (E.ite .eq (c_failure.res.st.regs.get .x7) (.c 0) (.c (pc-36#64)) (.c (pc+12#64)))}
theorem c_failure_at (pc : Word) : symRun {noAlias:=true} c_failureCode pc 40=some (cFailureAt pc) := by
  change some {c_failure.res with pc := (E.ite .eq (c_failure.res.st.regs.get .x7) (.c 0) (.c (pc+4#64+4#64+(-44#64))) (.c (pc+4#64+4#64+4#64)))} = _
  simp only [cFailureAt,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem b_preHash_at (pc : Word) : symRun {noAlias:=true} b_preHashCode pc 40=
    some {b_preHash.res with pc := .c (pc+4#64)} := by rfl

theorem b_last_at (pc : Word) : symRun {noAlias:=true} b_lastCode pc 40=
    some {b_last.res with pc := .c (pc+4#64)} := by rfl

theorem c_preHash_at (pc : Word) : symRun {noAlias:=true} c_preHashCode pc 40=
    some {c_preHash.res with pc := .c (pc+4#64)} := by rfl

theorem c_last_at (pc : Word) : symRun {noAlias:=true} c_lastCode pc 40=
    some {c_last.res with pc := .c (pc+4#64)} := by rfl

#print axioms b_failure_at
#print axioms c_failure_at
#print axioms b_save_at
#print axioms b_check_at
#print axioms c_check_at
end OuterNodeRelocate
