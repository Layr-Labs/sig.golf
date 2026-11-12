import SigGolfCandidate.OuterSignBlocks
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignImageLayout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open OuterSignBlocks SigGolfCandidate.FtsGrind

def code : List (BitVec 32) := saveCode++dispatchCode++b_startCode++b_preCode++b_checkCode++b_retryCode++
  b_exhaustCode++c_startCode++c_preCode++c_checkCode++c_retryCode++c_exhaustCode++cleanupCode

theorem length : code.length=51 := by decide +kernel

def At (im : Image) : Prop :=
  CodeAt im (pcOf 26156) saveCode ∧ CodeAt im (pcOf 26158) addrCode ∧
  CodeAt im (pcOf 26161) headerCode ∧ CodeAt im (pcOf 26167) heapCode ∧
  CodeAt im (pcOf 26170) coordCode ∧ CodeAt im (pcOf 26175) b_startCode ∧
  CodeAt im (pcOf 26177) b_preCode ∧ CodeAt im (pcOf 26179) b_checkCode ∧
  CodeAt im (pcOf 26182) b_retryCode ∧ CodeAt im (pcOf 26185) b_exhaustCode ∧
  CodeAt im (pcOf 26186) c_startCode ∧ CodeAt im (pcOf 26188) c_preCode ∧
  CodeAt im (pcOf 26190) c_checkCode ∧ CodeAt im (pcOf 26197) c_retryCode ∧
  CodeAt im (pcOf 26200) c_exhaustCode ∧ CodeAt im (pcOf 26201) cleanupCode ∧
  CodeAt im (pcOf 26204) doneCode

theorem slices {im : Image} (hc : CodeAt im (pcOf 26156) code) : At im := by
  refine ⟨codeAt_sub 0 hc (by decide) (by rfl),codeAt_sub 2 hc (by decide) (by rfl),
    codeAt_sub 5 hc (by decide) (by rfl),codeAt_sub 11 hc (by decide) (by rfl),
    codeAt_sub 14 hc (by decide) (by rfl),codeAt_sub 19 hc (by decide) (by rfl),
    codeAt_sub 21 hc (by decide) (by rfl),codeAt_sub 23 hc (by decide) (by rfl),
    codeAt_sub 26 hc (by decide) (by rfl),codeAt_sub 29 hc (by decide) (by rfl),
    codeAt_sub 30 hc (by decide) (by rfl),codeAt_sub 32 hc (by decide) (by rfl),
    codeAt_sub 34 hc (by decide) (by rfl),codeAt_sub 41 hc (by decide) (by rfl),
    codeAt_sub 44 hc (by decide) (by rfl),codeAt_sub 45 hc (by decide) (by rfl),
    codeAt_sub 48 hc (by decide) (by rfl)⟩

#print axioms slices
end OuterSignImageLayout
