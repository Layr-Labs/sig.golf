import SigGolfCandidate.OuterSignMachine
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace OuterSignBounds
open SigGolfCandidate.Legacy

theorem work_lt : OuterSignMachine.work+1<CYCLE_LIMIT := by decide +kernel
#print axioms work_lt
end OuterSignBounds
