import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_384 : (List.range' 384 64).all routineOK = true := by decide +kernel
theorem routineOK_448 : (List.range' 448 64).all routineOK = true := by decide +kernel
theorem routineOK_512 : (List.range' 512 51).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
