import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_0 : (List.range' 0 64).all routineOK = true := by decide +kernel
theorem routineOK_64 : (List.range' 64 64).all routineOK = true := by decide +kernel
theorem routineOK_128 : (List.range' 128 64).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
