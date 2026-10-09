import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_192 : (List.range' 192 64).all routineOK = true := by decide +kernel
theorem routineOK_256 : (List.range' 256 64).all routineOK = true := by decide +kernel
theorem routineOK_320 : (List.range' 320 64).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
