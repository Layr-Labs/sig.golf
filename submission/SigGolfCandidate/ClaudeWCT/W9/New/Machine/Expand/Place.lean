import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PlaceDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits

section
namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
