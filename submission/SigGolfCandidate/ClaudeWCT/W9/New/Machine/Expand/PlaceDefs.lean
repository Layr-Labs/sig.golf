import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def sibOff (l : Nat) (d : Bool) : Nat := 64 * (6 - l) + (if d then 0 else 48)
end ClaudeWCT.W9.Machine.Expand
