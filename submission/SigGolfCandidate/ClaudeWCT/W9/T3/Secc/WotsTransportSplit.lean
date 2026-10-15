import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportTable
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractVerify
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSplit

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem GameSplit.extends {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)}
    {interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
end ClaudeWCT.W9.T3.Security.Wots
