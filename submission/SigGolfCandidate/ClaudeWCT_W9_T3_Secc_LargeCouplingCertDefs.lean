import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingInteraction
import SigGolfCandidate.T3_Secc_LargeCouplingCertDefs

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
end ClaudeWCT.W9.T3.Security.LargeCoupling

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold_fold : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def routerFold (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : RouterState :=
  verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published) LargeResidual.RouterState.initial)
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.LargeResidual (WCoord)

def CertGhost (st : LargeResidual.Paired.RouterState) : Prop :=
  st.exposures.length ≤ CaseC.horizon ∧
    (st.reused = true ∨ ∃ p ∈ st.births,
      ClaudeWCT.Bank.Paired.lawSpec.admissible p.2 = true ∧
      ClaudeWCT.Bank.Paired.Covered st.exposures p.2)

def CertOut {U : Finset HashInput}
    (r : Option (Option (Bool × LargeResidual.Paired.RouterState)) ×
      SigGolfCandidate.T3.Security.LargeResidual.State WCoord (Cell U)) : Prop :=
  ∃ st, r.1 = some (some (true, st)) ∧ CertGhost st
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord trialRows)
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold_certR : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CertR (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary rec generated tagged checked →
    checked.value = true ∧
    (monitorRun (Wots.PairedReference.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = false ∧
    (monitorRun (Wots.PairedReference.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).calls ≤ q ∧
    CertGhost (routerFold (Wots.PairedReference.referenceInputs adversary) A generated.value.2 tagged.steps checked.events)

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
