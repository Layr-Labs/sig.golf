import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.T3.Secc.WotsExtractWord
import SigGolfCandidate.T3.Secc.CaseCSearch

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualRouter : DecidableEq T3.Cache := Classical.decEq _
inductive AuxQuery where
  | coin (n : Nat)
  | init
abbrev Cell (U : Finset HashInput) := {x // x ∈ U}
section Requests
variable (U : Finset HashInput)
end Requests
noncomputable def dummyDigest (lay : Layer) : Digest := Classical.choose (Wots.dummyDigits_valid lay)
section Route
variable (U : Finset HashInput)
end Route
end SigGolfCandidate.T3.Security.LargeResidual
