import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
theorem traceInUniverse (adversary : AdversaryP) (q : Nat) : TraceInUniverse adversary q :=
  fun sample hs entry he => reference_trace_mem adversary q sample hs entry he
end SigGolfCandidate.T3.Security.Wots
