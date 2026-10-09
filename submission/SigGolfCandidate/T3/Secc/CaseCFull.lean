import SigGolfCandidate.T3.Secc.CaseCLinkSplit

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFull : DecidableEq T3.Cache := Classical.decEq _
theorem queried_notDigest_keygen (A : Correctness.Answers) (input : T3.Spec.Domain)
    (h : input ∈ SourceReplay.queried A keygen) : BPB.NotDigestQ input :=
  BPB.allQ_queried A BPB.NotDigestQ keygen keygen_notDigest input h
end SigGolfCandidate.T3.Security.CaseC
