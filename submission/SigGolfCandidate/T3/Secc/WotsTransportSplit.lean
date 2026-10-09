import SigGolfCandidate.T3.Secc.WotsTransportTable
import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
end SigGolfCandidate.T3.Security.Wots
