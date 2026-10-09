import SigGolfCandidate.T3.Secc.SeccSufPayload
import SigGolfCandidate.T3.Secc.SeccLaw

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufSigned : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree
end SigGolfCandidate.T3.Security.BPB
