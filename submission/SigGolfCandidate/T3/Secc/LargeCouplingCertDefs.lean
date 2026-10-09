import SigGolfCandidate.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.T3.Secc.CaseCCore

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def honestNonce (A : Answers) (m : Message) : Digest := evalWithAnswerFn A (privateNonce m)
end SigGolfCandidate.T3.Security.LargeCoupling
