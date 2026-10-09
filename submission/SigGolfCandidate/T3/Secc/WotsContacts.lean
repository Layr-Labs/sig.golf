import SigGolfCandidate.T3.Secc.WotsTwoEdge

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
end SigGolfCandidate.T3.Security.Wots
