import SigGolfCandidate.OuterSourceQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
namespace OuterNonMac
open OracleComp OracleSpec SigGolfCandidate.T3
open _root_.SiggolfT3Mac4.Source (NonMac)
theorem output (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (out : HashOutput) :
    AllQueriesSatisfy (OuterSigning.signFromOutput cache rho counter out) NonMac :=
  OuterSourceQueries.signFromOutput_allowed NonMac ClaudeWCT.W9.T3.Security.PairedOuter.tail_nonMac forest cache rho counter out
#print axioms output
end OuterNonMac
