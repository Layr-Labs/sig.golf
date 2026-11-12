import SigGolfCandidate.OuterKeygenRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterKeygenValue
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M
open OuterImageValidity

theorem value (sk : SecretKey) :
    (fun r=>r.value) <$> sub.run .keygen sk=
      (fun p : SigGolfCandidate.T3.Digest×SigGolfCandidate.T3.Cache=>some ((p.1 : PublicKey),cacheB p.2)) <$>
      mrealize sk SigGolfCandidate.T3.keygen :=
  ClaudeWCT.W9.T3M.Final.value_of_counts (OuterKeygenRun.counts sk)
#print axioms value
end OuterKeygenValue
