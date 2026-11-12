import SigGolfCandidate.OuterLooseSource
import SigGolfCandidate.OuterHashOnly
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OuterLooseHashOnly
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.SourceReplay

theorem signCompact (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (OuterLooseSource.signCompact cache message) := by
  unfold OuterLooseSource.signCompact
  apply hashOnly_map
  exact OuterHashOnly.sign cache message
#print axioms signCompact
end OuterLooseHashOnly
