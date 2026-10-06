import SigGolfCandidate.W9Fin.V4.InlineFinalDriver
import SigGolfCandidate.W9Fin.V4.InlinePrefixExecution

namespace W9Fin.V4.Inline
/- Pure definitional assembly of the genuine native prefix execution.
   The source query and ccM/Obs representations coincide definitionally. -/
theorem prefixGood : PrefixGood W9Drv.GatePre := Prefix.prefixGood
#print axioms prefixGood
end W9Fin.V4.Inline
