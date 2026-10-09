import SigGolfCandidate.T3.Secc.SeccLaw

namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem prefixCount_eq_classCharge (cls : T3.Spec.Domain → Prop) (budget : Nat)
    (events : List FirstHit.QueryEvent) :
    prefixCount cls budget events = SeccLaw.classCharge cls budget events := by
  induction events generalizing budget with
  | nil => rfl
  | cons event rest ih => simp only [prefixCount, SeccLaw.classCharge, ih]
end SigGolfCandidate.T3.Security.CreationGame
