import SigGolfCandidate.T3.Secc.LargeCouplingBankState

section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Frame
variable (U : Finset HashInput)
end Frame
section Invariant
variable {U : Finset HashInput}
end Invariant
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Step
variable {U : Finset HashInput}
theorem birth_pay (m q : Nat) (hm : m < q) (p : ENNReal) :
    p + (CaseC.theta + 1 / 64) / 2 ^ 128 + ((q - (m + 1) : Nat) : ENNReal) / 2 ^ 128 ≤
      p + ((q - m : Nat) : ENNReal) / 2 ^ 128 := by
  rw [add_assoc]
  apply add_le_add le_rfl
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  have hq : q - m = (q - (m + 1)) + 1 := by omega
  rw [hq, Nat.cast_add, Nat.cast_one, add_comm ((q - (m + 1) : Nat) : ENNReal)]
  exact add_le_add CaseC.theta_add_sixteenth_le_one le_rfl
end Step
end SigGolfCandidate.T3.Security.LargeCoupling
end
