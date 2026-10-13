import SigGolfCandidate.T3.Secc.LargeCouplingBankSearch

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
noncomputable local instance instDecidableEqCache_largeCouplingBankSign : DecidableEq T3.Cache := Classical.decEq _
section Sign
variable {U : Finset HashInput}
variable (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem expectedValue_cell_univ (f : LargeResidual.Digest → ENNReal) :
    expectedValue (cell (Finset.univ : Finset LargeResidual.Digest)) f =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => f rho) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro rho
  have h1 : Pr[= rho | ($ᵗ Digest : ProbComp Digest)] = (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ :=
    probOutput_uniformSample _ rho
  have h2 : Pr[= rho | cell (Finset.univ : Finset LargeResidual.Digest)] =
      (Fintype.card LargeResidual.Digest : ENNReal)⁻¹ := by
    rw [cell, dif_pos Finset.univ_nonempty, SPMF.probOutput_eq_apply, SPMF.liftM_apply,
      PMF.uniformOfFinset_apply, if_pos (Finset.mem_univ _), Finset.card_univ]
  rw [h1, h2]
end Sign
end SigGolfCandidate.T3.Security.LargeCoupling
