import SigGolfCandidate.T3.Secc.LargeCouplingBankStep

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (a : AuxData) (rho : Digest) (m : Message)
theorem trial_ne {k c : Nat} (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) (hne : k ≠ c) :
    pad64 (digestInput rho m (BitVec.ofNat 32 k)) ≠ pad64 (digestInput rho m (BitVec.ofNat 32 c)) := by
  intro h
  obtain ⟨-, h2, -⟩ := BPB.digestInput_injective h
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hc] at this
  exact hne this
theorem reply_of_some {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} {u : LargeResidual.HashOutput}
    (h : rows row = some u) : reply rows row = pure u := by
  unfold reply; rw [h]
theorem reply_of_none {rows : ResidualTableCompletion.Cache (Cell U)} {row : Cell U} (h : rows row = none) :
    reply rows row = liftM (PMF.uniformOfFintype LargeResidual.HashOutput) := by
  unfold reply; rw [h]
theorem expectedValue_uniform_ro (f : LargeResidual.HashOutput → ENNReal) :
    expectedValue (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput) f =
      expectedValue ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _) (fun y => f y) := by
  simp only [expectedValue_def]
  apply tsum_congr
  intro y
  have h1 : Pr[= y | ($ᵗ (SphincsSecurity.HashSpec.Range (default : HashInput)) : ProbComp _)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := probOutput_uniformSample _ y
  have h2 : Pr[= y | (liftM (PMF.uniformOfFintype LargeResidual.HashOutput) : SPMF LargeResidual.HashOutput)] =
      (Fintype.card LargeResidual.HashOutput : ENNReal)⁻¹ := by
    rw [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  rw [h1, h2]
end Search
end SigGolfCandidate.T3.Security.LargeCoupling
