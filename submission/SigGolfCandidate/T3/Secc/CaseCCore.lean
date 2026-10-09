import SigGolfCandidate.T3.Secc.CaseCSearch
import SigGolfCandidate.T3.Secc.CaseCExcess
import SigGolfCandidate.T3.Secc.CaseCCover

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem pmf_expectedValue_left_mul {α : Type} (law : PMF α) (factor : ENNReal) (payoff : α → ENNReal) :
    expectedValue law (fun result => factor * payoff result) = factor * expectedValue law payoff := by
  unfold expectedValue
  simp_rw [mul_left_comm _ factor]
  exact ENNReal.tsum_mul_left
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => forecast R X N).sum + (slack : ENNReal) * excessForecast R X / 2 ^ 128
theorem expectedValue_list_sum' {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]
theorem theta_add_sixteenth_le_one : theta + 1 / 64 ≤ 1 := by
  unfold theta
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
noncomputable def admInd (a : HashOutput) : ENNReal := if digestAdmissible a = true then 1 else 0
def CoveredBy (X : List HashOutput) (N : HashOutput) : Prop :=
  ∀ f ∈ BPair.openedPositions N, ∃ out ∈ X, f ∈ BPair.openedPositions out
theorem expected_admInd_tight : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd ≤ 1/64 := by
  have he : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd=DigestSampling.acceptanceProbability := by
    rw [←Sampling.digest_acceptanceProbability,←expectedValue_ite_one]
    rfl
  rw [he]
  unfold DigestSampling.acceptanceProbability SigGolfResearch.Gate6.acceptance
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
structure BankCore where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  reuse : ENNReal
  slack : Nat
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if BPORS.Numeric.proposalLength < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger (BPORS.Numeric.proposalLength - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem expectedValue_add_const_le {α : Type} (p : ProbComp α) (f : α → ENNReal) (c : ENNReal) :
    expectedValue p (fun x => f x + c) ≤ expectedValue p f + c := by
  rw [expectedValue_add]
  exact add_le_add le_rfl (expectedValue_le_of_le p fun _ => le_rfl)
def BankCore.expose (b : BankCore) (C' : ENNReal) (o : Option HashOutput) : BankCore :=
  { b with exposures := b.exposures ++ o.toList, reuse := C' }
end SigGolfCandidate.T3.Security.CaseC
