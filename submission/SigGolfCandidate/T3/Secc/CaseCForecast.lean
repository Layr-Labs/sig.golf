import SigGolfCandidate.T3.Secc.CaseCScore

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def admissibleSet : Finset HashOutput :=
  Finset.univ.filter fun x => digestAdmissible x = true
theorem acceptedWeight_eq_sum (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight Sampling.digestDecode w =
      (∑ x ∈ admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) := by
  have h : Sampling.acceptedWeight Sampling.digestDecode w =
      BPORS.finiteAverage (fun x => (Sampling.digestDecode x).elim 0 w) := by
    unfold Sampling.acceptedWeight
    exact BPORS.expected_uniform_eq_finiteAverage _
  have hsum : (∑ x, (Sampling.digestDecode x).elim 0 w) = ∑ x ∈ admissibleSet, w x := by
    unfold admissibleSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    unfold Sampling.digestDecode
    split <;> simp_all
  rw [h, BPORS.finiteAverage, hsum]
theorem acceptanceProbability_eq_card :
    acceptanceProbability = (admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal) := by
  have h := acceptedWeight_eq_sum (fun _ => 1)
  have h1 := Sampling.digest_acceptedWeight (fun _ => (1 : ENNReal))
  rw [BPORS.History.finiteAverage_constant, one_mul] at h1
  rw [← h1, h, Finset.sum_const, nsmul_eq_mul, mul_one]
theorem admissibleSet_nonempty : admissibleSet.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  apply Sampling.WeightedSelection.acceptanceProbability_ne_zero
  rw [acceptanceProbability_eq_card, h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
noncomputable def accepted : PMF HashOutput := PMF.uniformOfFinset admissibleSet admissibleSet_nonempty
noncomputable def forecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord accepted R) (fun F => score (X ++ F) N)
theorem finiteAverage_expectedValue {α β : Type} [Fintype β] (law : PMF α) (f : β → α → ENNReal) :
    BPORS.finiteAverage (fun b => expectedValue law (f b)) =
      expectedValue law (fun a => BPORS.finiteAverage (fun b => f b a)) := by
  unfold BPORS.finiteAverage expectedValue
  simp only [div_eq_mul_inv]
  calc
    (∑ b, ∑' a, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ =
        (∑' a, ∑ b, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = ∑' a, (∑ b, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ := ENNReal.tsum_mul_right.symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [← Finset.mul_sum, mul_assoc]
noncomputable def theta : ENNReal := 63 / 64
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  uniformWordAverage R (fun W => BPORS.History.fullPrice (labels X ++ W) - theta)
end SigGolfCandidate.T3.Security.CaseC
