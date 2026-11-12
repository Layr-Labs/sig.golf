import SigGolfCandidate.TopRouteBank
import SigGolfCandidate.LocalRouteNumerics
set_option debug.skipKernelTC false
open scoped BigOperators
namespace ClaudeWCT.Bank.Paired.LocalRoute
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3
open ClaudeWCT.Numerics.LocalRoute.Tables
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
attribute [local irreducible] Finset.univ

noncomputable def routeInitial (i : Fin (2^31)) : ENNReal :=
  (indexInitial i.val : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.scale

theorem routeInitial_sum :
    (∑ i : Fin (2^31), routeInitial i) ≤
      ((2^31 : Nat) : ENNReal) * (meanInitial : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.scale := by
  simp only [routeInitial, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have h : (∑ i : Fin (2^31), (indexInitial i.val : ENNReal)) ≤
      ((2^31 : Nat) : ENNReal) * (meanInitial : ENNReal) := by
    exact_mod_cast ClaudeWCT.Numerics.LocalRoute.Tables.index_initial_sum
  exact mul_le_mul' h le_rfl

theorem routeInitial_average :
    (∑ p : Proposal, honestLaw p * routeInitial p.1) ≤
      (meanInitial : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.scale := by
  rw [honest_index_average]
  refine (mul_le_mul' le_rfl routeInitial_sum).trans_eq ?_
  rw [← mul_div_assoc, ← mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top _), one_mul]

theorem routeInitial_producer :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if producer a = true then routeInitial (proposal a).1 else 0) ≤
        ((meanInitial : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.scale) *
          ((ClaudeWCT.Numerics.CanonicalCompression.ftsNum : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.ftsDen) := by
  rw [acceptedProposalHonest (fun p => routeInitial p.1), producer_acceptance_exact]
  exact mul_le_mul' routeInitial_average le_rfl

theorem routeInitial_decoder :
    SigGolfCandidate.T3.Sampling.acceptedWeight
      (ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
      (fun a => routeInitial (proposal a).1) ≤
        ((meanInitial : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.scale) *
          ((ClaudeWCT.Numerics.CanonicalCompression.ftsNum : ENNReal) / ClaudeWCT.Numerics.CanonicalCompression.ftsDen) := by
  convert routeInitial_producer using 1
  unfold SigGolfCandidate.T3.Sampling.acceptedWeight
  congr 1
  funext a
  rw [producer_source]
  simp only [ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric.decoder]
  cases SigGolfCandidate.Research.SharedForest.digestAccepted a <;> rfl

open ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness

noncomputable def routeDigestBound : ENNReal :=
  ((ftsBound : ENNReal) / scale) * ((meanInitial : ENNReal) / scale)

theorem routeDigest_step : SigGolfCandidate.T3.Budgets.signingZ *
    (acceptedWeight (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted)
      (fun a => routeInitial (proposal a).1) +
      failMass (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted) * routeDigestBound) ≤ routeDigestBound := by
  have hfail : failMass (DigestGeneric.decoder SigGolfCandidate.Research.SharedForest.digestAccepted) =
      1 - (ftsNum : ENNReal) / ftsDen := by
    rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept,
      DigestGeneric.decoder_acceptance, digestAccepted_acceptance_exact]
  have hp : (ftsNum : ENNReal) / ftsDen ≤ 1 := by
    rw [← digestAccepted_acceptance_exact]
    exact probEvent_le_one
  have hd : 1 - (1 - (ftsNum : ENNReal) / ftsDen) = (ftsNum : ENNReal) / ftsDen :=
    ENNReal.sub_sub_cancel (by simp) hp
  have hs := (mul_le_mul' signing_z_ratio le_rfl).trans fts_ratio_step
  rw [hd] at hs
  rw [hfail]
  unfold routeDigestBound
  calc
    _ ≤ SigGolfCandidate.T3.Budgets.signingZ *
        (((meanInitial : ENNReal) / scale) * ((ftsNum : ENNReal) / ftsDen) +
          (1 - (ftsNum : ENNReal) / ftsDen) * (((ftsBound : ENNReal) / scale) * ((meanInitial : ENNReal) / scale))) :=
      mul_le_mul' le_rfl (add_le_add routeInitial_decoder le_rfl)
    _ = ((meanInitial : ENNReal) / scale) *
        (SigGolfCandidate.T3.Budgets.signingZ *
          ((1 - (ftsNum : ENNReal) / ftsDen) * ((ftsBound : ENNReal) / scale) + (ftsNum : ENNReal) / ftsDen)) := by ring
    _ ≤ ((meanInitial : ENNReal) / scale) * ((ftsBound : ENNReal) / scale) := mul_le_mul' le_rfl hs
    _ = _ := mul_comm _ _



end ClaudeWCT.Bank.Paired.LocalRoute
#print axioms ClaudeWCT.Bank.Paired.LocalRoute.routeDigest_step
