import SigGolfCandidate.OuterSigningMoment
import SigGolfCandidate.OuterIndexBank
import SigGolfCandidate.OuterGlobalDigestFresh
import SigGolfCandidate.OuterEnvelope
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSigningBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (digestIndex digestIndex_lt digestAttemptLimit digestAttemptLimit_le)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow V_bind_bounded)
open SigGolfCandidate.Research
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.Numerics.CanonicalCompression SphincsSecurity.Completeness
open SigGolfCandidate.Research.SharedSigningBudget (digestMoment_ge_one groundE_ge_one ftsE_ge_one mG_ge_one)
open OuterSigningMoment (V_signFromOutput_certified)
noncomputable def digestMoment : ENNReal := (ftsBound:ENNReal)/scale
noncomputable def postMoment : ENNReal := signingZ^111993*(ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.groundE*
  (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.ftsE*(OuterSigningMoment.outerE*((OuterIndexMean.meanInitial:ENNReal)/scale))))
noncomputable def payloadMoment : ENNReal := signingZ^2*(digestMoment*postMoment)
noncomputable def signingMoment : ENNReal := signingZ^2*payloadMoment

theorem postMoment_ge_one : 1≤postMoment := by
  apply one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
  refine one_le_mul groundE_ge_one (one_le_mul ftsE_ge_one (one_le_mul ?_ ?_))
  · exact one_le_mul (one_le_pow₀ (mG_ge_one 5 (by decide) (by decide))) (one_le_pow₀ (mG_ge_one 4 (by decide) (by decide)))
  · apply (ENNReal.toReal_le_toReal (by simp) (by unfold scale;finiteness)).mp
    norm_num [ENNReal.toReal_div,OuterIndexMean.meanInitial,OuterGroundNumerics.mean74,ClaudeWCT.Numerics.LocalRoute.Tables.meanInitial,scale]

theorem payloadMoment_ge_one : 1≤payloadMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (one_le_mul digestMoment_ge_one postMoment_ge_one)

theorem V_signPayload_weighted (secret : BitVec 256) (z B : ENNReal) (hz : 1 ≤ z) (hB : 1 ≤ B)
    (score : HashOutput → ENNReal) (G : RCache → Prop)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hG : ∀ rho rc, G rc → ∀ counter, counter < 2^32 → ∀ answer,
      G (rc.cacheQuery (digestTrial rho message counter) answer))
    (hnonce : ∀ nonce ∈ support (roRun secret (privateNonce message) rcache),
      G nonce.2 ∧ ∀ c, c < 2^32 → nonce.2 (digestTrial nonce.1 message c) = none)
    (hnext : ∀ rho counter output rc, G rc →
      V secret z (OuterSigning.signFromOutput cache rho counter output) rc ≤ score output)
    (hstep : z * (acceptedWeight (DigestGeneric.decoder SharedForest.digestAccepted) score +
      failMass (DigestGeneric.decoder SharedForest.digestAccepted) * B) ≤ B) :
    V secret z (OuterSigning.signPayload cache message) rcache ≤ z^2 * B := by
  unfold OuterSigning.signPayload
  refine V_bind_bounded secret z _ _ rcache (z^2) B
    (V_of_bound (bound_privateNonce message) secret z hz rcache) ?_
  intro nonce hn
  obtain ⟨hg, hfresh⟩ := hnonce nonce hn
  rw [SharedForest.sharedDigestSearch_eq_run, DigestGeneric.run_public]
  apply V_search_bind secret z B (digestTrial nonce.1 message)
    (DigestGeneric.decoder SharedForest.digestAccepted)
    (fun c value => (BitVec.ofNat 32 c, value)) _ score G (2^32)
  · intro counter _
    exact digestTrial_length nonce.1 message counter
  · intro left right hl hr he
    exact digestTrial_injective nonce.1 message hl hr he
  · intro rc hrc counter hc answer
    exact hG nonce.1 rc hrc counter hc answer
  · intro rc _
    simpa only [V_pure] using hB
  · intro rc hrc counter hc answer value _
    refine (V_bind_bounded secret z _ _ _ (score value) 1
      (hnext nonce.1 (BitVec.ofNat 32 counter) value _ (hG nonce.1 rc hrc counter hc answer)) ?_).trans_eq (mul_one _)
    intro result _
    cases result.1 <;> simp only [V_pure, le_refl]
  · exact hstep
  · simp only [Nat.zero_add]
    exact digestAttemptLimit_le
  · exact hg
  · intro c _ hc
    exact hfresh c hc

theorem V_sign_fixed (secret : BitVec 256) (z P : ENNReal) (hz : 1 ≤ z) (hP : 1 ≤ P)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hpayload : ∀ checked ∈ support (roRun secret (privateMac cache.region) rcache),
      checked.1 = cache.tag → V secret z (OuterSigning.signPayload cache message) checked.2 ≤ P) :
    V secret z (OuterSigning.sign cache message) rcache ≤ z ^ 2 * P := by
  unfold OuterSigning.sign
  refine V_bind_bounded secret z _ _ rcache (z ^ 2) P
    (V_of_bound (bound_privateMac cache.region) secret z hz rcache) ?_
  intro checked hchecked
  split
  · simpa only [V_pure] using hP
  · rename_i h
    exact hpayload checked hchecked (by simpa only [ne_eq, not_not] using h)


theorem V_signPayload_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache)
    (hg : ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.AllGFresh rcache)
    (hf : OuterGlobalFresh.AllFFresh rcache) :
    V secret signingZ (OuterSigning.signPayload cache message) rcache ≤ payloadMoment := by
  let factor : ENNReal := signingZ^111993 *
    (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.groundE *
      (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.ftsE*OuterSigningMoment.outerE))
  let G : RCache → Prop := fun rc => RowsFreshFrom 0 rc ∧
    ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.AllGFresh rc ∧
    OuterGlobalFresh.AllFFresh rc
  have hB : 1 ≤ factor * OuterIndexBank.routeDigestBound := by
    have he : factor * OuterIndexBank.routeDigestBound = digestMoment * postMoment := by
      unfold factor OuterIndexBank.routeDigestBound digestMoment postMoment
      ring
    rw [he]
    exact one_le_mul digestMoment_ge_one postMoment_ge_one
  have h := V_signPayload_weighted secret signingZ
    (factor * OuterIndexBank.routeDigestBound) (SigGolfCandidate.Budget.one_le_zOf _) hB
    (fun a => factor * OuterIndexBank.routeInitial (ClaudeWCT.Bank.Paired.proposal a).1)
    G cache message rcache ?_ ?_ ?_ ?_
  · convert h using 1 <;> unfold payloadMoment digestMoment postMoment factor
    all_goals unfold OuterIndexBank.routeDigestBound; ring
  · intro rho rc hrc counter hc answer
    exact ⟨hrc.1.cacheQuery_digest rho message counter answer,
      hrc.2.1.cacheQuery_digest rho message counter answer,
      hrc.2.2.cacheQuery_digest rho message counter answer⟩
  · intro nonce hn
    have hnonce := privateNonce_preserves_fresh secret message rcache hfresh nonce hn
    exact ⟨⟨(fun lay _ => hnonce.2 lay lay.isLt),
      ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.privateNonce_allGFresh secret message rcache hg nonce hn,
      OuterGlobalFresh.privateNonce_allFFresh secret message rcache hf nonce hn⟩,
      fun c hc => hnonce.1 _ _ _ hc⟩
  · intro rho counter output rc hrc
    have hpoint := V_signFromOutput_certified secret cache rho counter output rc hrc.1 hrc.2.1 hrc.2.2
    convert hpoint using 1
    unfold factor OuterIndexBank.routeInitial
    rw [ClaudeWCT.Bank.Paired.proposal_index]
    rw [OuterIndexMean.index_initial_matches]
    simp only [OuterLayerMoment.initialValue]
    ring
  · exact scaled_step _ _ factor _ _ OuterIndexBank.routeDigest_step

theorem V_sign_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache)
    (hg : ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.AllGFresh rcache)
    (hf : OuterGlobalFresh.AllFFresh rcache) :
    V secret signingZ (OuterSigning.sign cache message) rcache ≤ signingMoment := by
  apply V_sign_fixed secret signingZ payloadMoment (SigGolfCandidate.Budget.one_le_zOf _)
    payloadMoment_ge_one cache message rcache
  intro checked hc _
  exact V_signPayload_certified secret cache message checked.2
    (privateMac_preserves_fresh secret cache.region rcache hfresh checked hc)
    (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.privateMac_allGFresh secret cache.region rcache hg checked hc)
    (OuterGlobalFresh.privateMac_allFFresh secret cache.region rcache hf checked hc)

theorem signingMoment_eq : signingMoment =
    signingZ^111997*(((ftsBound:ENNReal)/scale)*(ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.groundE*
      (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.ftsE*(OuterSigningMoment.outerE*((OuterIndexMean.meanInitial:ENNReal)/scale))))) := by
  unfold signingMoment payloadMoment digestMoment postMoment
  rw [show 111997=2+2+111993 by decide,pow_add,pow_add]
  ac_rfl


#print axioms V_sign_certified
#print axioms signingMoment_eq
end OuterSigningBudget
