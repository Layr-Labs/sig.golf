import SigGolfCandidate.OuterSigning
import SigGolfCandidate.OuterRootNumerics
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterLayerMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open ClaudeWCT.WCT9 CanonicalPolicy
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.CanonicalSearch.LocalRoute
open SphincsSecurity.Completeness
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
open ClaudeWCT.Numerics.LocalRoute
theorem V_layers (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z)
    (index : Nat)
    (E : ClaudeWCT.W9.T3.CanonicalSearch.LocalRoute.Envelope z (SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)
      (SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) (cache : SigGolfCandidate.T3.Cache)
    (prepared : PreparedRoots) (forest : PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache)
    (J : ENNReal) (hJ : 1 ≤ J)
    (hroot : z * (acceptedWeight (decoder 0 (Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index)))
      (fun dl => E.one (routeResidual index (OuterSigning.requiredCredit index) 0 dl.2 dl.1)) +
      SphincsSecurity.Completeness.failMass (decoder 0 (Policy75Safe23.threshold 0 (OuterSigning.requiredCredit index))) * J) ≤ J) :
    V secret z (OuterSigning.searchPreparedLayers cache index prepared forest) rcache ≤ z^168 * J := by
  have hfactor : 1 ≤ z^168 := one_le_pow₀ hz
  unfold OuterSigning.searchPreparedLayers
  simp only [CanonicalPolicy.totalCredit, Policy75Safe23.threshold_top]
  apply V_layerSearch_bind (secret := secret) (z := z) (lay := 0)
    (weight := fun dl => z^168 * E.one (routeResidual index (OuterSigning.requiredCredit index) 0 dl.2 dl.1))
  · intro rc _
    simpa only [V_pure] using one_le_mul hfactor hJ
  · intro rc hr counter hc answer dl0 hd0
    obtain ⟨ds0, l0⟩ := dl0
    have hd0' := decoder_spec hd0
    have hraw1 := Policy75Safe23.accepted_top_residual_pool (OuterSigning.requiredCredit index) hd0'
    have hres1 : routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0<58 := by unfold routeResidual;omega
    have hp1 : Policy75Safe23.threshold 1 (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) < 17 :=
      Policy75Safe23.lower_one_floor_lt ⟨routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0, hres1⟩
    simp only [show ¬ (Policy75Safe23.threshold 1 (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) ≥ 17) by omega, ↓reduceIte]
    apply V_layerSearch_bind (secret := secret) (z := z) (lay := 1)
      (weight := fun dl => z^168 * E.two (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 dl.2 dl.1))
    · intro rc _
      simpa only [V_pure] using one_le_mul hfactor (E.one_ge _ hres1)
    · intro rc hr counter1 hc1 answer1 dl1 hd1
      obtain ⟨ds1, l1⟩ := dl1
      have hd1' := decoder_spec hd1
      have hres2 : routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1 < 42 :=
        by
        have hraw2 := Policy75Safe23.accepted_one_residual ⟨routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0, hres1⟩ hd1'
        simp only [routeResidual] at hraw2 ⊢;omega
      have hp2 : Policy75Safe23.threshold 2 (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) ≤ 19 :=
        (Policy75Safe23.lower_two_progress ⟨routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1, hres2⟩).1
      simp only [show ¬ (Policy75Safe23.threshold 2 (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) ≥ 24) by omega,
        ↓reduceIte]
      apply V_layerSearch_bind (secret := secret) (z := z) (lay := 2)
        (weight := fun dl => z^168 * E.three
          (routeResidual index (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) 2 dl.2 dl.1))
      · intro rc _
        simpa only [V_pure] using one_le_mul hfactor (E.two_ge _ hres2)
      · intro rc hr counter2 hc2 answer2 dl2 hd2
        obtain ⟨ds2, l2⟩ := dl2
        have hd2' := decoder_spec hd2
        have hres3 : routeResidual index (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) 2 l2 ds2 < 24 :=
          by
          have hraw3 := Policy75Safe23.accepted_two_residual ⟨routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1, hres2⟩ hd2'
          simp only [routeResidual] at hraw3 ⊢;omega
        have hp3 := Policy75Safe23.lower_three_progress _ hres3
        have hp3' := Policy75Safe23.lowerThreeFloor_le _ hres3
        simp only [show ¬ (Policy75Safe23.threshold 3
            (routeResidual index (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) 2 l2 ds2) ≥ 24) by omega,
          ↓reduceIte]
        apply V_layerSearch_bind (secret := secret) (z := z) (lay := 3) (weight := fun _ => z^168)
        · intro rc _
          simpa only [V_pure] using one_le_mul hfactor (E.three_ge _ hres3)
        · intro rc hr counter3 hc3 answer3 dl3 hd3
          obtain ⟨ds3, l3⟩ := dl3
          have hd : SigGolfCandidate.T3.decode 0 (encodingAnswer 0 answer) = some ds0 :=
            (producerDecodeAt_spec hd0').1
          have hds := SigGolfCandidate.T3.decode_length_sum hd
          have hbound := bound_signTop_e1 cache (route index 0).1 ds0
            (by exact hds.1)
            (by exact hds.2.le)
          refine (V_bind_bounded secret z _ _ rc (z^168) 1
            (V_of_bound hbound secret z hz rc) ?_).trans_eq (mul_one _)
          intro top _
          simp only [V_pure]
          exact le_rfl
        · simpa only [mul_one] using scaled_step z
            (E.three (routeResidual index (routeResidual index (routeResidual index (OuterSigning.requiredCredit index) 0 l0 ds0) 1 l1 ds1) 2 l2 ds2))
            (z^168) _ (fun _ => 1) (E.three_step _ hres3)
        · decide
        · exact hr
      · exact scaled_step z _ (z^168) _ _ (E.two_step _ hres2)
      · decide
      · exact hr
    · exact scaled_step z _ (z^168) _ _ (E.one_step _ hres1)
    · decide
    · exact hr
  · exact scaled_step z _ (z^168) _ _ hroot
  · decide
  · exact hfresh

noncomputable def initialValue (pool s1 s2 s3 : Nat) : ENNReal :=
  (OuterRootNumerics.initialAt pool (4*s1+2*s2+s3) : ENNReal)/ClaudeWCT.Numerics.CanonicalCompression.scale

theorem root_step (pool s1 s2 s3 : Nat) (hlo : 72 ≤ pool) (hhi : pool ≤ 74)
    (hs1 : s1 ≤ 1) (hs2 : s2 ≤ 1) (hs3 : s3 ≤ 1) :
    1 ≤ initialValue pool s1 s2 s3 ∧
    ((ClaudeWCT.Numerics.CanonicalCompression.zNum : ENNReal)/ClaudeWCT.Numerics.CanonicalCompression.zDen) *
      (acceptedWeight (decoder 0 (max 18 (pool-57)))
        (fun dl => oneValue s2 s3 (CanonicalPolicy.nextResidual pool 0 dl.2 dl.1-s1)) +
       failMass (decoder 0 (max 18 (pool-57))) * initialValue pool s1 s2 s3)  ≤  initialValue pool s1 s2 s3 := by
  have hf : 18 ≤ max 18 (pool-57) := Nat.le_max_left _ _
  have h := decoder_recurrence 220 (decoder 0 (max 18 (pool-57))) (dcredit 0)
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram (max 18 (pool-57)) pool
    ClaudeWCT.Numerics.CanonicalCompression.topDen (Checks.row1 (4*s1+2*s2+s3))
    (OuterRootNumerics.initialAt pool (4*s1+2*s2+s3)) (by decide)
    (fun a dl hd => top_decoder_credit_lt (by omega) hd)
    (by decide +kernel) (selected_top_probability_floor _ hf)
    (OuterRootNumerics.root_check_at pool _ hlo hhi (by omega))
  have he : acceptedWeight (decoder 0 (max 18 (pool-57)))
      (fun dl => ((Checks.row1 (4*s1+2*s2+s3))[pool-dcredit 0 dl]?.getD 0 : ENNReal)/ClaudeWCT.Numerics.CanonicalCompression.scale) =
      acceptedWeight (decoder 0 (max 18 (pool-57)))
      (fun dl => oneValue s2 s3 (CanonicalPolicy.nextResidual pool 0 dl.2 dl.1-s1)) := by
    apply acceptedWeight_congr_on
    intro answer dl hd
    have hh := Policy75Safe23.accepted_top_residual_pool pool (decoder_spec hd)
    have hres : pool-dcredit 0 dl<58 := hh
    have hm : (4*s1+2*s2+s3)%4=2*s2+s3 := by omega
    have hdiv : (4*s1+2*s2+s3)/4=s1 := by omega
    rw [shift1 (4*s1+2*s2+s3) _ (by omega) hres,hm,hdiv]
    rfl
  rw [he] at h
  exact h
#print axioms root_step


theorem V_layers_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : SigGolfCandidate.Research.SharedForest.PreparedRoots)
    (forest : SigGolfCandidate.Research.SharedForest.PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (OuterSigning.searchPreparedLayers cache index prepared forest) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^168 * (initialValue (OuterSigning.requiredCredit index)
        (SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1)
        (SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2)
        (SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3)) := by
  let s1 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 1
  let s2 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 2
  let s3 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave index 3
  have hs1 : s1≤1 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_le_one _ _
  have hs2 : s2≤1 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_le_one _ _
  have hs3 : s3≤1 := SigGolfCandidate.Research.SharedForest.LocalRoute.ownSave_le_one _ _
  let E := (ClaudeWCT.W9.T3.CanonicalSearch.LocalRoute.envelope s2 s3 hs2 hs3).mono_z signing_z_ratio
  have hb := OuterSigning.requiredCredit_bounds index
  have hi := root_step (OuterSigning.requiredCredit index)
    s1 s2 s3 hb.1 hb.2 hs1 hs2 hs3
  apply V_layers secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.Budget.one_le_zOf _) index E cache prepared forest rcache hfresh _ hi.1
  simpa only [Policy75Safe23.threshold_top,E,ClaudeWCT.W9.T3.CanonicalSearch.LocalRoute.Envelope.mono_z,ClaudeWCT.W9.T3.CanonicalSearch.LocalRoute.envelope,
    SigGolfCandidate.Research.SharedForest.routeResidual,s1,s2,s3,Fin.val_zero,Nat.zero_add] using
    (mul_le_mul' signing_z_ratio le_rfl).trans hi.2

#print axioms V_layers_certified
end OuterLayerMoment
