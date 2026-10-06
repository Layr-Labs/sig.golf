import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots
import SigGolfCandidate.ClaudeWCT.W9.T3M.Submission
import SigGolfCandidate.T3M.Verify.HashOk
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SecurityP

section





section
namespace ClaudeWCT.W9.T3.LayerBudget
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Budgets (signingZ encodingRate encodingRate_bounds encoding_failMass signing_z_le
  EncodingFreshBelow SourceFreshness V_bind_bounded post_of_roRun)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow layerTrial V_layerCounterSearch bound_layerCounterSearch
  avoids_layerCounterSearch preserves_pairBelow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
structure Envelopes where
  b : Layer → ℚ
  ge_one : ∀ lay, 1 ≤ b lay
  step : ∀ lay, (SigGolfCandidate.T3.BaseAudit.zU : ℝ) * ((1 - encodingRate lay) * (b lay : ℝ) + encodingRate lay) ≤
    (b lay : ℝ)
namespace Envelopes
variable (E : Envelopes)
noncomputable def envelope (lay : Layer) : ENNReal := ENNReal.ofReal (E.b lay : ℝ)
theorem envelope_ge_one (lay : Layer) : 1 ≤ E.envelope lay := by
  rw [envelope, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast E.ge_one lay)
theorem moment_step (lay : Layer) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass (Sampling.encodingDecode lay) * E.envelope lay +
        (1 - failMass (Sampling.encodingDecode lay))) ≤ E.envelope lay := by
  have hp0 : 0 ≤ encodingRate lay := by linarith [(encodingRate_bounds lay).1]
  have hp1 : 0 ≤ 1 - encodingRate lay := by linarith [(encodingRate_bounds lay).2]
  have hb0 : 0 ≤ (E.b lay : ℝ) := by have := E.ge_one lay; exact_mod_cast (by linarith : (0 : ℚ) ≤ E.b lay)
  have hz0 : 0 ≤ (SigGolfCandidate.T3.BaseAudit.zU : ℝ) := by norm_num [SigGolfCandidate.T3.BaseAudit.zU]
  have hs : 1 - (1 - encodingRate lay) = encodingRate lay := by ring
  rw [encoding_failMass, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp1, hs, envelope]
  calc
    _ ≤ ENNReal.ofReal (SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1 - encodingRate lay) * ENNReal.ofReal (E.b lay : ℝ) +
        ENNReal.ofReal (encodingRate lay)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
        ((1 - encodingRate lay) * (E.b lay : ℝ) + encodingRate lay)) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (E.step lay)
noncomputable def layerMomentBound : Nat → ENNReal
  | 0 => 1
  | n + 1 => E.envelope (Fin.ofNat 4 n) *
      (if n = 0 then signingZ ^ (layerFixedCost 1) else
        signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP (Fin.ofNat 4 n)) * layerMomentBound n)
theorem layerMomentBound_ge_one : ∀ n, 1 ≤ E.layerMomentBound n := by
  intro n; induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [layerMomentBound]
      apply one_le_mul (E.envelope_ge_one _)
      split
      · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
      · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) ih
theorem V_layerCounterSearch_fresh (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) cache ≤ E.envelope lay :=
  V_layerCounterSearch secret _ _ (E.envelope_ge_one lay) lay tree leaf msg (E.moment_step lay) fuel counter
    hlimit cache hfresh
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem bound_topPart (cache : Cache) (leaf : Nat) (out : Option (BitVec 32 × List Nat))
    (hout : ∀ counter digits, out = some (counter, digits) →
      digits.length = chainCount (Fin.ofNat 4 0) ∧ digits.sum = target (Fin.ofNat 4 0) ∧
        ValidDigits (Fin.ofNat 4 0) digits) :
    ∃ post, SigGolfCandidate.T3.Cost.CBound post (layerFixedCost 1)
      (signTop cache leaf ((out.map Prod.snd).getD dummyTop)) := by
  first
  | (have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
        ((out.map Prod.snd).getD dummyTop).sum = 126 := by
       cases out with
       | none => exact ⟨by decide, by decide⟩
       | some pair =>
           obtain ⟨counter, digits⟩ := pair
           have hd := hout counter digits rfl
           exact ⟨hd.1, hd.2.1⟩
     exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩)
  | (have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
        ((out.map Prod.snd).getD dummyTop).sum ≤ 128 := by
       cases out with
       | none => exact ⟨by decide, by decide⟩
       | some pair =>
           obtain ⟨counter, digits⟩ := pair
           have hd := hout counter digits rfl
           exact ⟨hd.1, hd.2.1.trans_le (by decide)⟩
     exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩)
section Avoid
open SigGolfCandidate.T3.Freshness
variable (secret : BitVec 256) (target : HashInput) (ht : HasTag 4 target ∨ HasTag 12 target)
include ht
theorem avoids_packedLowerSecret (lay : Layer) (tree q : Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret ClaudeWCT.WCT9.lowerSeedPair
  split
  · exact avoids_bind (avoids_privatePair secret target ht 0 _ _ _ _ (by decide) (by decide))
      fun _ => avoids_pure _ _ _
  · exact avoids_pure _ _ _
theorem avoids_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state i => ?_) _)
    (fun state => avoids_bind (avoids_leafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _)
  refine avoids_bind (avoids_packedLowerSecret secret target ht _ _ _ _) fun sc => ?_
  rcases sc with ⟨seed, carry'⟩
  exact avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun value =>
    avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun _ => avoids_pure _ _ _
theorem avoids_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Avoids secret target (ClaudeWCT.WCT9.buildTreeP lay tree selected digits) := by
  unfold ClaudeWCT.WCT9.buildTreeP
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state leaf =>
      avoids_bind (avoids_buildLeafP secret target ht _ _ _ _ _) fun r => ?_) _)
    (fun state => avoids_bind (avoids_buildLevels secret target ht 3 _ _ _ _ (by decide) (by decide))
      fun _ => avoids_pure _ _ _)
  rcases r with ⟨⟨root, values⟩, carry⟩
  exact avoids_pure _ _ _
end Avoid
theorem V_signLayersBC (secret : BitVec 256) (cache : Cache) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg rcache, PairFreshBelow n rcache →
      V secret signingZ (ClaudeWCT.WCT9.signLayersBC cache index n msg) rcache ≤ E.layerMomentBound n := by
  intro n
  induction n with
  | zero =>
      intro _ msg rcache _
      simp only [ClaudeWCT.WCT9.signLayersBC, V_pure, layerMomentBound, le_refl]
  | succ n ih =>
      intro hn msg rcache hc
      have hnv : (Fin.ofNat 4 n).val = n := Nat.mod_eq_of_lt (by omega)
      have hs := E.V_layerCounterSearch_fresh secret (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
        counterLimit 0 (by decide) rcache
        (fun c _ hlim => hc.layerTrial _ (by rw [hnv]; omega) _ _ _ _ hlim)
      simp only [ClaudeWCT.WCT9.signLayersBC, layerMomentBound]
      refine V_bind_bounded secret signingZ _ _ rcache _ _ hs ?_
      intro result hr
      have hpost := post_of_roRun (bound_layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg counterLimit 0)
        secret rcache result hr
      have hnext : PairFreshBelow n result.2 := by
        intro other ho tree' leaf' left' right' c hlt
        have hne : Fin.ofNat 4 n ≠ other := by intro he; subst other; omega
        rw [SigGolfCandidate.T3.Freshness.preserves secret _ _ (avoids_layerCounterSearch secret hne
          (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit
          tree' leaf' left' right' c) rcache result hr]
        exact hc other (by omega) tree' leaf' left' right' c hlt
      by_cases hn0 : n = 0
      · subst n
        simp only [ite_true]
        obtain ⟨post, htop⟩ := bound_topPart cache (route index (Fin.ofNat 4 0)).1 result.1
          (fun counter digits hx => hpost counter digits hx)
        refine V_bind_bounded secret signingZ _ _ result.2 _ 1
          (V_of_bound htop secret signingZ (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_ |>.trans_eq (mul_one _)
        intro out _; rw [V_pure]
      · simp only [hn0, ite_false]
        cases hx : result.1 with
        | none =>
            simp only [hx, V_pure]
            exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (E.layerMomentBound_ge_one n)
        | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hpost counter digits hx
          simp only [hx]
          refine V_bind_bounded secret signingZ _ _ result.2 _ _
            (V_of_bound (ClaudeWCT.WCT9.Cost.bound_buildTreeP (Fin.ofNat 4 n) _ _ digits hd.2.2) secret signingZ
              (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_
          intro treeResult htree
          have ht : PairFreshBelow n treeResult.2 :=
            preserves_pairBelow secret _ (fun target htag =>
              avoids_buildTreeP secret target (Or.inl htag) _ _ _ digits)
              n result.2 hnext treeResult htree
          refine V_bind_bounded secret signingZ _ _ treeResult.2 _ 1
            (ih (by omega) _ _ ht) ?_ |>.trans_eq (mul_one _)
          intro previous _
          cases previous.1 <;> rw [V_pure]
theorem layerMomentBound_four :
    E.layerMomentBound 4 = signingZ ^ (ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
      E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 := by
  have h4 : ClaudeWCT.WCT9.Cost.layerFixedCostP 4 = ClaudeWCT.WCT9.Cost.treeCostP 3 +
      (ClaudeWCT.WCT9.Cost.treeCostP 2 + (ClaudeWCT.WCT9.Cost.treeCostP 1 + layerFixedCost 1)) := rfl
  change E.envelope 3 * (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 3) * (E.envelope 2 *
    (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 2) * (E.envelope 1 * (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 1) *
      (E.envelope 0 * signingZ ^ (layerFixedCost 1))))))) = _
  rw [h4, pow_add, pow_add, pow_add]
  ring
theorem envelope_prod :
    E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 =
      ENNReal.ofReal ((E.b 0 : ℝ) * (E.b 1 : ℝ) * (E.b 2 : ℝ) * (E.b 3 : ℝ)) := by
  have h0 : 0 ≤ (E.b 0 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 0] : (0 : ℚ) ≤ E.b 0)
  have h1 : 0 ≤ (E.b 1 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 1] : (0 : ℚ) ≤ E.b 1)
  have h2 : 0 ≤ (E.b 2 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 2] : (0 : ℚ) ≤ E.b 2)
  simp only [envelope]
  rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (mul_nonneg h0 h1),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h0 h1) h2)]
end Envelopes
open ClaudeWCT.W9.T3.BaseAudit in
noncomputable def Envelopes.v4 : Envelopes where
  b := ![V4.b1, V4.b2, V4.b3, V4.b4]
  ge_one := by intro lay; fin_cases lay <;> norm_num [V4.b1, V4.b2, V4.b3, V4.b4]
  step := by
    intro lay
    fin_cases lay <;> norm_num [encodingRate, EncodingCounting.acceptedCount, SigGolfCandidate.T3.BaseAudit.zU,
      V4.b1, V4.b2, V4.b3, V4.b4]
end ClaudeWCT.W9.T3.LayerBudget
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V V_pure V_of_bound)
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le V_bind_bounded post_of_roRun signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow AllSearchesFreshBC digestSearch_preserves_pairBelow
  privateMac_preserves_fresh privateNonce_preserves_fresh)
open SigGolfCandidate.T3.BaseAudit (zU)
open SigGolfCandidate.T3.Cost (bound_privateNonce bound_privateMac)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable abbrev layerEnvelopes : ClaudeWCT.W9.T3.LayerBudget.Envelopes :=
  ClaudeWCT.W9.T3.LayerBudget.Envelopes.v4
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.V4.b0 : ℝ)
theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.V4.b0]
theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V4.p0 : ℝ)) :
    failMass digestDecode = ENNReal.ofReal (1 - (BaseAudit.V4.p0 : ℝ)) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, haccept,
    ENNReal.ofReal_sub 1 (by norm_num [BaseAudit.V4.p0, BaseAudit.V4.J])]
  simp
theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V4.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (BaseAudit.V4.p0 : ℝ) := by norm_num [BaseAudit.V4.p0, BaseAudit.V4.J]
  have hp1 : 0 ≤ 1 - (BaseAudit.V4.p0 : ℝ) := by norm_num [BaseAudit.V4.p0, BaseAudit.V4.J]
  have hb0 : 0 ≤ (BaseAudit.V4.b0 : ℝ) := by norm_num [BaseAudit.V4.b0]
  have hz0 : 0 ≤ (zU : ℝ) := by norm_num [zU]
  have hs : 1 - (1 - (BaseAudit.V4.p0 : ℝ)) = (BaseAudit.V4.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1, hs, digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (zU : ℝ) *
      (ENNReal.ofReal (1 - (BaseAudit.V4.p0 : ℝ)) * ENNReal.ofReal (BaseAudit.V4.b0 : ℝ) +
        ENNReal.ofReal (BaseAudit.V4.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((zU : ℝ) *
        ((1 - (BaseAudit.V4.p0 : ℝ)) * (BaseAudit.V4.b0 : ℝ) + (BaseAudit.V4.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := BaseAudit.V4.step_0
      have h' : ((zU * ((1 - BaseAudit.V4.p0) * BaseAudit.V4.b0 + BaseAudit.V4.p0) : ℚ) : ℝ) ≤
          (BaseAudit.V4.b0 : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V4.p0 : ℝ)) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  ClaudeWCT.W9.T3.Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh
theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance digest_probability_eq_p0
theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    digest_probability_eq_p0
structure SourceFreshness (secret : BitVec 256) : Prop where
  forest : ∀ index output cache, PairFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (ClaudeWCT.WCT9.signForest index output) cache),
      PairFreshBelow 4 result.2
noncomputable def postDigestMomentFor (fts : ℕ) : ENNReal := signingZ ^ fts * layerEnvelopes.layerMomentBound 4
noncomputable def payloadMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * (digestEnvelope * postDigestMomentFor fts)
noncomputable def signingMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * payloadMomentFor fts
noncomputable def signingMoment : ENNReal := signingMomentFor BaseAudit.V4.ftsSign
theorem postDigestMomentFor_ge_one (fts : ℕ) : 1 ≤ postDigestMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerEnvelopes.layerMomentBound_ge_one 4)
theorem payloadMomentFor_ge_one (fts : ℕ) : 1 ≤ payloadMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestEnvelope_ge_one (postDigestMomentFor_ge_one fts))
theorem V_signPayload_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (signPayload cache message) rcache ≤ payloadMomentFor fts := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateNonce message) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro nonce hn
  have hnFresh := privateNonce_preserves_fresh secret message rcache hc nonce hn
  refine V_bind_bounded secret signingZ _ _ nonce.2 _ _
    (V_digestSearch_fresh secret nonce.1 message digestAttemptLimit 0
      (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega) nonce.2
      (fun c _ hlim => hnFresh.1 _ _ _ hlim)) ?_
  intro found hd
  have hdFresh := digestSearch_preserves_pairBelow secret nonce.1 message 0 digestAttemptLimit nonce.2 hnFresh
    found hd
  cases hx : found.1 with
  | none => simp only [V_pure]; exact postDigestMomentFor_ge_one fts
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      obtain ⟨post, hbound⟩ := hforest (output.toNat % 2 ^ 31) output
      refine V_bind_bounded secret signingZ _ _ found.2 _ _
        (V_of_bound hbound secret signingZ (SigGolfCandidate.Budget.one_le_zOf _) found.2) ?_
      intro forest hforestRun
      have hforestFresh := hf.forest _ _ found.2 hdFresh forest hforestRun
      refine V_bind_bounded secret signingZ _ _ forest.2 _ 1
        (layerEnvelopes.V_signLayersBC secret cache (output.toNat % 2 ^ 31) 4 (by decide)
          (.forest forest.1.2) forest.2 hforestFresh) ?_ |>.trans_eq (mul_one _)
      intro pieces _
      cases pieces.1 <;> rw [V_pure]
theorem V_sign_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ signingMomentFor fts := by
  show V secret signingZ (ClaudeWCT.WCT9.signWith digestAttemptLimit cache message) rcache ≤
    signingMomentFor fts
  unfold ClaudeWCT.WCT9.signWith
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateMac cache.region) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro result hr
  have hmac := privateMac_preserves_fresh secret cache.region rcache hc result hr
  split
  · rw [V_pure]; exact payloadMomentFor_ge_one fts
  · exact V_signPayload_of_freshness_for secret hf fts hforest cache message result.2 hmac
theorem signingMomentFor_eq (fts : ℕ) : signingMomentFor fts =
    signingZ ^ (4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
    (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
      layerEnvelopes.envelope 3) := by
  rw [signingMomentFor, payloadMomentFor, postDigestMomentFor, layerEnvelopes.layerMomentBound_four, pow_add,
    pow_add]
  ring
theorem signingMomentFor_mono {a b : ℕ} (h : a ≤ b) : signingMomentFor a ≤ signingMomentFor b := by
  have hz : signingZ ^ a ≤ signingZ ^ b := pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) h
  unfold signingMomentFor payloadMomentFor postDigestMomentFor
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hz le_rfl)))
theorem envelope_product_eq : digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
    layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3 =
    ENNReal.ofReal ((BaseAudit.V4.b0 : ℝ) * (BaseAudit.V4.b1 : ℝ) * (BaseAudit.V4.b2 : ℝ) *
      (BaseAudit.V4.b3 : ℝ) * (BaseAudit.V4.b4 : ℝ)) := by
  change ENNReal.ofReal (BaseAudit.V4.b0 : ℝ) * ENNReal.ofReal (BaseAudit.V4.b1 : ℝ) *
    ENNReal.ofReal (BaseAudit.V4.b2 : ℝ) * ENNReal.ofReal (BaseAudit.V4.b3 : ℝ) *
    ENNReal.ofReal (BaseAudit.V4.b4 : ℝ) = _
  rw [← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V4.b0 : ℝ) by norm_num [BaseAudit.V4.b0]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V4.b0 : ℝ) * (BaseAudit.V4.b1 : ℝ) by
      norm_num [BaseAudit.V4.b0, BaseAudit.V4.b1]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V4.b0 : ℝ) * (BaseAudit.V4.b1 : ℝ) * (BaseAudit.V4.b2 : ℝ) by
      norm_num [BaseAudit.V4.b0, BaseAudit.V4.b1, BaseAudit.V4.b2]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V4.b0 : ℝ) * (BaseAudit.V4.b1 : ℝ) * (BaseAudit.V4.b2 : ℝ) *
      (BaseAudit.V4.b3 : ℝ) by
      norm_num [BaseAudit.V4.b0, BaseAudit.V4.b1, BaseAudit.V4.b2, BaseAudit.V4.b3])]
theorem fixed_le_117467 {fts : ℕ} (h : fts ≤ 31667) : 4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4 ≤ 117467 := by
  have h1 := ClaudeWCT.WCT9.Cost.layerFixedCostP_four
  have h2 := SigGolfCandidate.T3.Cost.layerFixedCost_four
  omega
theorem signingMomentFor_le_two_of_le {fts : ℕ} (h : fts ≤ 31667) : signingMomentFor fts ≤ 2 := by
  rw [signingMomentFor_eq]
  calc signingZ ^ (4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
        (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
          layerEnvelopes.envelope 3)
      ≤ signingZ ^ 117467 * (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
          layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3) :=
        mul_le_mul' (pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) (fixed_le_117467 h)) le_rfl
    _ ≤ 2 := by
        rw [SigGolfCandidate.Budget.zOf_pow, envelope_product_eq]
        have hcast := ENNReal.ofReal_le_ofReal BaseAudit.V4.signing_envelope
        rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((117467 : ℝ) / 131072) by positivity)] at hcast
        norm_num only [ENNReal.ofReal_ofNat] at hcast
        convert hcast using 1
        norm_num
theorem signingMoment_le_two : signingMoment ≤ 2 :=
  signingMomentFor_le_two_of_le (by norm_num [BaseAudit.V4.ftsSign])
theorem V_sign_le_two_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) {fts : ℕ}
    (hfts : fts ≤ 31667)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness_for secret hf fts hforest cache message rcache hc).trans
    (signingMomentFor_le_two_of_le hfts)
theorem realized_sign_exponential_budget_of_freshness_for (secret : BitVec 256)
    (hf : SourceFreshness secret) {fts : ℕ} (hfts : fts ≤ 31667)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (SigGolfCandidate.T3.Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  have h := V_sign_le_two_of_freshness_for secret hf hfts hforest cache message rcache hc
  rw [SigGolfCandidate.T3.Sampling.V_realized] at h
  simp only [signingZ_pow] at h
  rw [StateT.run'_eq, expectedValue_map]
  exact h
end ClaudeWCT.W9.T3.Budgets
end
end

section




section
namespace ClaudeWCT.W9.T3.FullCacheExpansionCost
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge privatePair_cost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem shortHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (x : HashInput) :
    cost answers (shortHash x) = (pad64 x).length / 64 := by
  unfold shortHash
  rw [cost_bind, cost_pure, Nat.add_zero]
  unfold publicHash
  rw [cost_query]
  rfl
theorem pad64_length_ge (x : HashInput) (hx : 0 < x.length) : 64 ≤ (pad64 x).length := by
  simp only [pad64, List.length_append, List.length_replicate]
  omega
theorem leafHash_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (ends : List Digest) : 1 ≤ cost answers (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash
  rw [shortHash_cost]
  have hpos : 0 < (SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++
      SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.wctHeader 6 coord index 0 selected) ++
      (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)).length := by
    simp only [List.length_append, SphincsSecurity.bytesLE_length]
    omega
  have := pad64_length_ge _ hpos
  omega
theorem buildChild_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) (carry : Digest) :
    1 ≤ cost answers (ClaudeWCT.WCT9.buildChild index coord selected word carry) := by
  unfold ClaudeWCT.WCT9.buildChild
  rw [cost_bind, cost_bind]
  exact le_trans (leafHash_cost_ge answers index coord selected _)
    (le_trans (Nat.le_add_right _ _) (Nat.le_add_left _ _))
theorem buildCoordinate_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (coord : ClaudeWCT.WCT9.Coord) (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    128 ≤ cost answers (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  rw [cost_bind]
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (by simp) (foldlM_cost_ge answers _ 1 (fun state j => ?_) (List.range 128) _)
  rw [cost_bind]
  exact le_trans (buildChild_cost_ge answers index coord.val j word state.2.2) (Nat.le_add_right _ _)
theorem forestRows_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    1152 ≤ cost answers (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows
  apply (show 1152 = (List.finRange 9).length * 128 by decide).le.trans
  apply foldlM_cost_ge
  intro state coord
  unfold ClaudeWCT.WCT9.openingStep
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildCoordinate_cost_ge answers index coord _ _
theorem signForest_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    1152 ≤ cost answers (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest
  rw [cost_bind]
  exact (forestRows_cost_ge answers index output).trans (Nat.le_add_right _ _)
theorem signPayload_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) = some sig) :
    90 ≤ cost answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := signForest_cost_ge answers (output.toNat % 2 ^ 31) output
      omega
end ClaudeWCT.W9.T3.FullCacheExpansionCost
end
section
namespace ClaudeWCT.W9.T3.ExpansionBudget
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit assembledSignature honestForest
  signForest_root assembled_forest_recovery toT3Signature)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query cost_bound)
open SigGolfCandidate.T3.Correctness (Answers cacheRegion maskedTop PiecesAgree CacheTagCorrect
  keygen_correct keygen_cache_tag privateMac_count)
open SigGolfCandidate.T3.Cost (CBound GoodQuery Bound ValidDigits recoverLayerCost recoveryLayersCost
  leafHashCost bound_chain bound_leafHash bound_nodeHash bound_recoverLayer sum_finRange remaining_steps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerCost lay) (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + height lay) (fun ends hends => ?_) ?_
  · refine (bound_leafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind
        (fun top _ => .pure _ 0 trivial)).mono_k (by simp)
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerCost]
    omega
theorem expandLayersBC_cost_le (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg pieces,
      evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) = some pieces →
      ∀ sig : Signature, PiecesAgree (toT3Signature sig) pieces n →
        cost answers (ClaudeWCT.WCT9.expandLayersBC sig index n msg) ≤
          cost answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) + recoveryLayersCost n := by
  intro n
  induction n with
  | zero =>
      intro _ msg pieces _ sig _
      simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_pure, recoveryLayersCost]
      omega
  | succ n ih =>
      intro hn msg pieces he sig hagree
      have hsource := he
      simp only [ClaudeWCT.WCT9.signLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none =>
          by_cases hn0 : n = 0
          · subst n
            simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, cost_pure,
              if_true]
            omega
          · simp only [hs, hn0, if_false, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (ClaudeWCT.WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            counterLimit 0 counter digits (by decide) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hls := decode_length_sum hd
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            have hrec := cost_bound answers (bound_recoverLayer (toT3Signature sig) index (Fin.ofNat 4 0)
              digits hvalid hls.1 hls.2)
            simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, if_true,
              cost_pure, recoveryLayersCost, cost_bind, Nat.add_zero, Option.map_some, Option.getD_some]
            omega
          · have hrec := cost_bound answers (bound_recoverLayerPair sig index (Fin.ofNat 4 n)
              digits hvalid hls.1 hls.2)
            have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv := congrArg Fin.val h
              simp only [Fin.val_ofNat, Fin.val_zero] at hv
              omega
            simp only [hn0, if_false, evalWithAnswerFn_bind,
              ClaudeWCT.WCT9.eval_buildTreeP_result answers hlay _ _ digits hvalid (route_leaf_bound index _)] at he
            cases hp : evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n
              (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                  (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) with
            | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst pieces
                have hlen := ClaudeWCT.WCT9.signLayersBC_length answers cache index n _ previous hp
                change PiecesAgree (toT3Signature sig) (previous ++ [ClaudeWCT.WCT9.wotsPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n + 1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover : evalWithAnswerFn answers
                    (ClaudeWCT.WCT9.recoverLayerPair sig index (Fin.ofNat 4 n) digits) =
                    ClaudeWCT.WCT9.builtPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
                  apply ClaudeWCT.WCT9.eval_recoverLayerPair_honest answers sig index (Fin.ofNat 4 n) digits hvalid
                  · intro i
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).values i = _
                    rw [hlayer]
                    simp [piecesSignature, ClaudeWCT.WCT9.wotsPieces, SigGolfCandidate.T3.Correctness.treeValue]
                  · intro j
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).path j = _
                    rw [hlayer]
                    simp [piecesSignature, ClaudeWCT.WCT9.wotsPieces, SigGolfCandidate.T3.Correctness.treeValue]
                have hprevious := ih (by omega) _ previous hp sig (PiecesAgree.prefix hlen hagree)
                unfold ClaudeWCT.WCT9.builtPair at hrecover
                simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, hn0,
                  if_false, hrecover, hp, ClaudeWCT.WCT9.eval_buildTreeP_result answers hlay _ _ digits hvalid
                    (route_leaf_bound index _), recoveryLayersCost]
                cases hx : evalWithAnswerFn answers (ClaudeWCT.WCT9.expandLayersBC sig index n
                    (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                      (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                      (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                        (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) <;>
                  simp only [cost_pure, Nat.add_zero] <;> omega
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (expand message pk sig) =
      cost answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersBC sig (output.toNat % 2 ^ 31) 4
        (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output)))) := by
  simp only [ClaudeWCT.WCT9.Rev3.expand, ClaudeWCT.WCT9.expandWith, cost_bind, hd]
  split
  · split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
  · simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output) +
      cost answers (ClaudeWCT.WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4
        (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2)) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem expand_cost_le_payload_add_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers
    (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
      digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers
        (ClaudeWCT.WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4
          (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          have hforest := assembled_forest_recovery answers
            (evalWithAnswerFn answers (privateNonce message)) (output.toNat % 2 ^ 31) output pieces
          have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
          have hlayer := expandLayersBC_cost_le answers cache (output.toNat % 2 ^ 31)
            hcache hindex 4 (by decide) _ pieces hl
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1 pieces)
            (fun _ _ => rfl)
          obtain ⟨post, hrecBound⟩ := hrecFts
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            (output.toNat % 2 ^ 31) output
          have hrec := cost_bound answers hrecBound
          have hexpand := expand_cost_step answers message pk
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            counter output (by simpa only [ClaudeWCT.WCT9.assembledSignature_rho] using hd)
          rw [hexpand, signPayload_cost_step answers cache message counter output hd]
          simp only [ClaudeWCT.WCT9.assembledSignature_rho] at hrec hlayer ⊢
          rw [hforest]
          omega
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac, ← hvalid, ne_eq,
    not_true_eq_false, ite_false]
  rfl
theorem expand_cost_le_eight_sign_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) := by
  have hk := keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers keygen).2 message) =
      some sig := by
    rw [show sign (evalWithAnswerFn answers keygen).2 message =
      ClaudeWCT.WCT9.signWith digestAttemptLimit (evalWithAnswerFn answers keygen).2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers _ message
        (keygen_cache_tag answers)] at hs
    exact hs
  have h := expand_cost_le_payload_add_of ftsRec hrecFts hbudget answers (evalWithAnswerFn answers keygen).2
    message sig hk.2.1 hs' (evalWithAnswerFn answers keygen).1
  have hmin := ClaudeWCT.W9.T3.FullCacheExpansionCost.signPayload_cost_ge answers
    (evalWithAnswerFn answers keygen).2 message sig hs'
  rw [sign_cost_honest]
  omega
theorem recoverFts_budget : 131 + recoveryLayersCost 4 ≤ 622 := by
  have h := SigGolfCandidate.T3.Cost.recoveryLayersCost_four
  omega
theorem expand_cost_le_payload_add (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 :=
  expand_cost_le_payload_add_of 131
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers cache message sig hcache he pk
theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) :=
  expand_cost_le_eight_sign_of 131
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers message sig hs
end ClaudeWCT.W9.T3.ExpansionBudget
end
end

section













section
namespace ClaudeWCT.W9.T3.SourceReplay
open OracleComp OracleSpec
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM
  hashOnly_foldlM hashOnly_shortHash hashOnly_privatePair hashOnly_nodeHash fixedAnswers fixed_replay)
open ClaudeWCT.WCT9 (Signature Witness)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[aesop safe apply] theorem hashOnly_chain (index coord selected i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (index coord selected : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    HashOnly (ClaudeWCT.WCT9.forestPk index pairs) := by
  unfold ClaudeWCT.WCT9.forestPk; hashes
@[aesop safe apply] theorem hashOnly_ite' {α : Type} {c : Prop} [Decidable c] {p q : M α}
    (hp : HashOnly p) (hq : HashOnly q) : HashOnly (if c then p else q) := by
  split
  · exact hp
  · exact hq
@[aesop safe apply] theorem hashOnly_ftsSeedPair (index coord pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.ftsSeedPair index coord pair) := by
  unfold ClaudeWCT.WCT9.ftsSeedPair; exact hashOnly_privatePair _ _ _ _ _
@[aesop safe apply] theorem hashOnly_lowerSeedPair (lay : Layer) (tree pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.lowerSeedPair lay tree pair) := by
  unfold ClaudeWCT.WCT9.lowerSeedPair; exact hashOnly_privatePair _ _ _ _ _
theorem hashOnly_packedSecret (pairQuery : Nat → M (Digest × Digest)) (h : ∀ p, HashOnly (pairQuery p))
    (q : Nat) (carry : Digest) : HashOnly (ClaudeWCT.WCT9.packedSecret pairQuery q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret
  split
  · exact hashOnly_bind (h _) fun _ => hashOnly_pure _
  · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_packedSecret_fts (index coord q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.ftsSeedPair index coord) q carry) :=
  hashOnly_packedSecret _ (hashOnly_ftsSeedPair index coord) q carry
@[aesop safe apply] theorem hashOnly_packedSecret_lower (lay : Layer) (tree q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) :=
  hashOnly_packedSecret _ (hashOnly_lowerSeedPair lay tree) q carry
@[aesop safe apply] theorem hashOnly_buildChild (index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank)
    (carry : Digest) : HashOnly (ClaudeWCT.WCT9.buildChild index coord selected word carry) := by
  unfold ClaudeWCT.WCT9.buildChild
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_packedSecret_fts _ _ _ _) fun r => ?_
    rcases r with ⟨secret, carry'⟩
    exact hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hashOnly_leafHash _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctNodeHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctNodeHash coord index heap left right) := by
  unfold ClaudeWCT.WCT9.wctNodeHash; exact hashOnly_nodeHash _ _ _ _ _ _
@[aesop safe apply] theorem hashOnly_heapBuild (index coord : Nat) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.heapBuild index coord leaves) := by
  unfold ClaudeWCT.WCT9.heapBuild
  exact hashOnly_foldlM _ _ (fun nodes heap =>
    hashOnly_bind (hashOnly_wctNodeHash coord index heap _ _) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_buildCoordinate (index : Nat) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    HashOnly (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state j => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildChild index coord.val j word _) fun r => ?_
    rcases r with ⟨⟨root, values⟩, carry⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_heapBuild index coord.val state.1) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (carry : Digest) : HashOnly (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_packedSecret_lower _ _ _ _) fun r => ?_
    rcases r with ⟨seed, carry'⟩
    exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.buildTreeP lay tree selected digits) := by
  unfold ClaudeWCT.WCT9.buildTreeP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state leaf => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildLeafP lay tree leaf _ _) fun r => ?_
    rcases r with ⟨⟨root, values⟩, carry⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_buildLevels _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.digestSearch; hashes
@[aesop safe apply] theorem hashOnly_openingStep (index : Nat) (output : HashOutput)
    (state : List ClaudeWCT.WCT9.Opening × List (Digest × Digest)) (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.openingStep index output state coord) := by
  unfold ClaudeWCT.WCT9.openingStep; hashes
@[aesop safe apply] theorem hashOnly_forestRows (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows; hashes
@[aesop safe apply] theorem hashOnly_signForest (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest; hashes
@[aesop safe apply] theorem hashOnly_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput)
    (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.recoverCoordinate sig index output coord) := by
  unfold ClaudeWCT.WCT9.recoverCoordinate; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.recoverFts sig index output) := by
  unfold ClaudeWCT.WCT9.recoverFts; hashes
@[aesop safe apply] theorem hashOnly_layerCounterSearch (lay : Layer) (tree leaf : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
@[aesop safe apply] theorem hashOnly_signLayersBC (cache : Cache) (index n : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) :
    HashOnly (ClaudeWCT.WCT9.signLayersBC cache index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.signLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.signLayersBC; hashes
@[aesop safe apply] theorem hashOnly_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) : HashOnly (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair; hashes
@[aesop safe apply] theorem hashOnly_expandLayersBC (sig : Signature) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersBC sig index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
@[aesop safe apply] theorem hashOnly_verifyLayersBC (w : Witness) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.verifyLayersBC w index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
@[aesop safe apply] theorem hashOnly_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signPayloadWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signPayloadWith; hashes
@[aesop safe apply] theorem hashOnly_signWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signWith; hashes
@[aesop safe apply] theorem hashOnly_expandWith (limit : Nat) (message : Message) (pk : Digest)
    (sig : Signature) : HashOnly (ClaudeWCT.WCT9.expandWith limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandWith; hashes
@[aesop safe apply] theorem hashOnly_verifyWith (limit : Nat) (message : Message) (pk : Digest)
    (w : Witness) : HashOnly (ClaudeWCT.WCT9.verifyWith limit message pk w) := by
  unfold ClaudeWCT.WCT9.verifyWith; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.signPayload cache message) :=
  hashOnly_signPayloadWith _ cache message
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.sign cache message) :=
  hashOnly_signWith _ cache message
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.Rev3.expand message pk sig) :=
  hashOnly_expandWith _ message pk sig
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (ClaudeWCT.WCT9.Rev3.verify message pk w) :=
  hashOnly_verifyWith _ message pk w
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (cache : Cache) (message : Message) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.sign cache message)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.sign cache message)) :=
  fixed_replay secret hash _ (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (sig : Signature) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.expand message pk sig)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.expand message pk sig)) :=
  fixed_replay secret hash _ (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (w : Witness) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.verify message pk w)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.verify message pk w)) :=
  fixed_replay secret hash _ (hashOnly_verify message pk w)
end ClaudeWCT.W9.T3.SourceReplay
end
section
namespace ClaudeWCT.W9.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey
@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler
def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))
theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))
theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]
theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega
def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery
theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)
noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)
theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)
theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl
end ClaudeWCT.W9.T3.NonceSampling
end
section
namespace ClaudeWCT.W9.T3.Completeness
open OracleComp OracleSpec ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_foldlM hashOnly_keygen
  fixedAnswers fixed_replay)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand hashOnly_verify)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true
theorem honestProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceed answers) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.honest_signing_complete_of_searches answers hgood message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem honestProgram_true_for (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceedFor answers message) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.signing_complete_for_of_searches answers
    (evalWithAnswerFn answers keygen) (SigGolfCandidate.T3.Correctness.keygen_correct answers) message hgood
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact hashOnly_pure false
  | some sig =>
    apply hashOnly_bind (hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact hashOnly_pure false
    | some witness => exact hashOnly_verify message keys.1 witness
theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram := by
  apply hashOnly_foldlM
  intro accepted message
  exact hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _
theorem everyMessageProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hall : ∀ message, evalWithAnswerFn answers (honestProgram message) = true) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted) = accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hall, Bool.and_true]
      exact ih accepted
  exact hf _ true
theorem everyMessageProgram_true_of_complete (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hcomplete : Correctness.SigningComplete answers (evalWithAnswerFn answers keygen)) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  apply everyMessageProgram_true
  intro message
  obtain ⟨sig, witness, hs, he, hv⟩ := hcomplete message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  Presampling.tableSampler
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs, good outputs →
      Pr[fun value => value = false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)] = 0) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)
theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program) = (pure true : ProbComp Bool)) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)] = 0 :=
  SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret program _ hgood
theorem honest_prepared_failure_zero (secret : BitVec 256) (message : Message)
    (outputs : SearchKey → HashOutput) (hgood : Budgets.tableGoodFor message outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run'
        (Presampling.preparedCache outputs)] = 0 := by
  refine prepared_failure_zero secret (honestProgram message) outputs ?_
  intro hash hagree
  have hsrc : Correctness.SearchesSucceedFor (fixedAnswers secret hash) message := by
    apply Budgets.tableGoodFor_searchesSucceedFor message outputs _ hgood
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (Presampling.preparedCache_apply outputs key)
  exact (fixed_replay secret hash _ (hashOnly_honestProgram message)).trans
    (congrArg (pure : Bool → ProbComp Bool) (honestProgram_true_for _ message hsrc))
theorem honest_failure_small_of_acceptance (secret : BitVec 256) (message : Message)
    (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (ClaudeWCT.W9.T3.Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 321 := by
  exact (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans
    (Budgets.tableGoodFor_failure_small_of_acceptance message p hp hp1 haccept)
theorem honest_failure_small (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 321 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_small message)
theorem honest_failure_128 (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 128 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_128 message)
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler
theorem everyMessage_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : Budgets.tableGoodForNonces nonces outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run'
        (NonceSampling.preparedCache secret nonces outputs)] = 0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret everyMessageProgram _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : Budgets.NonceAgreement nonces (fixedAnswers secret hash) := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := Budgets.tableGoodForNonces_signingComplete nonces outputs
    (fixedAnswers secret hash) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_everyMessageProgram).trans
    (congrArg (pure : Bool → ProbComp Bool) (everyMessageProgram_true_of_complete _ hcomplete))
theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1 / (2 : ENNReal) ^ 193 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (NonceSampling.presample_source secret everyMessageProgram)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p := fun outputs => ¬Budgets.tableGoodForNonces nonces outputs)
    (fun outputs _ hgood => everyMessage_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans
    (Budgets.tableGoodForNonces_failure_small nonces)
theorem source_completeness (secret : BitVec 256) :
    1 - 1 / (2 : ENNReal) ^ 128 ≤
      Pr[= true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  have hsmall : 1 / (2 : ENNReal) ^ 193 ≤ 1 / (2 : ENNReal) ^ 128 := by norm_num
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero, tsub_zero]
  exact tsub_le_tsub_left (hf.trans hsmall) 1
end ClaudeWCT.W9.T3.Completeness
end
section
namespace ClaudeWCT.W9.T3.Freshness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery HasTag tagged_ne_search hasTag_privatePair)
open ClaudeWCT.WCT9 (FtsQuery FtsInput FtsSeed)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem avoidsQuery_of_fts (secret : BitVec 256) (target : HashInput)
    (ht : HasTag 4 target ∨ HasTag 12 target) (index : Nat) (q : Spec.Domain)
    (hq : FtsQuery index q) : avoidsQuery secret target q := by
  rcases q with (coin | input) | (tweak | other)
  · exact hq.elim
  · rcases ClaudeWCT.WCT9.FtsInput.hdrBlock (show FtsInput index input from hq) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨tag, lay, position, idx, htag, hblock⟩
    · intro he
      subst he
      rcases ht with ⟨l, tr, p, ix, hh⟩ | ⟨l, tr, p, ix, hh⟩
      · exact ClaudeWCT.WCT9.ftsChainHeaderP_ne_header index coord selected t step 0 4 l tr p ix
          (bytesLE_injective (hblock.symm.trans hh))
      · exact ClaudeWCT.WCT9.ftsChainHeaderP_ne_header index coord selected t step 0 12 l tr p ix
          (bytesLE_injective (hblock.symm.trans hh))
    · have hmod := ClaudeWCT.WCT9.Wots.tag_mod' htag
      exact tagged_ne_search (tag := tag) ⟨lay, index, position, idx, hblock⟩ ht hmod.2.2.1 hmod.2.2.2
  · obtain ⟨coord, pair, -, -, rfl⟩ := (show FtsSeed index tweak from hq)
    exact tagged_ne_search (tag := 8) (hasTag_privatePair secret 8 coord index 0 pair)
      ht (by decide) (by decide)
  · exact hq.elim
theorem avoids_signForest (secret : BitVec 256) (target : HashInput)
    (ht : HasTag 4 target ∨ HasTag 12 target) (index : Nat) (output : HashOutput) :
    Avoids secret target (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (ClaudeWCT.WCT9.signForest_queries index output)
    (fun q hq => avoidsQuery_of_fts secret target ht index q hq)
theorem sourceFreshness (secret : BitVec 256) : Budgets.SourceFreshness secret where
  forest := by
    intro index output cache hc result hr
    exact ClaudeWCT.W9.T3.PairRows.preserves_pairBelow secret _
      (fun target ht => avoids_signForest secret target (Or.inl ht) index output)
      4 cache hc result hr
end ClaudeWCT.W9.T3.Freshness
end
section
namespace ClaudeWCT.W9.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V)
open ClaudeWCT.W9.T3.Budgets (V_sign_of_freshness_for realized_sign_exponential_budget_of_freshness_for)
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (AllSearchesFreshBC)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem V_sign_le_signingMoment (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ ClaudeWCT.W9.T3.Budgets.signingMoment :=
  V_sign_of_freshness_for secret (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) _
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_le_signingMoment secret cache message rcache hc).trans ClaudeWCT.W9.T3.Budgets.signingMoment_le_two
theorem realized_sign_exponential_budget (secret : BitVec 256) (cache : Cache)
    (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 :=
  realized_sign_exponential_budget_of_freshness_for secret
    (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) (by norm_num)
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)
theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message) = (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount, Cost.realize_bind]
  congr 1
  funext keys
  exact Cost.realize_count secret _
theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2 := by
  rw [honestSignCount, SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two secret keys.1.2 message keys.2
    (ClaudeWCT.W9.T3.PairRows.keygen_fresh_from_empty_bc secret keys hkeys)
  simpa only [V, signingZ_pow] using h
theorem realized_honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue ((simulateQ SphincsSecurity.romImpl (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message)))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [← honestSignCount_realize secret message, StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
theorem uniform_message_sign_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestSignCount message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
end ClaudeWCT.W9.T3.BudgetClosure
end
section
namespace ClaudeWCT.W9.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem joint_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.1 : ℝ) / 131072)) ≤ 2 := by
  refine le_trans ?_ (ClaudeWCT.W9.T3.BudgetClosure.honest_sign_exponential_budget secret message)
  simp only [honestJointCounts, jointCounts, ClaudeWCT.W9.T3.BudgetClosure.honestSignCount,
    SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig, signCost⟩, rcache⟩
  cases sig with
  | none => simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
  | some sig =>
    simp only [SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
theorem joint_cost_le (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message) :
    (evalWithAnswerFn answers (honestJointCounts message)).2 ≤
      8 * (evalWithAnswerFn answers (honestJointCounts message)).1 := by
  exact eval_joint_cost_le (κ := Digest × Cache) (σ := Signature) (ω := Option Witness) answers keygen
    (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
    (ClaudeWCT.W9.T3.ExpansionBudget.expand_cost_le_eight_sign answers message)
theorem support_joint_cost_le (secret : BitVec 256) (message : Message)
    (result : (Nat × Nat) × RCache)
    (hr : result ∈ support (roRun secret (honestJointCounts message) ∅)) :
    result.1.2 ≤ 8 * result.1.1 := by
  obtain ⟨hash, _, heval⟩ := SigGolfCandidate.T3.CountedReplay.support_replay secret _
    (hashOnly_honestJointCounts message) ∅ result hr
  rw [heval]
  exact joint_cost_le _ message
theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  refine le_trans ?_ (joint_sign_exponential_budget secret message)
  apply expectedValue_mono_of_support
  intro result hr
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (result.1.2 : ℝ) ≤ 8 * (result.1.1 : ℝ) := by
    exact_mod_cast support_joint_cost_le secret message result hr
  linarith
theorem uniform_message_expand_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_expand_exponential_budget secret message
end ClaudeWCT.W9.T3.ExpansionClosure
end
section
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open ClaudeWCT.W9.T3M (Images submission)
def verifyCycleBound : Nat := 7439
def claimedC : Nat := 7529
def DigestCapOk (hash : Hash) (m : Message) (w : Bytes 22984) : Prop :=
  ∀ N, evalWithAnswerFn hash (mrealize 0 (digestP m w)) = some N → WCT9.capOk N = true
variable (I : Images)
def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .keygen sk =
    (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$> countBoth (mrealize sk keygen)
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  (submission I).runWith hash .keygen sk =
    ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
      cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 53919407, 995328, 1048576⟩
def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .sign (sk, cache, m) =
    (fun p => (p.1.map sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk, cache, m)).finished = true ∧
    ((submission I).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5456),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .expand (m, pk, s) =
    (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDec s)))
def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5456),
  ((submission I).runWith hash .expand (m, pk, s)).finished = true ∧
    ((submission I).runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 22984),
  (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22984),
  ((submission I).runWith hash .verify (m, pk, w)).finished = true ∧
    ((submission I).runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22984),
  SigGolfCandidate.T3M.Verify.HashOk hash → DigestCapOk hash m w →
  ((submission I).runWith hash .verify (m, pk, w)).value.isSome = true →
    ((submission I).runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound
structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1 - 1 / (2 : ℝ≥0∞) ^ 128 ≤
    Pr[= true | (simulateQ SphincsSecurity.romImpl
      (realize secret ClaudeWCT.W9.T3.Completeness.everyMessageProgram)).run' ∅]
def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2
def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (cache : Cache) (message : SigGolfCandidate.T3.Message),
    AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (sig : Signature),
    AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (w : Witness),
    AllQueriesSatisfy (verify message pk w) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final
end
end
