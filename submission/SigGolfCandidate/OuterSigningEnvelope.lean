import SigGolfCandidate.OuterSigningBudget
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSigningEnvelope
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Freshness
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh
open OuterSigningBudget

theorem signingMoment_le_two : signingMoment≤2 := by
  rw [signingMoment_eq]
  have hz:=ENNReal.toReal_mono (by unfold zDen;finiteness) signing_z_ratio
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hz
  have hmt : ∀ b,mG b≠⊤ := fun b => by unfold mG;exact ENNReal.ofReal_ne_top
  have hGt : groundE≠⊤ := by
    unfold groundE
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (hmt 1))
      (ENNReal.pow_ne_top (hmt 2))) (ENNReal.pow_ne_top (hmt 3))) (ENNReal.pow_ne_top (hmt 4))
  have hFt : ftsE≠⊤ := by unfold ftsE;exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (hmt 1)) (ENNReal.pow_ne_top (hmt 2))
  have hOt : OuterSigningMoment.outerE≠⊤ := by
    unfold OuterSigningMoment.outerE
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (hmt 5)) (ENNReal.pow_ne_top (hmt 4))
  have hzt : signingZ^111997≠⊤ := ENNReal.pow_ne_top (by unfold signingZ SigGolfCandidate.Budget.zOf;finiteness)
  have hst : ∀ n : Nat,(n:ENNReal)/(scale:ENNReal)≠⊤ := fun n =>
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) (by unfold scale;simp)
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hzt (ENNReal.mul_ne_top (hst _)
    (ENNReal.mul_ne_top hGt (ENNReal.mul_ne_top hFt (ENNReal.mul_ne_top hOt (hst _)))))) (by simp)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  have hfixed : signingZ.toReal^111997≤(OuterGroundNumerics.fixedBound:ℝ)/scale :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hz _).trans OuterEnvelope.fixed_ratio_bound
  have hmG : ∀ b,(mG b).toReal=(ClaudeWCT.Numerics.TopZero.groundM b:ℝ)/scale := fun b => by
    unfold mG;exact ENNReal.toReal_ofReal (by positivity)
  have hG : groundE.toReal*ftsE.toReal≤(ClaudeWCT.Numerics.TopZero.groundBound:ℝ)/scale := by
    unfold groundE ftsE
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,hmG]
    calc
      _ = ((ClaudeWCT.Numerics.TopZero.groundM 1:ℝ)/scale)^128*
          (((ClaudeWCT.Numerics.TopZero.groundM 2:ℝ)/scale)^80*
            (((ClaudeWCT.Numerics.TopZero.groundM 3:ℝ)/scale)^12*((ClaudeWCT.Numerics.TopZero.groundM 4:ℝ)/scale)^6)) := by ring
      _ ≤ _ := ClaudeWCT.Numerics.TopZero.groundBound_ratio_ge
  have hO : OuterSigningMoment.outerE.toReal≤(OuterGroundNumerics.outerBound:ℝ)/scale := by
    unfold OuterSigningMoment.outerE
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,hmG] using OuterEnvelope.outer_ratio_bound
  have nn (n : Nat) : (0:ℝ)≤(n:ℝ)/scale := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA:=mul_le_mul hfixed hG (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (nn _)
  have hB:=mul_le_mul_of_nonneg_right hA (nn ftsBound)
  have hC:=mul_le_mul hB hO ENNReal.toReal_nonneg (mul_nonneg (mul_nonneg (nn _) (nn _)) (nn _))
  have hD:=mul_le_mul_of_nonneg_right hC (nn OuterIndexMean.meanInitial)
  calc
    _ = signingZ.toReal^111997*(groundE.toReal*ftsE.toReal)*((ftsBound:ℝ)/scale)*
      OuterSigningMoment.outerE.toReal*((OuterIndexMean.meanInitial:ℝ)/scale) := by ring
    _ ≤ ((OuterGroundNumerics.fixedBound:ℝ)/scale)*((ClaudeWCT.Numerics.TopZero.groundBound:ℝ)/scale)*
      ((ftsBound:ℝ)/scale)*((OuterGroundNumerics.outerBound:ℝ)/scale)*((OuterIndexMean.meanInitial:ℝ)/scale) := hD
    _ ≤ 2 := OuterGroundNumerics.envelope_ratio_le_two

theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message) (rcache : RCache)
    (hs : AllSearchesFreshBC rcache) (hg : AllGFresh rcache) (hf : OuterGlobalFresh.AllFFresh rcache) :
    V secret signingZ (OuterSigning.sign cache message) rcache≤2 :=
  (V_sign_certified secret cache message rcache hs hg hf).trans signingMoment_le_two

def honestSignCount (message : Message) : M (Option SigGolfCandidate.Research.SharedForest.Signature × Nat) := do
  let keys←keygen
  countBlocks (OuterSigning.sign keys.2 message)

theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2:ENNReal)^((result.1.2:ℝ)/131072))≤2 := by
  rw [honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h:=V_sign_le_two secret keys.1.2 message keys.2
    (keygen_fresh_from_empty_bc secret keys hkeys) (keygen_allGFresh secret keys hkeys)
    (OuterGlobalFresh.keygen_allFFresh secret keys hkeys)
  simpa only [V,signingZ_pow] using h
#print axioms signingMoment_le_two
#print axioms honest_sign_exponential_budget
end OuterSigningEnvelope
