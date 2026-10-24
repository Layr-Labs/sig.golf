import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamLift
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamRestart1
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafRef
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafView

/-! # Family restart, steps P5c-2/3: reference against the mixture, prefix views (r3-lean-seedfam)

Family port of the normalized part of `WotsLeafRef` (`testRun_map`, `errR_map`, `errAR_map`, `errAR_GD`, `ref_hyps`,
`errC_eq`, `ref_prob_eq_frozen`, `ref_le_mix`, `mix_le_ref`) and of the normalized `WotsLeafView`
(`view_prob_le`, `view_prob_ge`, `view_count_le`). A source chain `a` is charged to its family `famOf S a.key`
(coordinates `caOf S a`), the per-chain error `Core.errC` becomes `FamLift.errCF`. The leaf-independent parts
(`Core.reference_map_eq_frozen_of`, `LeafView.reference_prob_view`, `LeafView.mixLaw_seed`, `LeafView.runView_eq`)
are reused.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)

theorem testRun_mapF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (RawFam.revSetF S F R))
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
    (r : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) :
    FamCore.testRunF hU (fun T => out <$> GD T) aF p r =
      (fun x => (out x.1, x.2)) <$> FamCore.testRunF hU GD aF p r := by
  simp only [FamCore.testRunF, simulateQ_map, StateT.run_map]

theorem errR_mapF {S : FamScheme} {F : FamAddr} {a : ChainAddr} (R : Tables U) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (RawFam.revSetF S F R)) (q : ℕ) :
    FamCore.errRF hU (a := a) R (fun T => out <$> GD T) aF q = FamCore.errRF hU (a := a) R GD aF q := by
  unfold FamCore.errRF
  simp only [testRun_mapF, ClaudeWCT.W9.T3.Security.Wots.Leaf.amLen_map]

theorem errAR_mapF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (q : ℕ) (R : Tables U) :
    FamLift.errARF hU S ca haF (fun T => out <$> GD T) q R = FamLift.errARF hU S ca haF GD q R := by
  unfold FamLift.errARF
  split_ifs with hd1
  · rw [errR_mapF]
  · rfl

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

section Ref
variable (S : FamScheme) (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (out : Res → SeedResult)
  (hout : ∀ T, out <$> GD T = Core.GDseed adversary q T)

include ha hout in
theorem errAR_GDF (R : Tables (PairedReference.referenceInputs adversary)) :
    FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
        (FamLift.chainOf_caOf S a ha.2) GD q R =
      FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
        (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) q R := by
  rw [← errAR_mapF (referenceInputs_subset adversary) S (FamLift.caOf S a ha.2) (FamLift.chainOf_caOf S a ha.2)
    GD out q R]
  rw [show (fun T => out <$> GD T) = Core.GDseed adversary q from funext hout]

include ha hout in
/-- Query bound of the refined body, admissibility and tree bound of the family of a source chain. -/
theorem ref_hypsF (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) :
    (∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q) ∧ FamOkS S (FamSum.famOf S a.key) ∧
      (FamSum.famOf S a.key).tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits (FamSum.famOf S a.key).lay := by
  refine ⟨fun T => ?_, FamLift.famOk_of_source S hgrp ha.1, ha.1.1⟩
  have h := Core.GDseed_queryBound (adversary := adversary) q T
  rw [← hout T, OracleComp.isQueryBoundP_map_iff] at h
  exact h

include ha hout in
theorem errC_eqF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
          (FamLift.chainOf_caOf S a ha.2) GD q R = FamLift.errCF S adversary q a := by
  unfold FamLift.errCF
  rw [dif_pos ha]
  simp only [errAR_GDF S q ha GD out hout]

variable (E : RefSample → Prop)
  (F : (d : ℕ) → Tables (PairedReference.referenceInputs adversary) → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : Tables (PairedReference.referenceInputs adversary))
      (p : PDataF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (RawPrefix.restDepth a R))
      (K K' : Fin (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) → Digest),
    seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K =
        seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K' →
      F (RawPrefix.restDepth a R) (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay)
          (S.cnt (FamSum.famOf S a.key).lay) (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam)
          (FamSum.famOf S a.key) R (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) =
        F (RawPrefix.restDepth a R) (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay)
          (S.cnt (FamSum.famOf S a.key).lay) (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam)
          (FamSum.famOf S a.key) R (K', RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → GD T' = GD T)
  (hEF : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
      (res : Res × TObs (RawPrefix.restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD
          (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support →
      (E (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
          (out res.1)) ↔
        F (RawPrefix.restDepth a R) R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)))
  (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)

include ha hout hEF in
theorem ref_prob_eq_frozenF :
    Pr[E | PairedReference.referenceExperiment adversary q] =
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (Core.reference_map_eq_frozen_of q ha GD out hout E (fun R z => F (RawPrefix.restDepth a R) R z)
      (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h

include ha hout hF hF0 hG hEF hgrp C hws hb

/-- **Reference ≤ mixture + error** (every source chain, charged to its family). -/
theorem ref_le_mixF :
    Pr[E | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] +
        FamLift.errCF S adversary q a := by
  obtain ⟨hGq, hFok, htb⟩ := ref_hypsF S q ha GD out hout hgrp
  rw [ref_prob_eq_frozenF q ha GD out hout E F hEF, ← errC_eqF S q ha GD out hout]
  exact FamLift.frozen_le_mixF (referenceInputs_subset adversary) S hFok htb (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) GD hG q hGq C (hws _) (hb _) F hF hF0

/-- **Mixture ≤ reference + error** (every source chain, charged to its family). -/
theorem mix_le_refF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] ≤
      Pr[E | PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a := by
  obtain ⟨hGq, hFok, htb⟩ := ref_hypsF S q ha GD out hout hgrp
  rw [ref_prob_eq_frozenF q ha GD out hout E F hEF, ← errC_eqF S q ha GD out hout]
  exact FamLift.mix_le_frozenF (referenceInputs_subset adversary) S hFok htb (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) GD hG q hGq C (hws _) (hb _) F hF hF0
end Ref

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
open ClaudeWCT.W9.T3.Security.Wots.Leaf (prob_pmf_map prob_bind runViewD)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

section View
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs 0),
    ¬E (runViewD a 0 z))
include hgrp C hws hb ha hE0

/-- **Prefix view, reference ≤ mixture + error** (family charge). -/
theorem view_prob_leF :
    Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] +
        FamLift.errCF S adversary q a := by
  rw [LeafView.reference_prob_view q ha E]
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamLift.frozen_le_mixF (referenceInputs_subset adversary) S hFok ha.1.1 (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) (fun T T' h' => FamLift.GDseed_fam S hFok q T T' h') q
    (Core.GDseed_queryBound q) C (hws _) (hb _) (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl)
    (fun _ z => hE0 z)
  simpa only [LeafView.mixLaw_seed, ← LeafView.runView_eq, FamLift.errCF, dif_pos ha] using h

/-- **Prefix view, mixture ≤ reference + error** (family charge). -/
theorem view_prob_geF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] ≤
      Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  rw [LeafView.reference_prob_view q ha E]
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamLift.mix_le_frozenF (referenceInputs_subset adversary) S hFok ha.1.1 (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) (fun T T' h' => FamLift.GDseed_fam S hFok q T T' h') q
    (Core.GDseed_queryBound q) C (hws _) (hb _) (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl)
    (fun _ z => hE0 z)
  simpa only [LeafView.mixLaw_seed, ← LeafView.runView_eq, FamLift.errCF, dif_pos ha] using h
end View

/-- **Expected prefix counts, mixture ≤ reference + q · error** (family charge). -/
theorem view_count_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) +
        q * FamLift.errCF S adversary q a := by
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun r => (fun v : PrefixView => k < v.count) (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] :=
    fun R => ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (fun r => seedCost a R r.2.1) q
      (fun r hr => seedGame_real_cost (referenceInputs_subset adversary) adversary q a R r hr)
  have href : ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun s => (fun v : PrefixView => k < v.count) (sampleView a s) |
        PairedReference.referenceExperiment adversary q] :=
    ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (prefixCount a) q (fun s hs =>
      (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs))
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        ∑ k ∈ Finset.range q, Pr[fun r => k < (runView a R r).count |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
      = ∑ k ∈ Finset.range q, ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < (runView a R r).count |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range q, (Pr[fun s => k < (sampleView a s).count |
          PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact view_prob_geF S hgrp C hws hb q ha (fun v => k < v.count) (fun z h => by
          simp only [runViewD, ClaudeWCT.W9.T3.Security.Wots.Leaf.calls_prefixQuery_zero] at h
          omega)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
