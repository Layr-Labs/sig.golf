import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge020
import SigGolfCandidate.Merge021
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge097
import SigGolfCandidate.Merge105
import SigGolfCandidate.Merge107
import SigGolfCandidate.Merge108
import SigGolfCandidate.Merge109
import SigGolfCandidate.Merge110

-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafRef ====
section

/-! # Reference experiment against the `realRun` mixture, lower chains (campaign X1 stage B, step B3)

For a source chain `a` and an honest body `GD` refining the seed game (`out <$> GD T = GDseed T`), every
event of the reference experiment that is coupled (under the frozen seed) with a depth-uniform event of the
prefix-game run has the same probability as in the `realRun` mixture, up to the per-chain error `errC a`
(`ref_le_mix`, `mix_le_ref`). Every source chain (top leaves are families since campaign T8D). -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsLeafRef : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec Free amLen tinduction seedsR)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun fixedImpl)
open SphincsSecurity.QueryCap (recorded counted calls)
variable {adversary : AdversaryP}

theorem amLen_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : amLen (f <$> oa) = amLen oa := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih =>
      rw [map_bind, ClaudeWCT.Arith.SideChannel.amLen_coin, ClaudeWCT.Arith.SideChannel.amLen_coin]
      simp only [ih]
  | test p k ih =>
      rw [map_bind, ClaudeWCT.Arith.SideChannel.amLen_test, ClaudeWCT.Arith.SideChannel.amLen_test, ih]

theorem testRun_map {L : LeafAddr} {a : ChainAddr} {R : RefTables adversary} {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (revSet L R))
    (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) :
    testRun (fun T => out <$> GD T) aF p r = (fun x => (out x.1, x.2)) <$> testRun GD aF p r := by
  simp only [testRun, simulateQ_map, StateT.run_map]

theorem errR_map {L : LeafAddr} {a : ChainAddr} (R : RefTables adversary) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (revSet L R)) (q : ℕ) :
    errR (a := a) R (fun T => out <$> GD T) aF q = errR (a := a) R GD aF q := by
  unfold errR
  simp only [testRun_map, amLen_map]

theorem errAR_map {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (q : ℕ) (R : RefTables adversary) :
    errAR a hac (fun T => out <$> GD T) q R = errAR a hac GD q R := by
  unfold errAR
  split_ifs with hd1
  · rw [errR_map]
  · rfl

section Ref
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (out : Res → SeedResult)
  (hout : ∀ T, out <$> GD T = GDseed adversary q T)

include ha hout in
/-- The frozen mixture for a refined seed game. -/
theorem reference_map_eq_frozen_of {β : Type} (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (Res × TObs (restDepth a R)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R)) (res : Res × TObs (restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (gameD a (restDepth a R) R GD (evaluate x.1 (PrefixGame.ovSeed a R x.2))) (fun _ _ => none)).support →
      f (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) (out res.1)) =
        g R (evaluate x.1 (PrefixGame.ovSeed a R x.2), res)) :
    (referenceExperiment adversary q).map f =
      (restLaw adversary).bind (fun R => (frozenLaw a (restDepth a R) R GD).map (g R)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := SigGolfCandidate.T3.Security.Wots.height_le a.key.lay; omega)
    omega
  rw [reference_eq_bind, PMF.map_bind, restLaw_resample adversary a]
  apply congrArg (restLaw adversary).bind
  funext R
  unfold frozenLaw
  rw [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Hidden (restDepth a R))).bind
  funext x
  have hfix := PrefixGame.fixed_seedGame (adversary := adversary) q a htree hleaf R x
  have hgd : seedGame adversary q a R (evaluate x.1 (PrefixGame.ovSeed a R x.2)) =
      out <$> gameD a (restDepth a R) R GD (evaluate x.1 (PrefixGame.ovSeed a R x.2)) := by
    rw [seedGame_eq_gameD]
    unfold gameD
    rw [← simulateQ_map, hout]
  rw [hgd, simulateQ_map, PMF.monad_map_eq_map] at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp, PMF.map_comp]
  conv_rhs => rw [PMF.map_comp]
  exact SigGolfCandidate.T3.Security.Wots.PrefixGame.map_congr_support _ _ _ fun res hres => hfg R x res hres

include ha hout in
theorem errAR_GD (R : RefTables adversary) :
    errAR a ha.2 GD q R = errAR a ha.2 (GDseed adversary q) q R := by
  rw [← errAR_map ha.2 GD out q R]
  congr 1
  funext T
  exact hout T

include ha hout in
theorem ref_hyps :
    (∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q) ∧ a.key.leaf < 2 ^ 24 := by
  refine ⟨fun T => ?_, ?_⟩
  · have h := GDseed_queryBound (adversary := adversary) q T
    rw [← hout T, OracleComp.isQueryBoundP_map_iff] at h
    exact h
  · have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := SigGolfCandidate.T3.Security.Wots.height_le a.key.lay; omega)
    omega

include ha hout in
theorem errC_eq : ∑' R, restLaw adversary R * errAR a ha.2 GD q R = errC adversary q a := by
  unfold errC
  rw [dif_pos ha]
  simp only [errAR_GD q ha GD out hout]

variable (E : RefSample → Prop) (F : (d : ℕ) → RefTables adversary → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : RefTables adversary) (p : PData a.key (restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (restDepth a R) (ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (restDepth a R) (ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)
  (hG : ∀ T T', LeafCongr a.key T T' → GD T' = GD T)
  (hEF : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R)) (res : Res × TObs (restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (gameD a (restDepth a R) R GD (evaluate x.1 (PrefixGame.ovSeed a R x.2))) (fun _ _ => none)).support →
      (E (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) (out res.1)) ↔
        F (restDepth a R) R (evaluate x.1 (PrefixGame.ovSeed a R x.2), res)))
include ha hout hF hF0 hG hEF

theorem ref_prob_eq_frozen :
    Pr[E | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | frozenLaw a (restDepth a R) R GD] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (reference_map_eq_frozen_of q ha GD out hout E (fun R z => F (restDepth a R) R z)
      (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h

end Ref

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem testRun_map {L : LeafAddr} {a : ChainAddr} {R : Tables (PairedReference.referenceInputs adversary)} {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (revSet L R))
    (p : PData L (RawPrefix.restDepth a R)) (r : Fin (chainCount L.lay) → Digest) :
    testRun (referenceInputs_subset adversary) (fun T => out <$> GD T) aF p r = (fun x => (out x.1, x.2)) <$> testRun (referenceInputs_subset adversary) GD aF p r := by
  simp only [testRun, simulateQ_map, StateT.run_map]

theorem errR_map {L : LeafAddr} {a : ChainAddr} (R : Tables (PairedReference.referenceInputs adversary)) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (revSet L R)) (q : ℕ) :
    errR (referenceInputs_subset adversary) (a := a) R (fun T => out <$> GD T) aF q = errR (referenceInputs_subset adversary) (a := a) R GD aF q := by
  unfold errR
  simp only [testRun_map, amLen_map]

theorem errAR_map {a : ChainAddr} (hac : a.chain < chainCount a.key.lay) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (q : ℕ) (R : Tables (PairedReference.referenceInputs adversary)) :
    errAR (referenceInputs_subset adversary) a hac (fun T => out <$> GD T) q R = errAR (referenceInputs_subset adversary) a hac GD q R := by
  unfold errAR
  split_ifs with hd1
  · rw [errR_map]
  · rfl

section Ref
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (out : Res → SeedResult)
  (hout : ∀ T, out <$> GD T = GDseed adversary q T)

include ha hout in
/-- The frozen mixture for a refined seed game. -/
theorem reference_map_eq_frozen_of {β : Type} (f : RefSample → β)
    (g : (R : Tables (PairedReference.referenceInputs adversary)) → Digest × (Res × TObs (RawPrefix.restDepth a R)) → β)
    (hfg : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R)) (res : Res × TObs (RawPrefix.restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support →
      f (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (out res.1)) =
        g R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)) :
    (PairedReference.referenceExperiment adversary q).map f =
      (restLaw (PairedReference.referenceInputs adversary)).bind (fun R => (frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD).map (g R)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.tree_lt; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := SigGolfCandidate.T3.Security.Wots.height_le a.key.lay; omega)
    omega
  rw [reference_eq_normalized, PMF.map_bind, uniform_resample_prefix (referenceInputs_subset adversary) a]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (restLaw (PairedReference.referenceInputs adversary)).bind
  funext R
  unfold frozenLaw
  rw [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R))).bind
  funext x
  have hfix := fixed_seedGame (referenceInputs_subset adversary) q a ha.1 htree hleaf R x adversary
  have hgd : seedGame (referenceInputs_subset adversary) adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)) =
      out <$> gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD (evaluate x.1 (RawPrefix.ovSeed a R x.2)) := by
    rw [seedGame_eq_gameD]
    unfold gameD
    rw [← simulateQ_map, hout]
  rw [hgd, simulateQ_map, PMF.monad_map_eq_map] at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp, PMF.map_comp]
  conv_rhs => rw [PMF.map_comp]
  exact SigGolfCandidate.T3.Security.Wots.PrefixGame.map_congr_support _ _ _ fun res hres => hfg R x res hres

include ha hout in
theorem errAR_GD (R : Tables (PairedReference.referenceInputs adversary)) :
    errAR (referenceInputs_subset adversary) a ha.2 GD q R = errAR (referenceInputs_subset adversary) a ha.2 (GDseed adversary q) q R := by
  rw [← errAR_map ha.2 GD out q R]
  congr 1
  funext T
  exact hout T

include ha hout in
theorem ref_hyps :
    (∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q) ∧ a.key.leaf < 2 ^ 24 := by
  refine ⟨fun T => ?_, ?_⟩
  · have h := GDseed_queryBound (adversary := adversary) q T
    rw [← hout T, OracleComp.isQueryBoundP_map_iff] at h
    exact h
  · have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := SigGolfCandidate.T3.Security.Wots.height_le a.key.lay; omega)
    omega

include ha hout in
theorem errC_eq : ∑' R, restLaw (PairedReference.referenceInputs adversary) R * errAR (referenceInputs_subset adversary) a ha.2 GD q R = errC adversary q a := by
  unfold errC
  rw [dif_pos ha]
  simp only [errAR_GD q ha GD out hout]

variable (E : RefSample → Prop) (F : (d : ℕ) → Tables (PairedReference.referenceInputs adversary) → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (p : PData a.key (RawPrefix.restDepth a R)) (K K' : Fin (WCT9.famCount a.key.lay) → Digest),
    seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K' →
      F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K, progF p.1.1 p.1.2 K)) =
        F (RawPrefix.restDepth a R) (RawLeaf.ovL a.key R (K', progF p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)
  (hG : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → GD T' = GD T)
  (hEF : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R)) (res : Res × TObs (RawPrefix.restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support →
      (E (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (out res.1)) ↔
        F (RawPrefix.restDepth a R) R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)))
include ha hout hF hF0 hG hEF

theorem ref_prob_eq_frozen :
    Pr[E | PairedReference.referenceExperiment adversary q] =
      ∑' R, restLaw (PairedReference.referenceInputs adversary) R * Pr[F (RawPrefix.restDepth a R) R | frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (reference_map_eq_frozen_of q ha GD out hout E (fun R z => F (RawPrefix.restDepth a R) R z)
      (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h

end Ref

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafView ====
section

/-! # Prefix views of lower chains (campaign X1 stage B, step B3)

The prefix-view consumers (`ContactAt`, `TwoEdgeAt`, `prefixCount`) for lower source chains: the reference
experiment and the `realRun` mixture agree up to `errC a` (probabilities, `view_prob_le` / `view_prob_ge`), and the
expected prefix count of the mixture exceeds the reference one by at most `q · errC a` (`view_count_le`). -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsLeafView : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
variable {adversary : AdversaryP}

/-- The prefix view of a run at depth `d` (`runView` is the case `d = restDepth a R`). -/
noncomputable def runViewD (a : ChainAddr) (d : Nat) (r : Digest × (SeedResult × TObs d)) : PrefixView :=
  ⟨d, r.1, fun step value => if h : step < d then r.2.2 ⟨step, h⟩ value else none,
    calls (PrefixGame.PrefixQuery a d) r.2.1.2⟩

theorem runView_eq (a : ChainAddr) (R : RefTables adversary) (r : Digest × (SeedResult × TObs (restDepth a R))) :
    runView a R r = runViewD a (restDepth a R) r := rfl

theorem mixLaw_seed (q : ℕ) (a : ChainAddr) (R : RefTables adversary) :
    mixLaw a (restDepth a R) R (GDseed adversary q) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) := by
  have h : seedGame adversary q a R = gameD a (restDepth a R) R (GDseed adversary q) :=
    funext (seedGame_eq_gameD q a R)
  unfold mixLaw
  rw [h]

section View
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × TObs 0), ¬E (runViewD a 0 z))
include ha hE0

end View

/-! ### Expected counts by layers -/

theorem nat_eq_sum_lt (n m : ℕ) (h : n ≤ m) :
    (n : ℝ≥0∞) = ∑ k ∈ Finset.range m, (if k < n then 1 else 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [show (Finset.range m).filter (fun k => k < n) = Finset.range n by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega, Finset.card_range]

theorem expectation_layers {α : Type} (P : PMF α) (X : α → ℕ) (m : ℕ) (hX : ∀ s ∈ P.support, X s ≤ m) :
    ∑' s, P s * (X s : ℝ≥0∞) = ∑ k ∈ Finset.range m, Pr[fun s => k < X s | P] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun s => ?_
  by_cases hs : s ∈ P.support
  · rw [nat_eq_sum_lt (X s) m (hX s hs), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  · rw [(PMF.apply_eq_zero_iff P s).mpr hs]
    simp

theorem calls_prefixQuery_zero (a : ChainAddr) (qs : List RefWorld.Domain) :
    calls (PrefixGame.PrefixQuery a 0) qs = 0 := by
  unfold calls
  rw [List.countP_eq_zero]
  rintro x - hx
  simp only [decide_eq_true_eq] at hx
  obtain ⟨i, -, -⟩ := hx
  exact i.elim0

theorem prefixCount_le_length (a : ChainAddr) (s : RefSample) : prefixCount a s ≤ s.trace.length :=
  List.length_filter_le _ _

/-- Total seed-test error over the source chains. -/
noncomputable def errTot (adversary : AdversaryP) (q : ℕ) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errC adversary q a

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open Core
open ClaudeWCT.W9.T3.Security.Wots.Leaf (prob_pmf_map prob_bind)
set_option maxHeartbeats 100000
set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

theorem runView_eq (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs (RawPrefix.restDepth a R))) :
    runView a R r = ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R) r := rfl

theorem reference_map_view (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    (PairedReference.referenceExperiment adversary q).map (sampleView a) =
      (Core.restLaw (PairedReference.referenceInputs adversary)).bind (fun R =>
        (Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)).map
          (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R))) := by
  rw [reference_map_eq_frozen adversary q a ha (sampleView a) (fun R => ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R))
    (fun R x res hres => (sampleView_coupled adversary q a R ha.1 x res hres).trans (runView_eq a R _))]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  unfold Core.frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, Core.seedGame_eq_gameD]
  rfl

theorem reference_prob_view (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) (E : PrefixView → Prop) :
    Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] =
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun z => E (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a (RawPrefix.restDepth a R) z) |
          Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)] := by
  change Pr[E ∘ sampleView a | PairedReference.referenceExperiment adversary q] = _
  rw [← prob_pmf_map, reference_map_view q ha, prob_bind]
  simp only [prob_pmf_map, Function.comp_def]

theorem mixLaw_seed (q : ℕ) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) := by
  have h : seedGame (referenceInputs_subset adversary) adversary q a R =
      Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q) :=
    funext (Core.seedGame_eq_gameD q a R)
  unfold Core.mixLaw
  rw [h]

section View
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs 0), ¬E (ClaudeWCT.W9.T3.Security.Wots.Leaf.runViewD a 0 z))
include ha hE0

end View

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open Core
open ClaudeWCT.W9.T3.Security.Wots.Leaf (runViewD)
set_option maxHeartbeats 100000
set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

theorem prefixCount_le_length (a : ChainAddr) (s : RefSample) : prefixCount a s ≤ s.trace.length :=
  List.length_filter_le _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.LeafView
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsTwoEdge ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain a ∧ PrefixRowAt answers a input
  | _ => False
noncomputable def prefixClassCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRow s.answers (.inl (.inr e.1)))).length
theorem prefixRowAt_unique {answers : Answers} {a b : ChainAddr} (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) {input : HashInput} (hia : PrefixRowAt answers a input)
    (hib : PrefixRowAt answers b input) : a = b := by
  obtain ⟨s, v, hs, rfl⟩ := hia
  obtain ⟨s', v', hs', he⟩ := hib
  have h7a := Mask.depth_le_seven answers a
  have h7b := Mask.depth_le_seven answers b
  have hca : a.chain < 2 ^ 24 := by have := ha.2; have := Mask.chainCount_le a.key.lay; omega
  have hcb : b.chain < 2 ^ 24 := by have := hb.2; have := Mask.chainCount_le b.key.lay; omega
  have h := chainInputW_eq_chainRowW (a := b) hca hcb (by omega) (by omega) ((chainRowW_eq a s v).symm.trans he)
  have hkey := h.1.eq_of_lt (by have := ha.1.1; omega)
    (by have := ha.1.2; have : 2 ^ height a.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega); omega)
    (by have := hb.1.1; omega)
    (by have := hb.1.2; have : 2 ^ height b.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le b.key.lay; omega); omega)
  cases a; cases b
  simp only at hkey h ⊢
  rw [h.2.1, ← hkey]
theorem prefixCount_sum_le (s : RefSample) :
    ∑ a ∈ sourceChains, prefixCount a s ≤ prefixClassCount s := by
  unfold prefixCount prefixClassCount
  simp only [← List.countP_eq_length_filter]
  have h := SphincsSecurity.QueryCap.calls_sum_le sourceChains
    (fun a (e : Entry) => PrefixRowAt s.answers a e.1) (fun e => PrefixRow s.answers (.inl (.inr e.1)))
    ?_ s.trace
  · simpa only [SphincsSecurity.QueryCap.calls] using h
  · intro e
    by_cases hP : PrefixRow s.answers (.inl (.inr e.1))
    · rw [if_pos hP]
      obtain ⟨b, hb, hbe⟩ := hP
      rw [Finset.sum_eq_single b]
      · rw [if_pos hbe]
      · intro a ha hab
        rw [if_neg]
        intro hae
        exact hab (prefixRowAt_unique ((mem_sourceChains a).mp ha) hb hae hbe)
      · intro hb'
        exact absurd ((mem_sourceChains b).mpr hb) hb'
    · rw [if_neg hP]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro hae
      exact hP ⟨a, (mem_sourceChains a).mp ha, hae⟩
theorem counted_le_cost (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary) :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))
        (fun _ _ => none) r * (r.2.1.2 : ENNReal) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  conv_rhs => rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))
      (fun _ _ => none)).support
  · apply mul_le_mul' le_rfl
    have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r hr
    have hmem := PrefixGame.lazyRun_mem_support _ _ _ hlazy
    exact_mod_cast le_of_eq (seedGame_charge adversary q a R r.1 r.2.1 hmem)
  · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]
/-- Per rest table: the two-edge event of the `realRun` mixture against its prefix cost. -/
theorem twoEdge_mix_R (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] ≤
      twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge adversary q a R endpoint result h)
  have hreal := seedGame_real_cost adversary q a R
  have h1 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h1 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (twoEdgeRate q * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h1
    _ = twoEdgeRate q * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem twoEdgeAt_iff_sample (adversary : AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).TwoEdge | referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact twoEdgeAt_iff_view a s qs hqs
end ClaudeWCT.W9.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsContacts ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
/-- Per rest table: the contact event of the `realRun` mixture against its prefix cost. -/
theorem contact_mix_R (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] ≤
      (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge adversary q a R endpoint result h)
  have hreal := seedGame_real_cost adversary q a R
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h2 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem contactAt_iff_sample (adversary : AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).Contact | referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact contactAt_iff_view a s qs hqs
noncomputable def contactCount (s : RefSample) : Nat :=
  (sourceChains.filter fun a => ContactAt s.answers s.trace a).card
theorem expected_contactCount (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) =
      ∑ a ∈ sourceChains, Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold contactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ContactAt s.answers s.trace a
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
noncomputable def sourceChains7 : Finset ChainAddr :=
  SigGolfCandidate.T3.Security.Wots.sourceChains.filter WotsExtract.SourceChain7

theorem mem_sourceChains7 (a : ChainAddr) : a ∈ sourceChains7 ↔ WotsExtract.SourceChain7 a := by
  rw [sourceChains7, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨(SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mpr ⟨⟨by have := h.1.tree_lt; omega, h.1.2⟩, h.2⟩, h⟩

def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain7 a ∧ PrefixRowAt answers a input
  | _ => False
noncomputable def prefixClassCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRow s.answers (.inl (.inr e.1)))).length
theorem prefixRowAt_unique {answers : Answers} {a b : ChainAddr} (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) {input : HashInput} (hia : PrefixRowAt answers a input)
    (hib : PrefixRowAt answers b input) : a = b := by
  obtain ⟨s, v, hs, rfl⟩ := hia
  obtain ⟨s', v', hs', he⟩ := hib
  have h7a := CanonicalRef.Mask.depth_le_seven answers (sourceMessages answers) a
  have h7b := CanonicalRef.Mask.depth_le_seven answers (sourceMessages answers) b
  have hca : a.chain < 2 ^ 24 := by have := ha.2; have := Mask.chainCount_le a.key.lay; omega
  have hcb : b.chain < 2 ^ 24 := by have := hb.2; have := Mask.chainCount_le b.key.lay; omega
  have h := chainInputW_eq_chainRowW (a := b) hca hcb (by omega) (by omega) ((chainRowW_eq a s v).symm.trans he)
  have hkey := h.1.eq_of_lt (by have := ha.1.tree_lt; omega)
    (by have := ha.1.2; have : 2 ^ height a.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega); omega)
    (by have := hb.1.tree_lt; omega)
    (by have := hb.1.2; have : 2 ^ height b.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le b.key.lay; omega); omega)
  cases a; cases b
  simp only at hkey h ⊢
  rw [h.2.1, ← hkey]
theorem prefixCount_sum_le (s : RefSample) :
    ∑ a ∈ sourceChains7, prefixCount a s ≤ prefixClassCount s := by
  unfold prefixCount prefixClassCount
  simp only [← List.countP_eq_length_filter]
  have h := SphincsSecurity.QueryCap.calls_sum_le sourceChains7
    (fun a (e : Entry) => PrefixRowAt s.answers a e.1) (fun e => PrefixRow s.answers (.inl (.inr e.1)))
    ?_ s.trace
  · simpa only [SphincsSecurity.QueryCap.calls] using h
  · intro e
    by_cases hP : PrefixRow s.answers (.inl (.inr e.1))
    · rw [if_pos hP]
      obtain ⟨b, hb, hbe⟩ := hP
      rw [Finset.sum_eq_single b]
      · rw [if_pos hbe]
      · intro a ha hab
        rw [if_neg]
        intro hae
        exact hab (prefixRowAt_unique ((mem_sourceChains7 a).mp ha) hb hae hbe)
      · intro hb'
        exact absurd ((mem_sourceChains7 b).mpr hb) hb'
    · rw [if_neg hP]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro hae
      exact hP ⟨a, (mem_sourceChains7 a).mp ha, hae⟩
noncomputable def errTot (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : ℝ≥0∞ :=
  ∑ a ∈ sourceChains7, Core.errC adversary q a

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem counted_le_cost (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint))
        (fun _ _ => none) r * (r.2.1.2 : ENNReal) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  conv_rhs => rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint))
      (fun _ _ => none)).support
  · apply mul_le_mul' le_rfl
    have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r hr
    have hmem := PrefixGame.lazyRun_mem_support _ _ _ hlazy
    exact_mod_cast le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R r.1 r.2.1 hmem)
  · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]
/-- Per rest table: the two-edge event of the `realRun` mixture against its prefix cost. -/
theorem twoEdge_mix_R (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none)] ≤
      twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint result h)
  have hreal := seedGame_real_cost (referenceInputs_subset adversary) adversary q a R
  have h1 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h1 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (twoEdgeRate q * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h1
    _ = twoEdgeRate q * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem twoEdgeAt_iff_sample (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact twoEdgeAt_iff_view a s qs hqs
/-- Per rest table: the contact event of the `realRun` mixture against its prefix cost. -/
theorem contact_mix_R (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none)] ≤
      (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint result h)
  have hreal := seedGame_real_cost (referenceInputs_subset adversary) adversary q a R
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h2 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame (referenceInputs_subset adversary) adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem contactAt_iff_sample (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) :
    Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q] := by
  apply pmf_probEvent_congr
  intro s hs
  obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
  exact contactAt_iff_view a s qs hqs
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
noncomputable def contactCount (s : RefSample) : Nat :=
  (sourceChains7.filter fun a => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a).card
theorem expected_contactCount (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (contactCount s : ENNReal) =
      ∑ a ∈ sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold contactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Contacts
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsRestartBase ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {β : Type}
variable {adversary : AdversaryP}
noncomputable def pausedSeed (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  simulateQ (routeImpl a (restDepth a R) R) (pausedFull stop (referenceGame (fillTable a R endpoint) adversary q) [])
theorem pausedSeed_snd (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) : Prod.snd <$> pausedSeed adversary q a R stop endpoint = seedGame adversary q a R endpoint := by
  unfold pausedSeed seedGame
  rw [← simulateQ_map, pausedFull_snd]
noncomputable def seedBefore (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) ((List Entry × OracleComp RefWorld SeedResult) × Nat) :=
  SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryPause.run stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
noncomputable def seedAfter (a : ChainAddr) (R : RefTables adversary)
    (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat) :
    OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (routeImpl a (restDepth a R) R) middle.1.2
theorem seedBefore_after (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) :
    (do
      let middle ← seedBefore adversary q a R stop endpoint
      let result ← seedAfter a R middle
      pure (middle.1.1, result)) = pausedSeed adversary q a R stop endpoint := by
  unfold seedBefore seedAfter pausedSeed pausedFull
  simp only [simulateQ_bind, simulateQ_pure]
  conv_rhs => rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))]
  rw [bind_map_left]
theorem seedGame_support_cost (q : Nat) (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest)
    (result : SeedResult) (h : result ∈ support (seedGame adversary q a R endpoint)) : seedCost a R result ≤ q := by
  have hrec : result ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (fillTable a R endpoint) adversary q)) := by
    unfold seedGame at h
    revert h
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) result
  have hcount : (result.1, SphincsSecurity.QueryCap.calls RefCharged result.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (fillTable a R endpoint) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result, hrec, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (fillTable a R endpoint) adversary q) _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
theorem checkpoint_budget (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ q ∧ queryCount result.2 ≤ q := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hmem := lazyRun_mem_support _ _ _ hfull
  have htotal : middle.1.2 + result.1.2 ≤ q := by
    have hc := seedGame_charge adversary q a R endpoint _ hmem
    have hs := seedGame_support_cost q a R endpoint result.1.1 (by
      have := SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (seedGame adversary q a R endpoint)
      rw [← this, support_map]
      exact ⟨_, hmem, rfl⟩)
    simp only at hc
    omega
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  have hrows := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ middle.2 result hresult
  constructor <;> omega
theorem checkpoint_charge (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + 2 * result.1.2 ≤ 2 * seedCost a R result.1.1 := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hc := seedGame_charge adversary q a R endpoint _ (lazyRun_mem_support _ _ _ hfull)
  simp only at hc
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  omega
/-- The observed prefix rows of chain `a` are the used halves (`rowHalf`, C3) of the recorded answers. -/
def RowsInvW (a : ChainAddr) {d : Nat} (memory : List Entry) (observed : Fin d → Digest → Option Digest) : Prop :=
  ∀ (i : Fin d) (v w : Digest), observed i v = some w ↔
    ∃ answer, (chainRowW a i v, answer) ∈ memory ∧ rowHalf a i answer = w
theorem rowsInvW_nil (a : ChainAddr) (d : Nat) : RowsInvW a (d := d) [] (fun _ _ => none) := by
  intro i v w
  simp
theorem route_step_lazy (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (input : RefWorld.Domain)
    (memory : List Entry) (observed : Fin d → Digest → Option Digest) (hinv : RowsInvW a memory observed)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (routeImpl a d R input) observed).support) :
    RowsInvW a (stepTrace input result.1 memory) result.2 := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
    simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simpa [stepTrace, entryOf] using hinv
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        intro i v w
        rw [hinv i v w]
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨answer, hm, hl⟩
          exact ⟨answer, Or.inl hm, hl⟩
        · rintro ⟨answer, hm | hm, hl⟩
          · exact ⟨answer, hm, hl⟩
          · exact absurd (congrArg Prod.fst hm).symm (PrefixGame.rowOf_none hp (i, v))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
        simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
        obtain ⟨w₀, hw₀, rfl⟩ := hr
        have hin := PrefixGame.rowOf_some hp
        subst hin
        intro i v w
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [record, Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨_, Or.inr rfl, ?_⟩
            simp only [rowHalf, halfOf_joinHalf]
          · rintro ⟨answer, hm | hm, hl⟩
            ·
              have hold := (hinv i v w).mpr ⟨answer, hm, hl⟩
              simp only [hold, SphincsSecurity.Concrete.PartialChainEndpoint.rowLaw, PMF.mem_support_pure_iff] at hw₀
              exact hw₀
            · have := congrArg Prod.snd hm
              simp only at this
              rw [← hl, this]
              simp only [rowHalf, halfOf_joinHalf]
        · have hne : chainRowW a p.1 p.2 ≠ chainRowW a i v := by
            intro he
            obtain ⟨hs, hv⟩ := chainRowW_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          have hrec : record observed p w₀ i v = observed i v := by
            simp only [record]
            by_cases h1 : i = p.1
            · subst h1
              have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
              simp only [Function.update_self, Function.update_of_ne h2]
            · simp only [Function.update_of_ne h1]
          rw [hrec, hinv i v w]
          constructor
          · rintro ⟨answer, hm, hl⟩
            exact ⟨answer, Or.inl hm, hl⟩
          · rintro ⟨answer, hm | hm, hl⟩
            · exact ⟨answer, hm, hl⟩
            · exact absurd (congrArg Prod.fst hm).symm hne
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simpa [stepTrace, entryOf] using hinv
theorem checkpoint_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support) :
    RowsInvW a middle.1.1.1 middle.2 := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hplain : (middle.1.1, middle.2) ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none)).support := by
    rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])),
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_map, PMF.mem_support_map_iff]
    exact ⟨middle, hmiddle, rfl⟩
  have hcomp : lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none) =
      (simulateQ ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
        (SphincsSecurity.QueryPause.run stop stepTrace
          (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])).run
        (fun _ _ => none) := by
    unfold lazyRun
    rw [QueryImpl.simulateQ_compose]
  rw [hcomp] at hplain
  exact SphincsSecurity.QueryPause.run_simulation_invariant stop stepTrace
    ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
    (fun memory observed => RowsInvW a memory observed)
    (fun memory observed hinv _ input result hresult =>
      route_step_lazy a hd R input memory observed hinv result (by
        simpa only [QueryImpl.apply_compose, lazyRun] using hresult))
    _ [] (fun _ _ => none) (rowsInvW_nil a _) _ hplain
end PrefixGame
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill PairedReference.referenceGame PairedReference.offlineGame
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable def fillTable (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (e : Digest) : Answers :=
  answers (referenceInputs_subset adversary) (RawPrefix.fill a R e)
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (R : Tables (PairedReference.referenceInputs adversary)) (e : Digest) : QueryImpl RefWorld (OracleComp (SeedSpec d)) :=
  Route.routeImpl a d (answers (referenceInputs_subset adversary) R) (fillTable a R e)
noncomputable def pausedSeed (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (RawPrefix.restDepth a R)) (List Entry × SeedResult) :=
  simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint) (pausedFull stop (PairedReference.referenceGame (fillTable a R endpoint) adversary q) [])
theorem pausedSeed_snd (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (stop : List Entry → Prop)
    (endpoint : Digest) : Prod.snd <$> pausedSeed adversary q a R stop endpoint = seedGame (referenceInputs_subset adversary) adversary q a R endpoint := by
  unfold pausedSeed seedGame routeImpl fillTable
  rw [← simulateQ_map, pausedFull_snd]
noncomputable def seedBefore (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (RawPrefix.restDepth a R)) ((List Entry × OracleComp RefWorld SeedResult) × Nat) :=
  SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint)
    (SphincsSecurity.QueryPause.run stop stepTrace
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) []))
noncomputable def seedAfter (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest)
    (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat) :
    OracleComp (SeedSpec (RawPrefix.restDepth a R)) SeedResult :=
  simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint) middle.1.2
theorem seedBefore_after (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (stop : List Entry → Prop)
    (endpoint : Digest) :
    (do
      let middle ← seedBefore adversary q a R stop endpoint
      let result ← seedAfter a R endpoint middle
      pure (middle.1.1, result)) = pausedSeed adversary q a R stop endpoint := by
  unfold seedBefore seedAfter pausedSeed pausedFull
  simp only [simulateQ_bind, simulateQ_pure]
  conv_rhs => rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) []))]
  rw [bind_map_left]
theorem seedGame_support_cost (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest)
    (result : SeedResult) (h : result ∈ support (seedGame (referenceInputs_subset adversary) adversary q a R endpoint)) : seedCost a R result ≤ q := by
  have hrec : result ∈ support (SphincsSecurity.QueryCap.recorded
      (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) := by
    unfold seedGame at h
    revert h
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (routeImpl a (RawPrefix.restDepth a R) R endpoint)
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) result
  have hcount : (result.1, SphincsSecurity.QueryCap.calls RefCharged result.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result, hrec, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (fillTable a R endpoint) adversary q) _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
theorem checkpoint_budget (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R endpoint middle.1)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ q ∧ queryCount result.2 ≤ q := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R endpoint m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame routeImpl fillTable
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers (referenceInputs_subset adversary) (RawPrefix.fill a R endpoint)) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hmem := lazyRun_mem_support _ _ _ hfull
  have htotal : middle.1.2 + result.1.2 ≤ q := by
    have hc := seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint _ hmem
    have hs := seedGame_support_cost q a R endpoint result.1.1 (by
      have := SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint)
      rw [← this, support_map]
      exact ⟨_, hmem, rfl⟩)
    simp only at hc
    omega
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  have hrows := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ middle.2 result hresult
  constructor <;> omega
theorem checkpoint_charge (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R endpoint middle.1)) middle.2).support) :
    queryCount middle.2 + 2 * result.1.2 ≤ 2 * seedCost a R result.1.1 := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R endpoint m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame routeImpl fillTable
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers (referenceInputs_subset adversary) (RawPrefix.fill a R endpoint)) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame (referenceInputs_subset adversary) adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hc := seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint _ (lazyRun_mem_support _ _ _ hfull)
  simp only at hc
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  omega
theorem route_step_lazy (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest) (input : RefWorld.Domain)
    (memory : List Entry) (observed : Fin d → Digest → Option Digest)
    (hinv : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (routeImpl a d R endpoint input) observed).support) :
    ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a (stepTrace input result.1 memory) result.2 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, Route.routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
    simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simpa [stepTrace, entryOf] using hinv
  · cases hp : PrefixGame.rowOf a d input with
    | none =>
        simp only [routeImpl, Route.routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        intro i v w
        rw [hinv i v w]
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨answer, hm, hl⟩
          exact ⟨answer, Or.inl hm, hl⟩
        · rintro ⟨answer, hm | hm, hl⟩
          · exact ⟨answer, hm, hl⟩
          · exact absurd (congrArg Prod.fst hm).symm (PrefixGame.rowOf_none hp (i, v))
    | some p =>
        simp only [routeImpl, Route.routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
        simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
        obtain ⟨w₀, hw₀, rfl⟩ := hr
        have hin := PrefixGame.rowOf_some hp
        subst hin
        intro i v w
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [record, Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨_, Or.inr rfl, ?_⟩
            simp only [rowHalf, halfOf_joinHalf]
          · rintro ⟨answer, hm | hm, hl⟩
            ·
              have hold := (hinv i v w).mpr ⟨answer, hm, hl⟩
              simp only [hold, SphincsSecurity.Concrete.PartialChainEndpoint.rowLaw, PMF.mem_support_pure_iff] at hw₀
              exact hw₀
            · have := congrArg Prod.snd hm
              simp only at this
              rw [← hl, this]
              simp only [rowHalf, halfOf_joinHalf]
        · have hne : chainRowW a p.1 p.2 ≠ chainRowW a i v := by
            intro he
            obtain ⟨hs, hv⟩ := chainRowW_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          have hrec : record observed p w₀ i v = observed i v := by
            simp only [record]
            by_cases h1 : i = p.1
            · subst h1
              have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
              simp only [Function.update_self, Function.update_of_ne h2]
            · simp only [Function.update_of_ne h1]
          rw [hrec, hinv i v w]
          constructor
          · rintro ⟨answer, hm, hl⟩
            exact ⟨answer, Or.inl hm, hl⟩
          · rintro ⟨answer, hm | hm, hl⟩
            · exact ⟨answer, hm, hl⟩
            · exact absurd (congrArg Prod.fst hm).symm hne
  · simp only [routeImpl, Route.routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simpa [stepTrace, entryOf] using hinv
theorem checkpoint_rows (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support) :
    ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a middle.1.1.1 middle.2 := by
  have hd : RawPrefix.restDepth a R ≤ 256 := by have := RawPrefix.restDepth_le a R; omega
  have hplain : (middle.1.1, middle.2) ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none)).support := by
    rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) [])),
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_map, PMF.mem_support_map_iff]
    exact ⟨middle, hmiddle, rfl⟩
  have hcomp : lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (RawPrefix.restDepth a R) R endpoint) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none) =
      (simulateQ ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (RawPrefix.restDepth a R) R endpoint)
        (SphincsSecurity.QueryPause.run stop stepTrace
          (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (fillTable a R endpoint) adversary q)) [])).run
        (fun _ _ => none) := by
    unfold lazyRun
    rw [QueryImpl.simulateQ_compose]
  rw [hcomp] at hplain
  exact SphincsSecurity.QueryPause.run_simulation_invariant stop stepTrace
    ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (RawPrefix.restDepth a R) R endpoint)
    (fun memory observed => ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed)
    (fun memory observed hinv _ input result hresult =>
      route_step_lazy a hd R endpoint input memory observed hinv result (by
        simpa only [QueryImpl.apply_compose, lazyRun] using hresult))
    _ [] (fun _ _ => none) (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.rowsInvW_nil a _) _ hplain

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsRestart ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem fixed_pausedSeed (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (stop : List Entry → Prop) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) =
      (liftM (simulateQ (refImpl (restTable (ov a (restDepth a R) R x)))
        (pausedFull stop (referenceGame (restTable (ov a (restDepth a R) R x)) adversary q) [])) :
          PMF (List Entry × SeedResult)) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold pausedSeed
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl
theorem coupled_paused (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (stop : List Entry → Prop)
    (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    res.1.1 = (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take res.1.1.length ∧
      (∀ j, j < res.1.1.length → ¬stop ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take j)) ∧
      (stop res.1.1 ∨ res.1.1 = traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega
  have hfst : res.1 ∈ (simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2)))).support := by
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨res, hres, rfl⟩
  rw [fixed_pausedSeed q a htree hleaf R x stop] at hfst
  have hmem := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hfst
  obtain ⟨-, h2, h3, h4⟩ := paused_structure _ stop _ [] res.1 hmem
  simp only [List.nil_append, List.length_nil, Nat.zero_le, true_implies] at h2 h3 h4
  exact ⟨h2, h3, h4⟩
theorem coupled_paused_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    (res.1.2, res.2) ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support := by
  rw [← pausedSeed_snd q a R stop, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_map,
    PMF.mem_support_map_iff]
  exact ⟨res, hres, rfl⟩
theorem contactAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : ContactAt T (trace.take j) a) : ContactAt T (trace.take k) a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, (List.take_prefix_take_left hjk).subset hm, hl⟩
theorem contactAt_congr {T T' : Answers} (trace : List Entry) (a : ChainAddr) (hd : depth T a = depth T' a)
    (hf : frontierValue T a = frontierValue T' a) : ContactAt T trace a ↔ ContactAt T' trace a := by
  unfold ContactAt
  rw [hd, hf]
theorem fillTable_depth (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) :
    depth (fillTable a R endpoint) a = restDepth a R :=
  (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
theorem fillTable_frontier (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest)
    (hd : 1 ≤ restDepth a R) : frontierValue (fillTable a R endpoint) a = endpoint := by
  unfold fillTable
  rw [frontierValue_ov]
  obtain ⟨d', hd'⟩ : ∃ d', restDepth a R = d' + 1 := ⟨restDepth a R - 1, by omega⟩
  generalize ovSeed a R endpoint = s0
  revert s0
  rw [hd']
  intro s0
  exact evaluate_const_succ d' endpoint s0
theorem contact_iff_rowsInv (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) (memory : List Entry)
    (observed : Fin (restDepth a R) → Digest → Option Digest) (hinv : RowsInvW a memory observed) :
    Contact observed endpoint ↔ ContactAt (fillTable a R endpoint) memory a := by
  by_cases hd0 : restDepth a R = 0
  · unfold Contact ContactAt
    rw [fillTable_depth]
    constructor
    · rintro ⟨i, -, -⟩
      exact absurd i.isLt (by omega)
    · rintro ⟨h, -⟩
      omega
  unfold Contact ContactAt SeenRowW
  rw [fillTable_depth, fillTable_frontier a R endpoint (by omega)]
  constructor
  · rintro ⟨i, hi, value, h⟩
    obtain ⟨answer, hm, hl⟩ := (hinv i value endpoint).mp h
    have he : restDepth a R - 1 = i.val := by omega
    refine ⟨by omega, value, answer, ?_, ?_⟩
    · rw [he]; exact hm
    · rw [he]; exact hl
  · rintro ⟨hd, value, answer, hm, hl⟩
    refine ⟨⟨restDepth a R - 1, by omega⟩, by simp only; omega, value, (hinv _ value endpoint).mpr ⟨answer, hm, hl⟩⟩
end PrefixGame
open PrefixGame in
def ContactAfterStop (Stop : Answers → List Entry → Prop) (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, Stop T (trace.take k) ∧ ¬ContactAt T (trace.take k) a ∧ ContactAt T trace a
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem coupled_contact (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    ContactAt (restTable (ov a (restDepth a R) R x)) (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
      Contact res.2 (evaluate x.1 (ovSeed a R x.2)) := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2) (coupled_paused_rows q a R x stop res hres)
  have h1 := contactAt_iff_view a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) res.1.2.2 rfl
  rw [hview, runView_contact] at h1
  exact h1
end PrefixGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
/-- The stop predicate on the honest table of chain `a`'s prefix game. -/
def stopAt (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary) (e : Digest)
    (trace : List Entry) : Prop := Stop (fillTable a R e) trace
/-- The paused prefix game. -/
noncomputable def restartGame (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) (e : Digest) : OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  pausedSeed adversary q a R (stopAt Stop a R e) e
def genCAS (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1 a ∧ Contact r.2.2 r.1
def genStop (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1
noncomputable def genCharge (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : ENNReal :=
  ((2 * seedCost a R r.2.1.2 : ℕ) : ENNReal) * (if stopAt Stop a R r.1 r.2.1.1 then 1 else 0)
theorem restartGame_snd (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary)
    (e : Digest) : Prod.snd <$> restartGame adversary q a Stop R e = seedGame adversary q a R e :=
  pausedSeed_snd q a R _ e

/-- **Per rest table: contact after the stop, against the stop.** -/
theorem restart_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[genStop Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    let aux : Digest → QueryImpl unifSpec PMF := fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun aux before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun aux (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project aux before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support aux before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun aux before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hs : Pr[fun r => marked r.1 r.2 | realRun aux before (fun _ _ => none)] ≤
        Pr[genStop Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] := by
      rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_mark_probability aux before after
        (fun _ _ => none) marked, ← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_mono
      intro r _ hm
      exact hm.1
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_le_mark aux before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
      (fun r hr _ => (checkpoint_budget q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2).1)
    rw [card_digest] at hkernel
    rw [hc]
    exact hkernel.trans (mul_le_mul' le_rfl hs)

/-- **Per rest table: contact after the stop, against the prefix charge.** -/
theorem charge_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r := by
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_charge (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
    rw [card_digest] at hkernel
    rw [hc]
    refine hkernel.trans ?_
    have hexp : (∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r) =
        ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
          (fun _ _ => none) r * genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := by
      rw [← hproj, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
    refine le_of_le_of_eq ?_ hexp.symm
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).support
    · apply mul_le_mul' le_rfl
      have hch := checkpoint_charge q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2
      by_cases hm : marked r.1 r.2.1
      · rw [if_pos hm, mul_one]
        have hgc : genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) =
            ((2 * seedCost a R r.2.2.1.1 : ℕ) : ENNReal) := by
          simp only [genCharge]
          rw [if_pos hm.1, mul_one]
        rw [hgc]
        exact_mod_cast hch
      · rw [if_neg hm, mul_zero]
        exact bot_le
    · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]

/-! ### Couplings with the reference experiment (seed frozen at `ovSeed`) -/

theorem contactAt_ov_fill (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (trace : List Entry) :
    ContactAt (restTable (ov a (restDepth a R) R x)) trace a ↔
      ContactAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace a := by
  have hd : depth (restTable (ov a (restDepth a R) R x)) a = depth (fillTable a R (evaluate x.1 (ovSeed a R x.2))) a := by
    rw [fillTable_depth]; exact (restDepth_eq a _).symm.trans (restDepth_ov a R x)
  by_cases hd0 : restDepth a R = 0
  · unfold ContactAt
    rw [hd, fillTable_depth]
    exact ⟨fun h => absurd h.1 (by omega), fun h => absurd h.1 (by omega)⟩
  · apply contactAt_congr trace a hd
    rw [fillTable_frontier a R _ (by omega), frontierValue_ov]

section Couple
variable (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (Stop : Answers → List Entry → Prop)
  (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) (R : RefTables adversary)
  (x : Hidden (restDepth a R))
  (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
  (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
    (restartGame adversary q a Stop R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support)
include hmask in
theorem blind_frozen (trace : List Entry) :
    Stop (restTable (ov a (restDepth a R) R x)) trace ↔ stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)) trace := by
  show _ ↔ Stop (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace
  rw [← hmask, maskAt_ov_fill, hmask]
include ha hmask hres
theorem cas_coupled :
    ContactAfterStop Stop (restTable (ov a (restDepth a R) R x))
        (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
      genCAS Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  have hc := coupled_contact q a R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  unfold ContactAfterStop genCAS
  simp only [blind_frozen a Stop hmask R x, contactAt_ov_fill a R x]
  rw [first_stop_iff (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)))
    (fun trace => ContactAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace a)
    h1 h2 h3 (fun j k hjk h => contactAt_take_mono _ _ a hjk h)]
  rw [← contactAt_ov_fill a R x (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2), hc]
theorem stop_coupled :
    (∃ k, Stop (restTable (ov a (restDepth a R) R x))
        ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k)) ↔
      genStop Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  simp only [blind_frozen a Stop hmask R x]
  exact first_stop_exists_iff _ h1 h2 h3
theorem charge_coupled :
    ((2 * prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) : ℕ) : ENNReal) *
        (if ∃ k, Stop (restTable (ov a (restDepth a R) R x))
          ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k) then 1 else 0) =
      genCharge Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2)
    (coupled_paused_rows q a R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres)
  have hcount : prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 :=
    congrArg PrefixView.count hview
  have hstop := stop_coupled q a ha Stop hmask R x res hres
  unfold genCharge
  rw [hcount]
  by_cases hs : stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)) res.1.1
  · rw [if_pos (hstop.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hstop.mp h)), if_neg hs]
end Couple
end PrefixGame

theorem markerAt_maskAt (T : Answers) (trace : List Entry) (a : ChainAddr) (hal : Mask.MaskOK a) :
    MarkerAt (maskAt T a) trace a ↔ MarkerAt T trace a := by
  unfold MarkerAt
  rw [referenceInput_maskAt _ _ hal, referenceDigits_maskAt _ _ hal]
theorem markerAt_take_exists (T : Answers) (trace : List Entry) (a : ChainAddr) :
    (∃ k, MarkerAt T (trace.take k) a) ↔ MarkerAt T trace a := by
  constructor
  · rintro ⟨k, message, counter, pad, answer, digits, hfit, hm, h⟩
    exact ⟨message, counter, pad, answer, digits, hfit, List.mem_of_mem_take hm, h⟩
  · intro h
    exact ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem sourceChain_maskOK (a : ChainAddr) (ha : WotsExtract.SourceChain a) : Mask.MaskOK a :=
  Mask.maskOK_of_lt (by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill PairedReference.referenceGame PairedReference.offlineGame
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable def depth (T : Answers) (a : ChainAddr) := CanonicalRef.depth T (sourceMessages T) a
noncomputable def frontierValue (T : Answers) (a : ChainAddr) := CanonicalRef.frontierValue T (sourceMessages T) a
def ContactAt (T : Answers) (trace : List Entry) (a : ChainAddr) := CanonicalRef.ContactAt T (sourceMessages T) trace a
noncomputable def maskAt (T : Answers) (a : ChainAddr) := CanonicalRef.maskAt T (sourceMessages T) a
theorem fixed_pausedSeed (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R)) (stop : List Entry → Prop) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (pausedSeed adversary q a R stop (evaluate x.1 (RawPrefix.ovSeed a R x.2))) =
      (liftM (simulateQ (refImpl (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
        (pausedFull stop (PairedReference.referenceGame (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) adversary q) [])) :
          PMF (List Entry × SeedResult)) := by
  have hd : RawPrefix.restDepth a R ≤ 256 := by have := RawPrefix.restDepth_le a R; omega
  unfold pausedSeed routeImpl fillTable
  rw [← QueryImpl.simulateQ_compose, Normalized.fixed_route (referenceInputs_subset adversary) a hleaf R x, ← Normalized.referenceGame_fill (referenceInputs_subset adversary) a ha htree hleaf R x adversary q,
    QueryImpl.simulateQ_compose]
  rfl
theorem coupled_paused (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (R : Tables (PairedReference.referenceInputs adversary))
    (x : Hidden (RawPrefix.restDepth a R)) (stop : List Entry → Prop)
    (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    res.1.1 = (traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2).take res.1.1.length ∧
      (∀ j, j < res.1.1.length → ¬stop ((traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2).take j)) ∧
      (stop res.1.1 ∨ res.1.1 = traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.tree_lt; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega
  have hfst : res.1 ∈ (simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (pausedSeed adversary q a R stop (evaluate x.1 (RawPrefix.ovSeed a R x.2)))).support := by
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨res, hres, rfl⟩
  rw [fixed_pausedSeed q a ha.1 htree hleaf R x stop] at hfst
  have hmem := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hfst
  obtain ⟨-, h2, h3, h4⟩ := paused_structure _ stop _ [] res.1 hmem
  simp only [List.nil_append, List.length_nil, Nat.zero_le, true_implies] at h2 h3 h4
  exact ⟨h2, h3, h4⟩
theorem coupled_paused_rows (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    (res.1.2, res.2) ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame (referenceInputs_subset adversary) adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support := by
  rw [← pausedSeed_snd q a R stop, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_map,
    PMF.mem_support_map_iff]
  exact ⟨res, hres, rfl⟩
theorem contactAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : ContactAt T (trace.take j) a) : ContactAt T (trace.take k) a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, (List.take_prefix_take_left hjk).subset hm, hl⟩
theorem contactAt_congr {T T' : Answers} (trace : List Entry) (a : ChainAddr) (hd : depth T a = depth T' a)
    (hf : frontierValue T a = frontierValue T' a) : ContactAt T trace a ↔ ContactAt T' trace a := by
  unfold ContactAt CanonicalRef.ContactAt
  change CanonicalRef.depth T (sourceMessages T) a = CanonicalRef.depth T' (sourceMessages T') a at hd
  change CanonicalRef.frontierValue T (sourceMessages T) a = CanonicalRef.frontierValue T' (sourceMessages T') a at hf
  rw [hd, hf]
theorem fillTable_depth (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest) :
    depth (fillTable a R endpoint) a = RawPrefix.restDepth a R := by
  unfold depth fillTable
  rw [depth_eq (referenceInputs_subset adversary) _ a ha, ← RawPrefix.restDepth_eq]
  unfold RawPrefix.fill
  exact RawPrefix.restDepth_ov a R _
theorem fillTable_frontier (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest)
    (hd : 1 ≤ RawPrefix.restDepth a R) : frontierValue (fillTable a R endpoint) a = endpoint := by
  unfold frontierValue fillTable
  rw [frontier_eq (referenceInputs_subset adversary) _ a ha]
  unfold RawPrefix.fill
  rw [RawPrefix.frontierValue_ov (referenceInputs_subset adversary)]
  obtain ⟨d', hd'⟩ : ∃ d', RawPrefix.restDepth a R = d' + 1 := ⟨RawPrefix.restDepth a R - 1, by omega⟩
  generalize RawPrefix.ovSeed a R endpoint = s0
  revert s0
  rw [hd']
  intro s0
  exact ClaudeWCT.W9.T3.Security.Wots.PrefixGame.evaluate_const_succ d' endpoint s0
theorem contact_iff_rowsInv (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) (R : Tables (PairedReference.referenceInputs adversary)) (endpoint : Digest) (memory : List Entry)
    (observed : Fin (RawPrefix.restDepth a R) → Digest → Option Digest)
    (hinv : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed) :
    Contact observed endpoint ↔ ContactAt (fillTable a R endpoint) memory a := by
  by_cases hd0 : RawPrefix.restDepth a R = 0
  · unfold Contact ContactAt CanonicalRef.ContactAt
    change _ ↔ 1 ≤ depth (fillTable a R endpoint) a ∧ _
    rw [fillTable_depth a ha]
    constructor
    · rintro ⟨i, -, -⟩
      exact absurd i.isLt (by omega)
    · rintro ⟨h, -⟩
      omega
  -- C3 (#866): the contact row is read through the half its step keeps (`SeenRowW`, `RowsInvW`).
  unfold Contact ContactAt CanonicalRef.ContactAt ClaudeWCT.W9.T3.Security.Wots.SeenRowW
  change _ ↔ 1 ≤ depth (fillTable a R endpoint) a ∧ ∃ value answer, (chainRowW a (depth (fillTable a R endpoint) a - 1) value, answer) ∈ memory ∧ rowHalf a (depth (fillTable a R endpoint) a - 1) answer = frontierValue (fillTable a R endpoint) a
  rw [fillTable_depth a ha, fillTable_frontier a ha R endpoint (by omega)]
  constructor
  · rintro ⟨i, hi, value, h⟩
    obtain ⟨answer, hm, hl⟩ := (hinv i value endpoint).mp h
    have he : RawPrefix.restDepth a R - 1 = i.val := by omega
    refine ⟨by omega, value, answer, ?_, ?_⟩
    · rw [he]; exact hm
    · rw [he]; exact hl
  · rintro ⟨hd, value, answer, hm, hl⟩
    refine ⟨⟨RawPrefix.restDepth a R - 1, by omega⟩, by simp only; omega, value, (hinv _ value endpoint).mpr ⟨answer, hm, hl⟩⟩
def ContactAfterStop (Stop : Answers → List Entry → Prop) (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, Stop T (trace.take k) ∧ ¬ContactAt T (trace.take k) a ∧ ContactAt T trace a
theorem coupled_contact (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    ContactAt (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2) a ↔
      Contact res.2 (evaluate x.1 (RawPrefix.ovSeed a R x.2)) := by
  have hview := sampleView_coupled adversary q a R ha x (res.1.2, res.2) (coupled_paused_rows q a R x stop res hres)
  have h1 := contactAt_iff_view a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) res.1.2.2 rfl
  rw [hview, runView_contact] at h1
  exact h1
/-- The stop predicate on the honest table of chain `a`'s prefix game. -/
def stopAt (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary)) (e : Digest)
    (trace : List Entry) : Prop := Stop (fillTable a R e) trace
/-- The paused prefix game. -/
noncomputable def restartGame (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary)) (e : Digest) : OracleComp (SeedSpec (RawPrefix.restDepth a R)) (List Entry × SeedResult) :=
  pausedSeed adversary q a R (stopAt Stop a R e) e
def genCAS (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1 a ∧ Contact r.2.2 r.1
def genStop (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1
noncomputable def genCharge (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) : ENNReal :=
  ((2 * seedCost a R r.2.1.2 : ℕ) : ENNReal) * (if stopAt Stop a R r.1 r.2.1.1 then 1 else 0)
theorem restartGame_snd (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary))
    (e : Digest) : Prod.snd <$> restartGame adversary q a Stop R e = seedGame (referenceInputs_subset adversary) adversary q a R e :=
  pausedSeed_snd q a R _ e

/-- **Per rest table: contact after the stop, against the stop.** -/
theorem restart_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[genStop Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    let aux : Digest → QueryImpl unifSpec PMF := fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (endpoint : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => seedAfter a R endpoint middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun aux before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun aux (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project aux before
        (fun e middle => seedAfter a R e middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support aux before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun aux before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a ha R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hs : Pr[fun r => marked r.1 r.2 | realRun aux before (fun _ _ => none)] ≤
        Pr[genStop Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] := by
      rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_mark_probability aux before after
        (fun _ _ => none) marked, ← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_mono
      intro r _ hm
      exact hm.1
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_le_mark aux before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
      (fun r hr _ => (checkpoint_budget q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2).1)
    rw [card_digest] at hkernel
    rw [hc]
    exact hkernel.trans (mul_le_mul' le_rfl hs)

/-- **Per rest table: contact after the stop, against the prefix charge.** -/
theorem charge_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r := by
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (endpoint : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => seedAfter a R endpoint middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
        (fun e middle => seedAfter a R e middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a ha R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_charge (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
    rw [card_digest] at hkernel
    rw [hc]
    refine hkernel.trans ?_
    have hexp : (∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r) =
        ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
          (fun _ _ => none) r * genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := by
      rw [← hproj, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
    refine le_of_le_of_eq ?_ hexp.symm
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).support
    · apply mul_le_mul' le_rfl
      have hch := checkpoint_charge q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2
      by_cases hm : marked r.1 r.2.1
      · rw [if_pos hm, mul_one]
        have hgc : genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) =
            ((2 * seedCost a R r.2.2.1.1 : ℕ) : ENNReal) := by
          simp only [genCharge]
          rw [if_pos hm.1, mul_one]
        rw [hgc]
        exact_mod_cast hch
      · rw [if_neg hm, mul_zero]
        exact bot_le
    · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]

/-! ### Couplings with the reference experiment (seed frozen at `ovSeed`) -/

theorem contactAt_ov_fill (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
    (trace : List Entry) :
    ContactAt (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) trace a ↔
      ContactAt (fillTable a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) trace a := by
  have hd : depth (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a = RawPrefix.restDepth a R := by
    unfold depth
    rw [depth_eq (referenceInputs_subset adversary) _ a ha, ← RawPrefix.restDepth_eq, RawPrefix.restDepth_ov]
  apply contactAt_congr trace a (hd.trans (fillTable_depth a ha R _).symm)
  unfold frontierValue fillTable
  rw [frontier_eq (referenceInputs_subset adversary) _ a ha, frontier_eq (referenceInputs_subset adversary) _ a ha,
    RawPrefix.frontierValue_ov (referenceInputs_subset adversary)]
  unfold RawPrefix.fill
  rw [RawPrefix.frontierValue_ov (referenceInputs_subset adversary)]
  exact (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.evaluate_fill _ _ _).symm

section Couple
variable (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (Stop : Answers → List Entry → Prop)
  (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) (R : Tables (PairedReference.referenceInputs adversary))
  (x : Hidden (RawPrefix.restDepth a R))
  (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
  (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
    (restartGame adversary q a Stop R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support)
include ha hmask in
theorem blind_frozen (trace : List Entry) :
    Stop (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) trace ↔ stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)) trace := by
  show _ ↔ Stop (fillTable a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) trace
  rw [← hmask]
  change Stop (CanonicalRef.maskAt _ (sourceMessages _) a) trace ↔ _
  rw [Normalized.maskAt_ov_fill (referenceInputs_subset adversary) a ha.1 (Core.sourceLeaf_leaf_lt ha.1) R x]
  exact hmask _ trace
include ha hmask hres
theorem cas_coupled :
    ContactAfterStop Stop (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        (traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2) a ↔
      genCAS Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres
  have hc := coupled_contact q a ha.1 R x (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres
  unfold ContactAfterStop genCAS
  simp only [blind_frozen a ha Stop hmask R x, contactAt_ov_fill a ha.1 R x]
  rw [first_stop_iff (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))
    (fun trace => ContactAt (fillTable a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) trace a)
    h1 h2 h3 (fun j k hjk h => contactAt_take_mono _ _ a hjk h)]
  rw [← contactAt_ov_fill a ha.1 R x (traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2), hc]
theorem stop_coupled :
    (∃ k, Stop (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        ((traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2).take k)) ↔
      genStop Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres
  simp only [blind_frozen a ha Stop hmask R x]
  exact first_stop_exists_iff _ h1 h2 h3
theorem charge_coupled :
    ((2 * prefixCount a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) : ℕ) : ENNReal) *
        (if ∃ k, Stop (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
          ((traceOf (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2.2).take k) then 1 else 0) =
      genCharge Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res) := by
  have hview := sampleView_coupled adversary q a R ha.1 x (res.1.2, res.2)
    (coupled_paused_rows q a R x (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres)
  have hcount : prefixCount a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 :=
    congrArg PrefixView.count hview
  have hstop := stop_coupled q a ha Stop hmask R x res hres
  unfold genCharge
  rw [hcount]
  by_cases hs : stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)) res.1.1
  · rw [if_pos (hstop.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hstop.mp h)), if_neg hs]
end Couple


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafRestart ====
section

/-! # Restart bounds for lower source chains (campaign X1 stage B, step B3)

`WotsRestart` bounds a first contact after a stop for top source chains, whose seeds are uniform. For lower source
chains (seeds = degree-16 family evaluations) the same bounds hold up to the seed-test error `(2^128 + 2q) · errC a`
(`lower_contactAfterStop_le`, `lower_contactAfterStop_charge`), for stops that are invariant under the leaf
congruence of the chain's leaf (contacts of source chains and markers are, `contactAt_leafCongr`,
`markerAt_leafCongr`). The combined statements for all source chains are `source_contactAfterStop_le` and
`source_contactAfterStop_charge`. -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsLeafRestart : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
open SphincsSecurity.QueryCap (recorded counted calls)
open ClaudeWCT.Arith.SideChannel (seedsR)
open ClaudeWCT.W9.T3.Security.Wots.PrefixGame (restartGame genCAS genStop genCharge stopAt restart_le_R
  charge_le_R cas_coupled stop_coupled restartGame_snd)
variable {adversary : AdversaryP}

theorem source_bounds {b : ChainAddr} (hb : WotsExtract.SourceChain b) :
    b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24 := by
  refine ⟨by have := hb.1.1; omega, ?_⟩
  have h1 := hb.1.2
  have h2 : 2 ^ height b.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
    have := SigGolfCandidate.T3.Security.Wots.height_le b.key.lay; omega)
  omega

/-! ### Contacts and markers under leaf congruence -/

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : LeafCongr L T T') (hLleaf : L.leaf < 2 ^ 24)
  (hLtree : L.tree < 2 ^ 40)
include hC hLleaf

end Congr

/-! ### The paused reference game as an honest body -/

/-- The paused reference game of a table (the honest body of `restartGame`). -/
noncomputable def GDr (adversary : AdversaryP) (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    OracleComp RefWorld (List Entry × SeedResult) :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull (Stop T) (referenceGame T adversary q) []

theorem GDr_snd (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    Prod.snd <$> GDr adversary q Stop T = GDseed adversary q T :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull_snd _ _ _

theorem gameD_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary) :
    gameD a (restDepth a R) R (GDr adversary q Stop) = restartGame adversary q a Stop R := by
  funext e
  rfl

theorem mixLaw_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary) :
    mixLaw a (restDepth a R) R (GDr adversary q Stop) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) := by
  unfold mixLaw
  rw [gameD_restart]

theorem restart_real_cost (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest)))
    (hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
      (fun _ _ => none)).support) : seedCost a R r.2.1.2 ≤ q := by
  have h := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_map
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
    (fun _ => Prod.snd) (fun _ _ => none)
  simp only [restartGame_snd] at h
  have hm : (r.1, r.2.1.2, r.2.2) ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (seedGame adversary q a R) (fun _ _ => none)).support := by
    rw [h, PMF.mem_support_map_iff]
    exact ⟨r, hr, rfl⟩
  exact seedGame_real_cost adversary q a R _ hm

/-! ### Lower chains -/

section Restart
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', LeafCongr a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)

/-- The stop-then-contact event of the prefix-game run at depth `d`. -/
def casD (Stop : Answers → List Entry → Prop) (a : ChainAddr) (d : ℕ) (R : RefTables adversary)
    (z : Digest × ((List Entry × SeedResult) × TObs d)) : Prop :=
  Stop (PrefixGame.fillTable a R z.1) z.2.1.1 ∧ ¬ContactAt (PrefixGame.fillTable a R z.1) z.2.1.1 a ∧
    Contact z.2.2 z.1

/-! ### The charge, by layers -/

theorem calls_pos_depth {d : ℕ} {qs : List RefWorld.Domain} (h : 0 < calls (PrefixGame.PrefixQuery a d) qs) :
    1 ≤ d := by
  cases d with
  | zero => rw [calls_prefixQuery_zero] at h; omega
  | succ d => omega

theorem count_coupled (R : RefTables adversary) (x : Hidden (restDepth a R))
    (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (restartGame adversary q a Stop R (evaluate x.1 (PrefixGame.ovSeed a R x.2))) (fun _ _ => none)).support) :
    prefixCount a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2)
    (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.coupled_paused_rows q a R x
      (stopAt Stop a R (evaluate x.1 (PrefixGame.ovSeed a R x.2))) res hres)
  exact congrArg PrefixView.count hview

theorem lt_ite_iff (k n : ℕ) (P : Prop) [Decidable P] : k < (if P then n else 0) ↔ k < n ∧ P := by
  split_ifs with h
  · exact ⟨fun hk => ⟨hk, h⟩, And.left⟩
  · exact ⟨fun hk => absurd hk (Nat.not_lt_zero k), fun hk => absurd hk.2 h⟩

end Restart

/-! ### All source chains -/

section Source
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', LeafCongr a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)
include ha hmask hStopL

end Source

/-! ### Size of the total seed-test error -/

theorem kconst_le (q : ℕ) : (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) ≤ 5 * (q : ℝ) ^ 2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q : ℝ)]

theorem card_digest_real : (Fintype.card Digest : ℝ) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  push_cast
  ring

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

/-!
# Regrouped seed-test scalar budget

A pair family has 86 real chains rather than the current maximum 54. The
existing 0.351 quadratic bound cannot simply be kept for this new charge.
These are scalar bounds on the proposed charge, not a proof that the
unchanged reference experiment or errTot has been correctly regrouped.
-/
namespace ClaudeWCT.W9.T3.Security.Wots.AdjacentLeafResearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Bound the actual existing side-channel error constant against an 86q
charge, on a slightly smaller small-route window. -/
theorem regrouped_seed_charge_le (q : ℕ) (hs : q ≤ 2710 * 2 ^ 106) :
    ENNReal.ofReal (Leaf.errConst q) * (86 * q) ≤
      (557 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  set t : ℝ := ((2 : ℝ) ^ 128)⁻¹ * q with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 2710 / 2 ^ 22 := by
    rw [ht, inv_mul_le_iff₀ (by positivity)]
    have : (q : ℝ) ≤ 2710 * 2 ^ 106 := by exact_mod_cast hs
    linarith
  have hpos : 0 < 1-t := by linarith
  have hconst : Leaf.errConst q =
      2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q / (1-t) := by
    unfold Leaf.errConst
    rw [Leaf.card_digest_real]
  have hc0 : 0 ≤ Leaf.errConst q := by rw [hconst]; positivity
  have hr : Leaf.errConst q * (86*q) ≤ 557/1000 * ((q : ℝ)/2^128)^2 := by
    rw [hconst,div_mul_eq_mul_div,div_le_iff₀ hpos]
    have hk := Leaf.kconst_le q
    calc 2 * ((2 : ℝ)^128)⁻¹^3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) * (86*q)
        ≤ 2 * ((2 : ℝ)^128)⁻¹^3 * (5*(q : ℝ)^2) * (86*q) := by gcongr
      _ = 860*t^3 := by rw [ht]; ring
      _ ≤ 557/1000*t^2*(1-t) := by
        have h1 : 0 ≤ 557/1000-860557/1000*t := by
          have : (860557/1000 : ℝ)*(2710/2^22) ≤ 557/1000 := by norm_num
          nlinarith
        nlinarith [mul_nonneg (sq_nonneg t) h1]
      _ = 557/1000*((q : ℝ)/2^128)^2*(1-t) := by rw [ht]; ring
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc0,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  exact hr

/-- Direct conditional use: the regrouped errTot must first be proved
bounded by this 86q charge. No such hypothesis is asserted for old errTot. -/
theorem regrouped_seed_error_le {err : ENNReal} (q : ℕ) (hs : q ≤ 2710*2^106)
    (hcharge : err ≤ ENNReal.ofReal (Leaf.errConst q) * (86*q)) :
    err ≤ (557/1000 : ENNReal)*((q : ENNReal)/2^128)^2 :=
  hcharge.trans (regrouped_seed_charge_le q hs)

end ClaudeWCT.W9.T3.Security.Wots.AdjacentLeafResearch

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem source_bounds {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24 := by
  refine ⟨by have := hb.1.tree_lt; omega, ?_⟩
  have h1 := hb.1.2
  have h2 : 2 ^ height b.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
    have := SigGolfCandidate.T3.Security.Wots.height_le b.key.lay; omega)
  omega

/-! ### Contacts and markers under leaf congruence -/

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : CanonicalRef.Leaf.Congr (sourceMessages T) L T T') (hLleaf : L.leaf < 2 ^ 24)
  (hLtree : L.tree < 2 ^ 40)
include hC hLleaf

end Congr


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
noncomputable def GDr (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    OracleComp RefWorld (List Entry × SeedResult) :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull (Stop T) (PairedReference.referenceGame T adversary q) []

theorem GDr_snd (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    Prod.snd <$> GDr adversary q Stop T = Core.GDseed adversary q T :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull_snd _ _ _

theorem gameD_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (GDr adversary q Stop) = restartGame adversary q a Stop R := by
  funext e
  rfl

theorem mixLaw_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (GDr adversary q Stop) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) := by
  unfold Core.mixLaw
  rw [gameD_restart]

theorem restart_real_cost (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)))
    (hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
      (fun _ _ => none)).support) : seedCost a R r.2.1.2 ≤ q := by
  have h := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_map
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
    (fun _ => Prod.snd) (fun _ _ => none)
  simp only [restartGame_snd] at h
  have hm : (r.1, r.2.1.2, r.2.2) ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)).support := by
    rw [h, PMF.mem_support_map_iff]
    exact ⟨r, hr, rfl⟩
  exact seedGame_real_cost (referenceInputs_subset adversary) adversary q a R _ hm

/-! ### Lower chains -/

section Restart
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)

/-- The stop-then-contact event of the prefix-game run at depth `d`. -/
def casD (Stop : Answers → List Entry → Prop) (a : ChainAddr) (d : ℕ) (R : Tables (PairedReference.referenceInputs adversary))
    (z : Digest × ((List Entry × SeedResult) × TObs d)) : Prop :=
  Stop (fillTable a R z.1) z.2.1.1 ∧ ¬ContactAt (fillTable a R z.1) z.2.1.1 a ∧
    Contact z.2.2 z.1

/-! ### The charge, by layers -/

theorem calls_pos_depth {d : ℕ} {qs : List RefWorld.Domain} (h : 0 < calls (PrefixGame.PrefixQuery a d) qs) :
    1 ≤ d := by
  cases d with
  | zero => rw [calls_prefixQuery_zero] at h; omega
  | succ d => omega

include ha in
theorem count_coupled (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
    (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (restartGame adversary q a Stop R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    prefixCount a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 := by
  have hview := sampleView_coupled adversary q a R ha.1 x (res.1.2, res.2)
    (coupled_paused_rows q a R x
      (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres)
  exact congrArg PrefixView.count hview

theorem lt_ite_iff (k n : ℕ) (P : Prop) [Decidable P] : k < (if P then n else 0) ↔ k < n ∧ P := by
  split_ifs with h
  · exact ⟨fun hk => ⟨hk, h⟩, And.left⟩
  · exact ⟨fun hk => absurd hk (Nat.not_lt_zero k), fun hk => absurd hk.2 h⟩

end Restart

/-! ### All source chains -/

section Source
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)
include ha hmask hStopL

end Source


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
def MarkerAt (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  CanonicalRef.MarkerAt T (sourceMessages T) trace a

theorem markerAt_maskAt (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hal : Wots.Mask.MaskOK a) : MarkerAt (maskAt T a) trace a ↔ MarkerAt T trace a := by
  unfold MarkerAt CanonicalRef.MarkerAt maskAt
  simp only [CanonicalRef.referenceInput, CanonicalRef.referenceDigits]
  rw [CanonicalRef.referenceSearch_source_maskAt T a hal,
    CanonicalRef.sourceMessages_maskAt T _ a hal]

theorem markerAt_take_exists (T : Answers) (trace : List Entry) (a : ChainAddr) :
    (∃ k, MarkerAt T (trace.take k) a) ↔ MarkerAt T trace a := by
  constructor
  · rintro ⟨k, message, counter, pad, answer, digits, hfit, hm, h⟩
    exact ⟨message, counter, pad, answer, digits, hfit, List.mem_of_mem_take hm, h⟩
  · intro h
    exact ⟨trace.length, by rw [List.take_length]; exact h⟩

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsClasses ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRowW (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRowW a s v) = bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  WCT9.chainInputW_header _ _ _ _ _ _
theorem posOf_chainRow (a : ChainAddr) (s : Nat) (v : Digest) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 4096) (hc : a.chain < 64) (hs : s < 7) :
    Extract.posOf (chainRowW a s v) = some (.chain a.key.lay a.key.tree a.key.leaf a.chain s) :=
  Extract.posOf_eq ⟨htree, hleaf, hc, hs⟩ (chainRowW_length a s v)
    (hdrBlock_chainRowW a s v)
/-- Pairing stage 1: no chain row of the current scheme (F or G) is a digest query (header block). -/
theorem chainRowW_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRowW a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRowW] at hb
  change _ = SigGolfCandidate.T3M.Extract.hdrBlock _ at hb
  rw [SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest] at hb
  exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hb)
end SmallA
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
namespace SmallA
theorem chainRowW_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRowW a s v ≠ encRow L m c pad := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h1 : ClaudeWCT.W9.T3M.Extract.hdrBlock (chainRowW a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
    hdrBlock_chainRowW a s v
  rw [h1, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker] at hm
  have := chainHeader_firstByte a.key.lay a.key.tree a.key.leaf a.chain s
  unfold tweakMarker at hm
  omega
theorem encRow_ne_digest (L : LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : RowPad) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (digestHeader c') :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker, digestHeader_marker] at hm
  exact absurd hm (by decide)
end SmallA
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
    have h7 := Mask.depth_le_seven T a
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change OtherChainRow T (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent PrefixRow := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [PrefixRow, PrefixRowAt, hdepth]
  · exact Iff.rfl
theorem shortCongruent_otherQuery : ShortCongruent OtherQuery := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  have hcls : ∀ x p, StructuralClass A x p ↔ StructuralClass T x p := by
    intro x p
    cases p <;> simp only [StructuralClass, OtherChainRow, hdepth]
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [OtherQuery, OtherInput, hcls]
  · exact Iff.rfl
noncomputable def refExpect (adversary : AdversaryP) (q : Nat) (f : RefSample → Nat) : ENNReal :=
  ∑' s, referenceExperiment adversary q s * (f s : ENNReal)
theorem reference_class_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    refExpect adversary q prefixClassCount + refExpect adversary q encodingCount + refExpect adversary q otherCount +
      SeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow shortCongruent_otherQuery prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input => prefixRow_digest_disjoint z.2 input)
    (fun z input => encodingRow_digest_disjoint z.2 input) (fun z input => otherQuery_digest_disjoint z.2 input)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    have hlegacy : SigGolfCandidate.T3.Security.WotsExtract.SourceChain a := ⟨⟨ha.1.tree_lt,ha.1.2⟩,ha.2⟩
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds hlegacy
    have h7 := (CanonicalRef.depth_le T (CanonicalRef.sourceMessages T) a ha.2).trans
      (SigGolfCandidate.T3.Security.Wots.Mask.width_le _ _)
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change CanonicalRef.OtherChainRow T (CanonicalRef.sourceMessages T) (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent CanonicalRef.Normalized.Contacts.PrefixRow := by
  intro A T hAT input
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) = CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [CanonicalRef.Normalized.Contacts.PrefixRow, CanonicalRef.Normalized.PrefixRowAt, hdepth]
  · exact Iff.rfl

def digestClass : PairedSeccLaw.SampleClass := fun _ input=>IsDigestQuery input
theorem sample_class_budget (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) :
    PairedSeccLaw.sampleCharge (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>EncodingRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>OtherQuery z.2 input) q z +
    PairedSeccLaw.sampleCharge digestClass q z ≤ q := by
  let A := CanonicalRef.Normalized.Contacts.PrefixRow z.2
  let B := EncodingRow z.2
  let C := OtherQuery z.2
  let D := IsDigestQuery
  have hab : ∀input,¬(A input ∧ B input) := prefixRow_encodingRow_disjoint z.2
  have hac : ∀input,¬(A input ∧ C input) := prefixRow_otherQuery_disjoint z.2
  have had : ∀input,¬(A input ∧ D input) := prefixRow_digest_disjoint z.2
  have hbc : ∀input,¬(B input ∧ C input) := encodingRow_otherQuery_disjoint z.2
  have hbd : ∀input,¬(B input ∧ D input) := encodingRow_digest_disjoint z.2
  have hcd : ∀input,¬(C input ∧ D input) := otherQuery_digest_disjoint z.2
  have h1 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or A B hab q (QueryRecorded.recordedTrace z.1).events
  have h2 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>A input ∨ B input) C
    (fun input h=>h.1.elim (fun ha=>hac input ⟨ha,h.2⟩) (fun hb=>hbc input ⟨hb,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have h3 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>(A input ∨ B input) ∨ C input) D
    (fun input h=>h.1.elim (fun h'=>h'.elim (fun ha=>had input ⟨ha,h.2⟩)
      (fun hb=>hbd input ⟨hb,h.2⟩)) (fun hc=>hcd input ⟨hc,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have hle := SigGolfCandidate.T3.Security.SeccLaw.classCharge_le (fun input=>((A input ∨ B input) ∨ C input) ∨ D input) q
    (QueryRecorded.recordedTrace z.1).events
  change SigGolfCandidate.T3.Security.SeccLaw.classCharge A q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge B q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge C q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge D q _ ≤ q
  omega

noncomputable def refExpect (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (f : RefSample → Nat) : ENNReal := ∑'s,referenceExperiment adversary q s*(f s : ENNReal)

theorem prefix_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) :=
  reference_count_le adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow shortCongruent_prefixRow

theorem encoding_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q encodingCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>EncodingRow z.2 input) :=
  reference_count_le adversary q hq EncodingRow shortCongruent_encodingRow

theorem other_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q otherCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>OtherQuery z.2 input) :=
  reference_count_le adversary q hq OtherQuery otherQuery_short

theorem reference_class_budget (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount+refExpect adversary q encodingCount+refExpect adversary q otherCount+
      PairedSeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow otherQuery_short prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input=>prefixRow_digest_disjoint z.2 input)
    (fun z input=>encodingRow_digest_disjoint z.2 input) (fun z input=>otherQuery_digest_disjoint z.2 input)

end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
end
-- ==== merged from T3_Secc_WotsEncodingE1 ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem tsum_uniform_prod {α β : Type} {iP : Fintype (α × β)} [Nonempty (α × β)] (iA : Fintype α) (iB : Fintype β)
    [Nonempty α] [Nonempty β] (G : α × β → ENNReal) :
    ∑' R, @PMF.uniformOfFintype (α × β) iP _ R * G R =
      ∑' a, @PMF.uniformOfFintype α iA _ a * ∑' b, @PMF.uniformOfFintype β iB _ b * G (a, b) := by
  obtain rfl : iP = @instFintypeProd α β iA iB := Subsingleton.elim _ _
  rw [ENNReal.tsum_prod (f := fun a b => @PMF.uniformOfFintype (α × β) (@instFintypeProd α β iA iB) _ (a, b) *
    G (a, b))]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (by simp) (by simp), mul_assoc]
theorem weighted_le {α : Type} (μ : α → ENNReal) (left right : α → ENNReal) (rate : ENNReal)
    (h : ∀ x, left x ≤ rate * right x) : ∑' x, μ x * left x ≤ rate * ∑' x, μ x * right x := by
  calc _ ≤ ∑' x, μ x * (rate * right x) := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => mul_left_comm _ _ _
end Assembly
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsEncodingMarker ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
theorem unit_neighbors_le_53 (lay : Layer) (word : Encoding lay) (i : ChainIndex lay) :
    (MixedCode.unitNeighbors word i).card ≤ 53 :=
  (MixedCode.unitNeighbors_card_le word i).trans (Nat.sub_le_sub_right (chainCount_le_54 lay) 1)
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsEncodingContact ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card
theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingE1 ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem restTable_pair (p : FullGame.FullTable) (x : referenceInputs adversary → HashOutput) :
    restTable ((p, x) : RefTables adversary) = eagerAnswers (referenceInputs adversary) p x := by
  rw [restTable]
theorem reference_free_le (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (f g : RefSample → ENNReal)
    (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : referenceInputs adversary → HashOutput),
      ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) → HashOutput)
          (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          f (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r) ≤
      rate * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) →
          HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          g (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r)) :
    ∑' s, referenceExperiment adversary q s * f s ≤ rate * ∑' s, referenceExperiment adversary q s * g s := by
  rw [reference_eq_bind, tsum_bind_mul, tsum_bind_mul]
  simp only [tsum_map_mul]
  unfold restLaw
  have iF : Fintype FullGame.FullTable := by unfold FullGame.FullTable; exact Pi.instFintype
  have iU : Fintype (referenceInputs adversary → HashOutput) := Pi.instFintype
  rw [tsum_uniform_prod iF iU, tsum_uniform_prod iF iU]
  simp only [restTable_pair]
  refine weighted_le _ _ _ _ fun privateTable => ?_
  have hU := publicUniverse_sub adversary
  rw [@public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r)),
    @public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r))]
  refine weighted_le _ _ _ _ fun pub => ?_
  exact hfg privateTable pub
theorem reference_cells_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (f g : RefSample → ENNReal) (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : referenceInputs adversary → HashOutput),
      ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          f (mkSample (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) r) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          g (mkSample (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) r)) :
    ∑' s, referenceExperiment adversary q s * f s ≤ rate * ∑' s, referenceExperiment adversary q s * g s := by
  rw [reference_eq_bind, tsum_bind_mul, tsum_bind_mul]
  simp only [tsum_map_mul]
  unfold restLaw
  have iF : Fintype FullGame.FullTable := by unfold FullGame.FullTable; exact Pi.instFintype
  have iU : Fintype (referenceInputs adversary → HashOutput) := Pi.instFintype
  rw [tsum_uniform_prod iF iU, tsum_uniform_prod iF iU]
  simp only [restTable_pair]
  refine weighted_le _ _ _ _ fun privateTable => ?_
  have hU := publicUniverse_sub adversary
  rw [@public_resample_cells (referenceInputs adversary) _ _ iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r)),
    @public_resample_cells (referenceInputs adversary) _ _ iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r))]
  refine weighted_le _ _ _ _ fun pub => ?_
  exact hfg privateTable pub
theorem reference_matchInd_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) :
    ∑' s, referenceExperiment adversary q s * matchInd s ≤
      (7 / ((4 : ENNReal) * 2^128)) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) :=
  reference_free_le adversary q iX matchInd (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => free_match_le adversary q iX (referenceInputs adversary)
      (publicUniverse_sub adversary) privateTable pub)
end Assembly
end Enc
open Enc in
theorem reference_encodingMatch_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf7 L ∧ EncodingMatchAt s.answers s.trace L |
        referenceExperiment adversary q] ≤
      (7 / ((4 : ENNReal) * 2^128)) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  refine le_trans ?_ (Enc.reference_matchInd_le adversary q (fun k => Pi.instFintype))
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun s => ?_
  split_ifs with h
  · obtain ⟨L, h7, hm⟩ := h
    have ht31 : L.tree < 2 ^ 31 := lt_of_lt_of_le h7.1
      (Nat.pow_le_pow_right (by decide) (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
    have hpos : ∃ L' : CanonGraph.LeafPos, L'.Source ∧ EncodingMatchAt s.answers s.trace (Enc.leafOf L') := by
      refine ⟨⟨L.lay, ⟨L.tree, ht31⟩, ⟨L.leaf, lt_of_lt_of_le h7.2 ?_⟩⟩, h7, hm⟩
      calc 2 ^ height L.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le L.lay)
        _ = 4096 := by norm_num
    rw [Enc.matchInd, if_pos hpos, mul_one, PMF.probOutput_eq_apply]
  · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput

theorem reference_expectation (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (f : RefSample → ENNReal) :
    ∑' s, PairedReference.referenceExperiment adversary q s * f s =
      ∑' privateTable, PMF.uniformOfFintype FullGame.FullTable privateTable *
        ∑' pub, PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput) pub *
          ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary)
            privateTable pub) adversary q) : PMF SeedResult) r *
            f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r) := by
  have heq : PairedReference.referenceExperiment adversary q =
      (PMF.uniformOfFintype FullGame.FullTable).bind (fun privateTable =>
        (PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput)).bind (fun pub =>
          (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary)
            privateTable pub) adversary q) : PMF SeedResult).map
              (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))) := by
    unfold PairedReference.referenceExperiment PairedReference.referenceComp
    rw [liftM_bind, PrefixGame.liftM_uniform]
    simp only [liftM_bind, PrefixGame.liftM_uniform,liftM_map]
    rfl
  rw [heq,tsum_bind_mul]
  apply tsum_congr
  intro privateTable
  rw [tsum_bind_mul]
  apply congrArg
  apply tsum_congr
  intro pub
  rw [tsum_map_mul]


theorem reference_cells_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (f g : RefSample → ENNReal) (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : PairedReference.referenceInputs adversary → HashOutput),
      ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey
          (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
          (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) r) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey
          (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
          (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          g (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) r)) :
    ∑' s, PairedReference.referenceExperiment adversary q s * f s ≤
      rate * ∑' s, PairedReference.referenceExperiment adversary q s * g s := by
  rw [reference_expectation, reference_expectation]
  apply SigGolfCandidate.T3.Security.Wots.Enc.weighted_le
  intro privateTable
  have hU : SeccLaw.publicUniverse ⊆ PairedReference.referenceInputs adversary := Finset.subset_union_left
  rw [public_resample_source hU privateTable
      (fun pub => ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r)),
    public_resample_source hU privateTable
      (fun pub => ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r))]
  exact SigGolfCandidate.T3.Security.Wots.Enc.weighted_le _ _ _ _ (hfg privateTable)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingMarker ====
section
-- serialization only (no declarations used): keeps this ~9 GB-private module from building in parallel with WotsLeafSum under the verifier's 2-job / 24 GiB limit



namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
theorem uniform_unit_neighbors (lay : Layer) (W : Encoding lay) (i : ChainIndex lay) :
    Pr[fun ans => ∃ high : Bool, ClaudeWCT.WCT9.verificationAnswer lay high ans ∈
      EncodingTargets.targets lay (MixedCode.unitNeighbors W i) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (371 / 4) / (2 : ENNReal)^128 := by
  classical
  let targets := EncodingTargets.targets lay (MixedCode.unitNeighbors W i)
  have hc : targets.card ≤ chainCount lay - 1 :=
    (EncodingTargets.targets_card _ _).trans (MixedCode.unitNeighbors_card_le W i)
  have hn : targets.card ≤ 53 := by
    have hmax : chainCount lay ≤ 54 := by fin_cases lay <;> decide +kernel
    omega
  have hp : lay ≠ 0 → ∀ d, d ∈ targets → lowerSpare d := by
    intro hl d hd
    obtain ⟨word, _, hword⟩ := (EncodingTargets.mem_targets _ _ _).mp hd
    exact decode_lowerSpare hl hword
  calc _ ≤ (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2^128)) :=
        ClaudeWCT.WCT9.probability_verification_exists_le lay targets hp
    _ ≤ 53 * (7 / ((4 : ENNReal) * 2^128)) := mul_le_mul' (by exact_mod_cast hn) le_rfl
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      norm_num
end Enc
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
/-- Both halves of a uniform answer, counted separately (kept outside the `irreducible Finset.univ` section). -/
theorem halves_card (p : Digest → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 0 128)).card +
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 128 128)).card =
      (Finset.univ.filter p).card * (2*2^128) := by
  have hl := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide) p
  have hh := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide) p
  dsimp only [Nat.reduceSub] at hl hh
  rw [hl, hh]
  ring

theorem encoding_broad (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card * (2*2^128) := by
  have hsub : (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome) ⊆
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 0 128)).isSome) ∪
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 128 128)).isSome) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at ha ⊢
    rw [encodingAnswer_eq] at ha
    split_ifs at ha
    · exact Or.inl ha
    · exact Or.inr ha
  have hh := halves_card (fun d : Digest => (decode lay d).isSome = true)
  exact le_trans (Finset.card_le_card hsub) ((Finset.card_union_le _ _).trans hh.le)
end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false
attribute [local irreducible] Finset.univ Finset.filter
def broadCount (lay : Layer) : Nat :=
  (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card

theorem broad_decoder_card (lay : Layer) : broadCount lay =
    (if lay=0 then SigGolfResearch.NonbinaryTop.Counting.count else EncodingCounting.rawAcceptedCount lay) := by
  unfold broadCount
  rw [← Fintype.card_subtype]
  by_cases hl : lay=0
  · subst lay
    exact Nonbinary.actual_decoder_count
  · rw [Fintype.card_congr (EncodingCounting.acceptedDigestEquiv lay hl), EncodingCounting.accepted_words_count]
    exact (if_neg hl).symm

/-- Crude union bound (both halves): enough for the 1000/1001 rejection estimate. -/
theorem broad_encoding_card (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      broadCount lay * (2*2^128) := by
  simpa only [broadCount] using encoding_broad lay


theorem encodingAnswer_normal (lay : Layer) (a : HashOutput) :
    encodingAnswer (CanonicalPolicy.normalLayer lay) a=encodingAnswer lay a := by
  fin_cases lay <;> rfl

theorem verificationAnswer_normal (lay : Layer) (high : Bool) (a : HashOutput) :
    verificationAnswer (CanonicalPolicy.normalLayer lay) high a=verificationAnswer lay high a := by
  fin_cases lay <;> rfl

theorem producer_rejection_broad (lay : Layer) (floor : Nat) :
    1000*2^256 ≤ 1001*(Finset.univ.filter fun a : HashOutput =>
      CanonicalPolicy.producerDecodeOut lay floor a=none).card := by
  classical
  let accepted := Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a ≠ none
  let broad := Finset.univ.filter fun a : HashOutput =>
    (SigGolfCandidate.T3.decode (CanonicalPolicy.normalLayer lay) (encodingAnswer (CanonicalPolicy.normalLayer lay) a)).isSome
  have hsub : accepted ⊆ broad := by
    intro a ha
    obtain ⟨⟨ds,low⟩,hds⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Option.isSome_iff_exists.mpr ⟨ds,?_⟩⟩
    rw [encodingAnswer_normal]
    exact (CanonicalPolicy.producerDecodeAt_spec (CanonicalPolicy.producerDecodeOut_spec hds).2).1
  have hbound : accepted.card ≤ broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128) :=
    (Finset.card_le_card hsub).trans (broad_encoding_card _)
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset HashOutput))
    (fun a => CanonicalPolicy.producerDecodeOut lay floor a = none)
  simp only [Finset.card_univ, Fintype.card_bitVec] at hpart
  change (Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a=none).card + accepted.card = 2^256 at hpart
  have hsmall : 1001 * (broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128)) ≤ 2^256 := by
    rw [broad_decoder_card]
    fin_cases lay <;> norm_num [CanonicalPolicy.normalLayer, EncodingCounting.rawAcceptedCount, SigGolfResearch.NonbinaryTop.Counting.count]
  omega

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def UnitNeighborDecode (lay : Layer) (reference : List Nat) (chain : Nat) (output : HashOutput) : Prop :=
  ∃ digits, encodingCanDecode lay output digits ∧
    digits.getD chain 0+1=reference.getD chain 0 ∧
    ∀ j, j ≠ chain → reference.getD j 0 ≤ digits.getD j 0

theorem marker_uniform_raw (lay : Layer) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  classical
  let normal := CanonicalPolicy.normalLayer lay
  have href' : decode normal value=some reference := href
  by_cases hc : chain<chainCount normal
  · let W := decodedWord href'
    let i : Fin (MixedCode.Code.n (code normal)) := ⟨chain,hc⟩
    let targets := EncodingTargets.targets normal (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => ∃ high : Bool, verificationAnswer normal high output∈targets |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro answer - ⟨digits,⟨high,hd⟩,hlow,hrest⟩
          refine ⟨high, ?_⟩
          have hd' : decode normal (verificationAnswer normal high answer)=some digits := by
            rw [verificationAnswer_normal]
            exact hd
          refine (EncodingTargets.source_decoded_target hd' _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid href',decodedWord_valid hd',hlow,?_⟩
          intro j hj
          exact hrest j.val (fun he=>hj (Fin.ext he))
      _ ≤ _ := ClaudeWCT.W9.T3.Security.Wots.Enc.uniform_unit_neighbors normal W i
  · have hz : Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)]=0 := by
      apply probEvent_eq_zero
      rintro answer - ⟨digits,-,hlow,hrest⟩
      have hlen := (decode_length_sum href').1
      rw [List.getD_eq_default reference 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le


open SphincsSecurity.Concrete.UniformTableCompletion

noncomputable def rejectedAt (lay : Layer) (floor : Nat) : Finset HashOutput :=
  Finset.univ.filter fun a => CanonicalPolicy.producerDecodeOut lay floor a=none

theorem probEvent_rejected_le (lay : Layer) (floor : Nat) (p : HashOutput→Prop) :
    Pr[p | cell (rejectedAt lay floor)] ≤ 1001/1000*Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite,probEvent_eq_tsum_ite,←ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ans=>?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply,cell_apply,probOutput_uniformSample]
    split_ifs
    · have hc : ((1000:ENNReal)*2^256)≤1001*((rejectedAt lay floor).card:ENNReal) := by
        exact_mod_cast producer_rejection_broad lay floor
      calc ((rejectedAt lay floor).card:ENNReal)⁻¹ = 1001/(1001*((rejectedAt lay floor).card:ENNReal)) := by
            rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              mul_comm (1001:ENNReal)⁻¹,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),mul_one]
        _ ≤ 1001/(1000*2^256) := ENNReal.div_le_div_left hc _
        _ = 1001/1000*((Fintype.card HashOutput:Nat):ENNReal)⁻¹ := by
          simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
          rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),div_eq_mul_inv]
          ring
    · exact zero_le
  · simp

theorem marker_rejected_le (lay : Layer) (floor : Nat) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | cell (rejectedAt lay floor)] ≤ 93/(2:ENNReal)^128 := by
  calc _ ≤ 1001/1000*Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] :=
      probEvent_rejected_le _ _ _
    _ ≤ 1001/1000*((371/4)/(2:ENNReal)^128) := mul_le_mul' le_rfl (marker_uniform_raw lay reference value href chain)
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The LOW path bonus only helps: a word accepted through HIGH is accepted through LOW. -/
theorem producerDecodeAt_true_of_false {lay : Layer} {floor : Nat} {word : Digest} {digits : List Nat}
    (h : CanonicalPolicy.producerDecodeAt lay floor false word = some digits) :
    CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
  unfold CanonicalPolicy.producerDecodeAt at h ⊢
  cases hd : CanonicalPolicy.decode lay word with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h ⊢
      split_ifs at h with hc
      cases h
      have hb : ∀ d, CanonicalPolicy.pathReward lay false d ≤ CanonicalPolicy.pathReward lay true d := by
        intro d
        simp only [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false]
        omega
      rw [if_pos ⟨hc.1.trans (hb _), hc.2⟩]

/-- Path-aware rejected cell (both layer kinds; top bonus 3, lower bonus 4). Let `word` be accepted at `floor`
through some half, with digits `digits`. A rejected answer that still decodes to `digits` for some witness hint has
HIGH half `word`: if its LOW half were `word`, LOW would pass the producer predicate through the (better) LOW path
and the producer would have selected it (top: the producer prefers a good LOW; lower: the decodable LOW is spare). -/
theorem rejected_canDecode {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) {a : HashOutput}
    (hrej : CanonicalPolicy.producerDecodeOut lay floor a = none)
    (hdec : encodingCanDecode lay a digits) :
    a.extractLsb' 128 128 = word := by
  obtain ⟨high, hd⟩ := hdec
  have hword : verificationAnswer lay high a = word :=
    canonical_decode_injective hd (CanonicalPolicy.producerDecodeAt_spec href).1
  have hrej' : CanonicalPolicy.producerDecodeAt lay floor (lowSelected lay a) (encodingAnswer lay a) = none := by
    unfold CanonicalPolicy.producerDecodeOut at hrej
    simpa only [Option.map_eq_none_iff] using hrej
  have htrue : CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
    cases low
    · exact producerDecodeAt_true_of_false href
    · exact href
  have hlowne : a.extractLsb' 0 128 = word → False := by
    intro hlw
    have hsel : lowSelected lay a = true := by
      by_cases hl : lay = 0
      · subst hl
        have hf := hfloor rfl
        subst hf
        have hg : topGood (a.extractLsb' 0 128) := by
          unfold topGood
          rw [hlw, htrue]
          rfl
        simp only [lowSelected, if_true, topChooseLow, decide_eq_true_eq]
        exact Or.inl hg
      · have hdw := (CanonicalPolicy.producerDecodeAt_spec href).1
        simp only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] at hdw
        have hspare : lowerSpare (a.extractLsb' 0 128) := by
          rw [hlw]
          exact SigGolfCandidate.T3.decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hdw
        simp [lowSelected, hl, hspare]
    rw [encodingAnswer_eq, hsel, if_pos rfl, hlw, htrue] at hrej'
    cases hrej'
  by_cases hl : lay = 0
  · subst hl
    have hread : verificationAnswer 0 high a = TopChoice.read high a := rfl
    rw [hread] at hword
    unfold TopChoice.read at hword
    split_ifs at hword
    · exact hword
    · exact (hlowne hword).elim
  · rw [verificationAnswer_eq_lower lay hl, verificationLow_lower lay hl] at hword
    split_ifs at hword
    · exact (hlowne hword).elim
    · exact hword

/-- Rejected-cell match bound (path-aware floors): `(1001/1000)/2^128 ≤ (7/4)/2^128`. -/
theorem canDecode_rejected_le {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) :
    Pr[fun a => encodingCanDecode lay a digits | cell (rejectedAt lay floor)] ≤ 7/((4:ENNReal)*2^128) := by
  classical
  calc _ ≤ Pr[fun a : HashOutput => a.extractLsb' 128 128 = word | cell (rejectedAt lay floor)] := by
        apply probEvent_mono
        intro a ha hdec
        have hmem := SigGolfCandidate.T3.Security.Wots.Enc.Lazy.cell_nonzero_mem
          ((SPMF.mem_support_iff _ _).mp ha)
        have hrej : CanonicalPolicy.producerDecodeOut lay floor a = none := by
          simpa only [rejectedAt, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        exact rejected_canDecode hfloor href hrej hdec
    _ ≤ 1001/1000*Pr[fun a : HashOutput => a.extractLsb' 128 128 = word |
          ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_rejected_le _ _ _
    _ = 1001/1000*(1/(2:ENNReal)^128) := by
        congr 1
        rw [probEvent_uniformSample]
        have hc := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide)
          (fun v : BitVec 128 => v = word)
        have h1 : (Finset.univ.filter fun v : BitVec 128 => v = word).card = 1 := by
          rw [Finset.filter_eq' Finset.univ word]
          simp
        change (Finset.univ.filter fun a : HashOutput => a.extractLsb' 128 128 = word).card = _ at hc
        rw [hc, h1, Fintype.card_bitVec]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one]
        rw [show (2:ENNReal)^256 = 2^128*2^128 by rw [← pow_add], ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
          mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MarkEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) (digits : List Nat),
    Extract.msgFits a.key.lay message ∧ entry.1 = encRow a.key message counter pad ∧
      referenceInput T messages a.key ≠ some (encRow a.key message counter pad) ∧
      WCT9.encodingCanDecode a.key.lay entry.2 digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T messages a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T messages a.key).getD i 0 ≤ digits.getD i 0

theorem markerAt_iff (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T messages trace a ↔ ∃ entry ∈ trace, MarkEntry T messages a entry := by
  constructor
  · rintro ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩

theorem markEntry_cell_le_raw (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_uniform_raw a.key.lay
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      93/(2:ENNReal)^128 := by
  refine (markEntry_cell_le_raw T messages x a).trans (ENNReal.div_le_div_right ?_ _)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem markEntry_rejected_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) (remaining : Nat) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | cell (rejectedAnswers a.key.lay remaining)] ≤
      93/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_rejected_le a.key.lay
    (WCT9.CanonicalPolicy.threshold a.key.lay.val remaining)
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      93/(2:ENNReal)^128 := by
  by_cases hp : p.1=e.val.1.1
  · refine (probEvent_mono fun ans _ h => h.2).trans ?_
    unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le T messages _ _
    · split
      · rw [Lazy.probEvent_cell_univ]
        exact markEntry_cell_le T messages _ _
      · have h := markEntry_rejected_le T messages (Enc.encInput e.val) (Enc.chainAt p) ‹Nat›
        rw [show (Enc.chainAt p).key.lay=e.val.1.1.lay from by rw [←hp]; rfl] at h
        exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
    exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
      Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm

theorem markEntry_sum_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      5022/(2:ENNReal)^128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      if p.1=e.val.1.1 then (if p.2.val<54 then 93/(2:ENNReal)^128 else 0) else 0 := by
    intro p
    split_ifs with hp hc
    · exact markEntry_init_le T messages k e p
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsource,-⟩
      have hcount := chainCount_le_54 p.1.lay
      have hchain : p.2.val < chainCount p.1.lay := hsource.2
      omega
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
      exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
        Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans ?_
  rw [Fintype.sum_prod_type,Finset.sum_eq_single e.val.1.1 (fun L _ hL=>by simp [hL]) (by simp)]
  simp only [if_true]
  have hn : (Finset.univ.filter (fun i : Fin 58 => i.val<54)).card=54 := by decide
  rw [←Finset.sum_filter,Finset.sum_const,hn,nsmul_eq_mul,←mul_div_assoc]
  gcongr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem layerCounterSearch_first (T : Answers) (lay : Layer) (floor tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel start k (digits : List Nat × Bool), k<fuel →
      (∀i<k,WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+i)))))))=none) →
      WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+k)))))))=some digits →
      evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel)=
        some (BitVec.ofNat 32 (start+k),digits) := by
  intro fuel
  induction fuel with
  | zero => intro start k digits hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt,evalWithAnswerFn_bind,eval_publicHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have h := ih (start+1) k digits (by omega)
          (fun i hi=>by rw [show start+1+i=start+(i+1) by omega];exact hprev (i+1) (by omega))
          (by rw [show start+1+k=start+(k+1) by omega];exact hvalid)
        rw [show start+(k+1)=start+1+k by omega]
        exact h

theorem reached_valid_reference {T : Answers} {messages : LeafAddr→WCT9.LayerMsg}
    {L : LeafAddr} {input : HashInput} (hr : Reached T messages L input)
    {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {digits : List Nat × Bool}
    (hv : WCT9.CanonicalPolicy.producerDecodeOut L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr input)))=some digits) :
    referenceInput T messages L=some input := by
  obtain ⟨c,⟨hc,oldRemaining,hctx',hprev⟩,rfl⟩ := hr
  rw [hctx] at hctx'
  cases hctx'
  have hs : searchOf T messages L remaining=some (BitVec.ofNat 32 c,digits) := by
    unfold searchOf
    have h := layerCounterSearch_first T L.lay _ L.tree L.leaf (messages L)
      (WCT9.searchLimit L.lay) 0 c digits hc
      (fun i hi=>by rw [Nat.zero_add,←encRow_zero]; rw [←decodeRow_answer];exact hprev i hi)
      (by rw [Nat.zero_add,←encRow_zero];exact hv)
    simpa only [Nat.zero_add] using h
  have href : referenceSearch T messages L=some (BitVec.ofNat 32 c,digits) := by
    exact Option.bind_eq_some_iff.mpr ⟨remaining,hctx,hs⟩
  unfold referenceInput
  rw [href]
  rfl

theorem referenceInput_eq_of_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (L : CanonGraph.LeafPos) (hsource : L.Source) (message : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : RowPad) (hfit : Extract.msgFits L.lay message)
    (he : x=encRow (Enc.leafOf L) message counter pad) :
    referenceInput T messages (Enc.leafOf L)=some x := by
  let entry : Enc.EncIndex := Enc.encIdx L hsource message counter pad hfit
  have hin : Enc.encInput entry=x := (Enc.encInput_encIdx L hsource message counter pad hfit).trans he.symm
  have hleaf : Enc.leafOf entry.1.1=Enc.leafOf L := rfl
  have hnc : ¬(entry∈freeSet T messages ∨ entry∈rejectedSet T messages) :=
    fun hc=>hx ⟨entry,hc,hin⟩
  have hreached : Reached T messages (Enc.leafOf L) x := by
    by_contra hfree
    apply hnc
    left
    change ¬Reached T messages (Enc.leafOf entry.1.1) (Enc.encInput entry)
    rw [hin,hleaf]
    exact hfree
  obtain ⟨c,hreach,hxrow⟩ := hreached
  obtain ⟨hc,remaining,hctx,hprev⟩ := hreach
  cases hs : decodeRow T (Enc.leafOf L) (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (messages (Enc.leafOf L)) c with
  | none =>
      exact False.elim (hnc (Or.inr
        ⟨c,remaining,⟨hc,remaining,hctx,hprev⟩,hin.trans hxrow,hctx,hs⟩))
  | some ds =>
      have hvalid : WCT9.CanonicalPolicy.producerDecodeOut L.lay
          (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr x)))=some ds := by
        rw [decodeRow_answer,←hxrow] at hs
        exact hs
      have href := reached_valid_reference ⟨c,⟨hc,remaining,hctx,hprev⟩,hxrow⟩ hctx hvalid
      exact href


theorem markEntry_noncell (T : Answers) (messages : LeafAddr→WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (p : CanonGraph.LeafPos×Fin 58) :
    ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (x,T (.inl (.inr x)))) := by
  rintro ⟨hsrc,message,counter,pad,digits,hfit,he,hne,hdec,rest⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx p.1 hsrc.1
    message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MatchEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad),
    L.Source ∧ Extract.msgFits L.lay message ∧ entry.1 = encRow (Enc.leafOf L) message counter pad ∧
      referenceInput T messages (Enc.leafOf L) ≠ some (encRow (Enc.leafOf L) message counter pad) ∧
      referenceSearch T messages (Enc.leafOf L) ≠ none ∧
      WCT9.encodingCanDecode L.lay entry.2 (referenceDigits T messages (Enc.leafOf L))

theorem matchEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (e : Enc.EncIndex) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      7/((4:ENNReal)*2^128) := by
  apply le_trans (probEvent_mono ?_) (WCT9.probability_encodingCanDecode_le e.1.1.lay
    (referenceDigits T messages (Enc.leafOf e.1.1)))
  rintro answer - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs,hdec⟩
  have hL := Enc.encInput_leaf hsource he
  subst hL
  exact hdec

private theorem bind_at_some {α β : Type} (o : Option α) (f : α → Option β)
    {a : α} {b : β} (ho : o = some a) (h : o.bind f = some b) : f a = some b := by
  subst o
  exact h

theorem referenceSearch_producerDecode (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {c : BitVec 32} {digits : List Nat} {low : Bool} (hs : referenceSearch T messages L=some (c,digits,low)) :
    WCT9.CanonicalPolicy.producerDecodeOut L.lay (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (T (.inl (.inr (encRow L (messages L) c 0))))=some (digits,low) := by
  have hs' : searchOf T messages L remaining=some (c,digits,low) := by
    exact bind_at_some _ _ hctx hs
  have h := counterSearch_decode T L.lay _ L.tree L.leaf (messages L)
    (WCT9.searchLimit L.lay) 0 c (digits,low) hs'
  rw [eval_publicHash,←encRow_zero] at h
  exact h

/-- Path-aware floors: the reference word was accepted through the half the producer selected. -/
theorem reference_accepted (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    (hs : referenceSearch T messages L≠none) :
    ∃ (word : Digest) (low : Bool), WCT9.CanonicalPolicy.producerDecodeAt L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) low word=some (referenceDigits T messages L) := by
  obtain ⟨⟨c,digits,low⟩,hfound⟩ := Option.ne_none_iff_exists'.mp hs
  have href : referenceDigits T messages L=digits := by
    simp only [referenceDigits,hfound,Option.map_some,Option.getD_some]
  rw [href]
  exact ⟨_,_,(WCT9.CanonicalPolicy.producerDecodeOut_spec (referenceSearch_producerDecode T messages L hctx hfound)).2⟩

theorem threshold_top_floor (lay : Layer) (remaining : Nat) :
    lay = 0 → WCT9.CanonicalPolicy.threshold lay.val remaining = WCT9.CanonicalPolicy.topFloor := by
  rintro rfl
  simp [WCT9.CanonicalPolicy.threshold]

theorem matchEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (e : (cellKey T messages).cells) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e.val,ans) |
      cell (cellInit (cellKey T messages) e)] ≤ 7/((4:ENNReal)*2^128) := by
  unfold cellInit
  split_ifs
  · rw [Lazy.probEvent_cell_univ]
    exact matchEntry_cell_le T messages e.val
  · split
    · rw [Lazy.probEvent_cell_univ]
      exact matchEntry_cell_le T messages e.val
    · rename_i hctx
      by_cases hs : referenceSearch T messages (Enc.leafOf e.val.1.1) = none
      · apply le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hs' hs
      · obtain ⟨word,low,hword⟩ := reference_accepted T messages (Enc.leafOf e.val.1.1) hctx hs
        refine le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.canDecode_rejected_le
          (threshold_top_floor e.val.1.1.lay _) hword)
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hd

theorem matchEntry_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x) :
    ¬MatchEntry T messages (x,T (.inl (.inr x))) := by
  rintro ⟨L,message,counter,pad,hsource,hfit,he,hne,hselected,hdecode⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx L hsource message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def markerCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
    WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry) trace

noncomputable def matchCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun _ : Unit => MatchEntry T messages) trace

theorem lazy_marker_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (markerCount T messages result.1.2.toList:ENNReal) ≤
      (5022/(2:ENNReal)^128) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry)
    _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => markEntry_sum_init_le T messages _ e)
    (fun x hx p => markEntry_noncell T messages x hx p) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

theorem lazy_match_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (matchCount T messages result.1.2.toList:ENNReal) ≤
      (7/((4:ENNReal)*2^128)) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun _ : Unit => MatchEntry T messages) _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => by simpa using matchEntry_init_le T messages e)
    (fun x hx _ => matchEntry_noncell T messages x hx) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem referenceDigits_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceDigits T' messages' leaf=referenceDigits T messages leaf := by
  unfold referenceDigits
  rw [(source_reference_congr T T' messages messages' hm hd hl).2]

theorem referenceInput_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceInput T' messages' leaf=referenceInput T messages leaf := by
  unfold referenceInput
  rw [(source_reference_congr T T' messages messages' hm hd hl).2,hm leaf hl]

theorem markEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (entry : Entry) :
    MarkEntry T' messages' a entry ↔ MarkEntry T messages a entry := by
  unfold MarkEntry
  rw [referenceInput_decisions hm hd a.key ha.1, referenceDigits_decisions hm hd a.key ha.1]

theorem matchEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (entry : Entry) :
    MatchEntry T' messages' entry ↔ MatchEntry T messages entry := by
  unfold MatchEntry
  apply exists_congr
  intro leaf
  apply exists_congr
  intro message
  apply exists_congr
  intro counter
  apply exists_congr
  intro pad
  by_cases hl : leaf.Source
  · have hs : WotsExtract.SourceLeaf7 (Enc.leafOf leaf) := hl
    rw [referenceInput_decisions hm hd _ hs, referenceDigits_decisions hm hd _ hs,
      (source_reference_congr T T' messages messages' hm hd hs).2]
  · simp only [hl,false_and]

theorem markerCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    markerCount T' messages' trace=markerCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  apply propext
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · exact and_congr_right fun _ => markEntry_decisions hm hd _ hs entry
  · simp [hs]

theorem matchCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    matchCount T' messages' trace=matchCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  exact propext (matchEntry_decisions hm hd entry)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_count_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (count : Answers → (LeafAddr → WCT9.LayerMsg) → List Entry → Nat) (rate : ENNReal)
    (hcount : ∀ {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg},
      (∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf) →
      DecisionsAgree T T' messages → ∀ trace, count T' messages' trace=count T messages trace)
    (hlazy : ∀ (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
        (program : OracleComp RefWorld (Option (Bool × Nat))),
      ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (count T messages result.1.2.toList:ENNReal) ≤ rate *
        ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal)) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (count (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
            (sourceMessages (eagerAnswers U privateTable pub))).cells pub y))
            (sourceMessages (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)))
            (traceOf (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r.2) : ENNReal) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) : ENNReal) := by
  have hleft := cell_transfer adversary q U hU privateTable pub
      (fun s => (count s.answers (sourceMessages s.answers) s.trace : ENNReal))
      (fun tr => (count (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y hy r => by
        dsimp only [mkSample]
        rw [hcount (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)])
  simp only [mkSample] at hleft
  rw [hleft, cell_transfer adversary q U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y _ r => encodingCount_mkSample _ r)]
  exact hlazy _ _ _
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_markerCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (markerCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub markerCount _
    (fun hm hd trace => markerCount_decisions hm hd trace)
    (fun T messages program => lazy_marker_le T messages program)

theorem reference_matchCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (matchCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub matchCount _
    (fun hm hd trace => matchCount_decisions hm hd trace)
    (fun T messages program => lazy_match_le T messages program)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem markerCount_marks_eq (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) :
    markerCount T messages trace = (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt T messages trace (Enc.chainAt p)).card := by
  unfold markerCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [markerAt_iff]
  constructor
  · rintro ⟨e,he,hs,hm⟩
    exact ⟨hs,e,he,hm⟩
  · rintro ⟨hs,e,he,hm⟩
    exact ⟨e,he,hs,hm⟩

theorem reference_marker_sum_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers (sourceMessages s.answers) s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite,PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  rw [markerCount_marks_eq,Finset.card_filter,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem matchCount_pos {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace : List Entry}
    {L : LeafAddr} (hsource : WotsExtract.SourceLeaf7 L)
    (hs : referenceSearch T messages L ≠ none) (hm : EncodingMatchAt T messages trace L) :
    1 ≤ matchCount T messages trace := by
  obtain ⟨message,counter,pad,answer,hfit,hmem,hne,-,hdecode⟩ := hm
  have ht31 : L.tree < 2^31 := lt_of_lt_of_le hsource.1
    (Nat.pow_le_pow_right (by decide) (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
  have hl12 : L.leaf < 4096 := lt_of_lt_of_le hsource.2 (by
    calc 2^height L.lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le L.lay)
         _ = 4096 := by norm_num)
  unfold matchCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply Nat.succ_le_of_lt
  apply Finset.card_pos.mpr
  refine ⟨(),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  refine ⟨(encRow L message counter pad,answer),hmem,?_⟩
  exact ⟨⟨L.lay,⟨L.tree,ht31⟩,⟨L.leaf,hl12⟩⟩,message,counter,pad,hsource,hfit,rfl,hne,hs,hdecode⟩

theorem reference_encodingMatch_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf7 L ∧
      referenceSearch s.answers (sourceMessages s.answers) L ≠ none ∧
      EncodingMatchAt s.answers (sourceMessages s.answers) s.trace L |
        PairedReference.referenceExperiment adversary q] ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans ?_ (reference_matchCount_le adversary q)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro s
  split_ifs with h
  · obtain ⟨L,hsource,hs,hm⟩ := h
    rw [PMF.probOutput_eq_apply]
    exact le_mul_of_one_le_right' (by exact_mod_cast matchCount_pos hsource hs hm)
  · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingContact ====
section


namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp

theorem contact_mono {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace trace' : List Entry} {a : ChainAddr}
    (h : CanonicalRef.ContactAt T messages trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    CanonicalRef.ContactAt T messages trace' a := by
  obtain ⟨hd, v, ans, hm, hv⟩ := h
  exact ⟨hd, v, ans, hsub _ hm, hv⟩
def ContactFirstAt (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T messages (trace.take k) a ∧ ¬MarkerAt T messages (trace.take k) a ∧ MarkerAt T messages trace a
def CFK (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactFirstAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
noncomputable def contacts (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)).card
theorem contacts_mono (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T messages trace ≤ contacts T messages trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, contact_mono hp.2 hsub⟩
noncomputable def costL (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) + costL T messages F (hist ++ [e]) rest
theorem costL_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    ∀ (trace hist : List Entry), costL T messages F hist trace ≤ 93 * trace.length * contacts T messages (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T messages hist ≤ contacts T messages (hist ++ e :: rest) :=
        contacts_mono T messages (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) ≤ 93 * contacts T messages hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith
theorem cfk_new {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {h : List Entry} {e : Entry} (hold : ¬ CFK T messages h) (hnew : CFK T messages (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) e ∧ ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, contact_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T messages _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T messages _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm
noncomputable def cfCharge (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x then 93 * contacts T messages h.toList else 0
  | _ => 0
theorem costL_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T messages F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T messages F h input + costL T messages F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]
theorem cfk_nil (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) : ¬ CFK T messages [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T messages _ _).mp hm
  simp at hmem
section Step
variable [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, Fintype k] [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, DecidableEq k]
theorem cf_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T input).run allowed] *
        (if CFK T messages (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T messages h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T messages F h input : ENNReal) := by
  classical
  by_cases hold : CFK T messages h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x
    · rw [Lazy.lazyImpl_cell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
      set e₀ := Lazy.cellOf ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx with he₀
      have hx₀ : ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val = x := Lazy.cellOf_input ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx
      by_cases hq : ∃ ans₀, (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T messages _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h.toList (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
        calc _ = Pr[fun ans => CFK T messages (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 93 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hsrc : WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                exact hp.1
              rw [← hx₀]
              exact (probEvent_mono fun ans _ h => ⟨hsrc, h⟩).trans (hcell e₀ p)
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((93 * contacts T messages h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
theorem lazy_cf_le {α : Type} (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (if CFK T messages z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (costL T messages F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
    (fun h st => Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F hinit)))
    (fun h _ => if CFK T messages h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costL T messages F h.toList tail.toList) (cfCharge T messages F)
    (fun h => by simp [costL]) (fun h input answer tail => costL_step T messages F h input answer tail)
    (fun h st hc input => cf_step T messages F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T messages), zero_add] at key
  simpa using key
end Step

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
  (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
  (hd : DecisionsAgree T T' messages)
  (hnon : ∀ query, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc query → T' query=T query)
include hm hd hnon

theorem frontier_decisions (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.frontierValue T' messages' a=CanonicalRef.frontierValue T messages a := by
  have hs : WCT9.wotsSeed T' a.key.lay a.key.tree a.key.leaf a.chain =
      WCT9.wotsSeed T a.key.lay a.key.tree a.key.leaf a.chain :=
    ClaudeWCT.W9.T3.Security.Wots.Mask.wotsSeed_congr_cells _ _ _ fun p => hnon (.inr (.inl _)) trivial
  -- C3 (#866): the frontier is the chain of the current scheme.
  unfold CanonicalRef.frontierValue CanonicalRef.depth ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [referenceDigits_decisions hm hd a.key ha.1,hs]
  exact (ClaudeWCT.W9.T3.Security.Wots.Enc.respects_chainW _ _ _ _ _ _ _).eval_eq hnon

theorem contact_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.ContactAt T' messages' trace a ↔ CanonicalRef.ContactAt T messages trace a := by
  unfold CanonicalRef.ContactAt
  rw [frontier_decisions hm hd hnon a ha]
  unfold CanonicalRef.depth
  rw [referenceDigits_decisions hm hd a.key ha.1]

omit hnon in
theorem marker_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.MarkerAt T' messages' trace a ↔ CanonicalRef.MarkerAt T messages trace a := by
  rw [markerAt_iff,markerAt_iff]
  exact exists_congr fun e => and_congr_right fun _ => markEntry_decisions hm hd a ha e

theorem cfk_decisions (trace : List Entry) : CFK T' messages' trace ↔ CFK T messages trace := by
  unfold CFK ContactFirstAt
  refine exists_congr fun p => and_congr_right fun hp => exists_congr fun k => ?_
  rw [contact_decisions hm hd hnon _ _ hp,marker_decisions hm hd _ _ hp,
    marker_decisions hm hd _ _ hp]

theorem contacts_decisions (trace : List Entry) : contacts T' messages' trace=contacts T messages trace := by
  unfold contacts
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_congr_right fun hp => contact_decisions hm hd hnon trace _ hp
end Congr

noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers (sourceMessages s.answers) s.trace then 1 else 0
noncomputable def cfCost (s : RefSample) : ENNReal :=
  ((93*s.trace.length*contacts s.answers (sourceMessages s.answers) s.trace:Nat):ENNReal)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_cf_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfCost (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) := by
  have hleft := cell_transfer adversary q U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr then (1:ENNReal) else 0)
      (fun y hy r => by
        unfold cfInd mkSample
        rw [propext (cfk_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _)])
  have hright := cell_transfer adversary q U hU privateTable pub cfCost
      (fun tr => ((93*tr.length*contacts (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr:Nat):ENNReal))
      (fun y hy r => by
        unfold cfCost mkSample
        rw [contacts_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _])
  rw [hleft,hright]
  refine (lazy_cf_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))
    (cellInit_nonempty _)
    (fun e p => markEntry_init_le _ _ _ e p)
    (fun x hx p => markEntry_noncell _ _ x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costL_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this

theorem reference_cfInd_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q cfInd cfCost _
    (fun privateTable pub => cells_cf_le adversary q (PairedReference.referenceInputs adversary)
      Finset.subset_union_left privateTable pub)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem chainAt_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
theorem contacts_le_contactCount (s : RefSample) : contacts s.answers (sourceMessages s.answers) s.trace ≤ Normalized.Contacts.contactCount s := by
  unfold contacts Normalized.Contacts.contactCount
  refine Finset.card_le_card_of_injOn (fun p => Enc.chainAt p) ?_ (fun p _ p' _ h => chainAt_injective h)
  intro p hp
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
  rw [Finset.mem_coe, Finset.mem_filter, Normalized.Contacts.mem_sourceChains7]
  exact hp
theorem cfCost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s ≤
      ((93 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : PairedReference.referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (contacts_le_contactCount s)
theorem reference_contactFirst_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧ ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      93 * ((q : ENNReal) / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  calc _ ≤ ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := exists_chainAt ha
          rw [cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := reference_cfInd_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((93 * q : Nat) : ENNReal) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (cfCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
end
-- ==== merged from T3_Secc_WotsSmallTransport ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open _root_.SigGolfCandidate.T3.Security.Wots.Ref
structure TraceEvent where
  holds : Answers → List Entry → Prop
  mono : ∀ {T : Answers} {trace trace' : List Entry}, holds T trace → (∀ e ∈ trace, e ∈ trace') → holds T trace'
  transfer : ∀ {A T : Answers} {trace : List Entry}, ShortAgree A T →
    (∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1))) → holds A trace → holds T trace
end SmallT
open SmallT
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsSmallTransport ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open ClaudeWCT.W9.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
open SigGolfCandidate.T3.Security.Wots.Ref (ShortAgree cap_recorded_le chargeSum cut eagerSide eval_congr_queried fixedRecord
  pmf_probEvent_mono pureRecord pureRecord_value entriesOf_congr fillAnswers_empty fixedRecord_counted fixedRecord_hashOnly
  fixedRecord_mem_record recorded_bind agrees_empty chargeSum_append cut_cached cut_shortAgree pureRecord_charge
  pureRecord_inputs ticks_recorded verdict_recorded_fixed embed traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public)
theorem wotsPrimitiveSrc_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : WotsExtract.WotsPrimitiveSrc A trace) : WotsExtract.WotsPrimitiveSrc T trace := by
  have hdepth : depth A = depth T := funext (depth_short hAT)
  have hfront : frontierValue A = frontierValue T := funext (frontierValue_short hAT)
  have hrefi : referenceInput A = referenceInput T := funext (referenceInput_short hAT)
  have hrefd : referenceDigits A = referenceDigits T := funext (referenceDigits_short hAT)
  rcases h with ⟨L, hsrc, hL⟩ | hS | ⟨a, hsrc, ha⟩ | ⟨a, b, hsa, hsb, hab, ha, hb⟩ | ⟨a, hsrc, ha, hc⟩
  · refine Or.inl ⟨L, hsrc, ?_⟩
    simpa only [EncodingMatchAt, hrefi, hrefd] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hsource, hclass, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, hsource, ?_, ?_⟩
    · cases position <;> simpa only [StructuralClass, OtherChainRow, hdepth] using hclass
    · rw [← honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem, ← hAT.public _ (honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, hsrc, ?_⟩))
    simpa only [TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsa, hsb, hab, ?_, ?_⟩)))
    · simpa only [ContactAt, hdepth, hfront] using ha
    · simpa only [ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsrc, ?_, ?_⟩)))
    · simpa only [MarkerAt, hrefi, hrefd] using ha
    · simpa only [ContactAt, hdepth, hfront] using hc
def srcEvent : TraceEvent where
  holds := WotsExtract.WotsPrimitiveSrc
  mono := fun h hsub => WotsExtract.WotsPrimitiveSrc.mono h hsub
  transfer := fun hAT htrace h => wotsPrimitiveSrc_transfer hAT htrace h
def VerifierEv (Ev : TraceEvent) (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    Ev.holds answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
def CaseABEvAt (Ev : TraceEvent) (adversary : AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  ∀ generated interaction checked, GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → VerifierEv Ev answers generated.value.1 forgery
def CaseABEv (Ev : TraceEvent) (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEvAt Ev adversary (QueryRecorded.recordedTrace z.1) z.2
def GoodEv (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABEvAt Ev adversary result answers
def PsiEv (Ev : TraceEvent) (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true ∧
    Ev.holds T (entriesOf T (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)))
theorem psiEv_of_verifierEv (Ev : TraceEvent) (A T : Answers) (publicKey : Digest)
    (result : Option ForgeryP × QueryLog Requests) (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → VerifierEv Ev A publicKey forgery) :
    PsiEv Ev T publicKey result := by
  refine ⟨haccept, ?_⟩
  obtain ⟨forgery, hf, hcheck, hsub⟩ := verdict_accepts T publicKey result haccept
  obtain ⟨-, m', w', hof', -, hqsub⟩ := PaddedExtraction.check_accepting T publicKey result.2 forgery hcheck
  obtain ⟨m, w, hof, -, hprim⟩ := hab forgery hf
  have hofT : PaddedExtraction.WitnessOf T publicKey forgery m w := by
    cases forgery with
    | witness message witness => exact hof
    | signature message signature =>
        obtain ⟨hm, hw⟩ := hof
        refine ⟨hm, ?_⟩
        rw [← hw]
        symm
        apply (eval_congr_queried _ A T fun query hq => hverdict query (hsub query ?_)).1
        simp only [checkForgeryP, SourceReplay.queried_bind]
        exact List.mem_append_left _ hq
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hofT hof'
  have hagree : ∀ query ∈ SourceReplay.queried T (verifyP m publicKey w), A query = T query :=
    fun query hq => hverdict query (hsub query (hqsub query hq))
  have hq := (eval_congr_queried _ A T hagree).2
  have he : entriesOf A (SourceReplay.queried A (verifyP m publicKey w)) =
      entriesOf T (SourceReplay.queried T (verifyP m publicKey w)) := by
    rw [hq]
    exact entriesOf_congr A T _ hagree
  change Ev.holds A (entriesOf A (SourceReplay.queried A (verifyP m publicKey w))) at hprim
  rw [he] at hprim
  have hprimT := Ev.transfer hshort (fun e he' => ?_) hprim
  · exact Ev.mono hprimT (WotsExtract.entriesOf_mono fun query hq' => hsub query (hqsub query hq'))
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1, e.2) ∈ _ from he')
    exact hagree _ hmem
theorem goodEv_imp (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (fixedInteraction adversary T))
    (hgood : GoodEv Ev adversary q (combine T interaction) (cut (combine T interaction).state T)) :
    PsiEv Ev T (evalWithAnswerFn T keygen).1 interaction.value ∧
      keygenCharge T + chargeSum interaction.events +
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hg0val : (pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen := pureRecord_value T keygen (∅, ∅)
  have hg0 : pureRecord T keygen (∅, ∅) ∈ support (fixedRecord T keygen (∅, ∅)) := by
    rw [fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := fixedRecord_mem_record T keygen (∅, ∅) (agrees_empty T) _ hg0
  unfold fixedInteraction at hi
  rw [← hg0val] at hi
  obtain ⟨hirec, hagi⟩ := fixedRecord_mem_record T _ _ hag0 interaction hi
  have hci : verdictRecord T interaction ∈ support (fixedRecord T (GameWith.verdict PaddedGame.checker
      (pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : GameSplit adversary (combine T interaction) (pureRecord T keygen (∅, ∅)) interaction
      (verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hwin, hcharge, hab⟩ := hgood
  have hacc : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
      interaction.value) = true := by
    rw [← pureRecord_value]
    exact hwin
  rw [hg0val] at hcirec
  have hknown := FirstHit.recorded_query_known _ (verdict_hashOnly _ _) interaction.state _ hcirec
  have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
      SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) :=
    pureRecord_inputs T _ interaction.state
  have hverdict : ∀ query ∈ SourceReplay.queried T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value),
      cut (verdictRecord T interaction).state T query = T query := by
    intro query hq
    rw [← hinputs] at hq
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hq
    apply cut_cached
    intro x hx
    have hk := (hknown event hevent).1
    rcases event with ⟨before, input, answer⟩
    change input = .inl (.inr x) at hx
    subst hx
    change (verdictRecord T interaction).state.2 x = some answer at hk
    rw [hk]
    rfl
  refine ⟨psiEv_of_verifierEv Ev (cut (verdictRecord T interaction).state T) T _ interaction.value
    (cut_shortAgree _ _) hverdict hacc ?_, ?_⟩
  · intro forgery hf
    have h := hab _ interaction _ hsplit forgery hf
    rw [hg0val] at h
    exact h
  · have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hv : chargeSum (verdictRecord T interaction).events =
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
      pureRecord_charge T _ (verdict_hashOnly _ _) interaction.state
    have hc : chargeSum (combine T interaction).events = chargeSum (pureRecord T keygen (∅, ∅)).events +
        (chargeSum interaction.events + chargeSum (verdictRecord T interaction).events) := by
      simp only [combine, chargeSum_append]
    omega
theorem offlineEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => PsiEv Ev T (evalWithAnswerFn T keygen).1 x.1 ∧
        keygenCharge T + x.2 + verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (offlineGame T adversary) q
    (fun queries => Ev.holds T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change Ev.holds T (traceOf T (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact Ev.mono hprim (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PaddedGame.verdict_public _ _)]
    unfold verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_gameEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => GoodEv Ev adversary q result (cut result.state T) |
        fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  rw [fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => goodEv_imp Ev adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offlineEv_le Ev adversary q T)
  rw [← hcount, probEvent_map]
  rfl
theorem caseABEv_le_recorded (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 | recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => GoodEv Ev adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] := by
        apply SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [completed_map, MonitoredPrivate.event_lift]
theorem eagerEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) :
    Pr[fun pair => GoodEv Ev adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceComp adversary q] := by
  unfold eagerSide referenceComp
  apply Ref.probEvent_bind_mono
  intro privateTable
  apply Ref.probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_gameEv_le Ev adversary q _
theorem caseABEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceExperiment adversary q] := by
  refine (caseABEv_le_recorded Ev adversary q hq).trans ?_
  rw [recorded_eq_eager adversary (GoodEv Ev adversary q)]
  refine (eagerEv_le_reference Ev adversary q).trans (le_of_eq ?_)
  unfold referenceExperiment
  rw [MonitoredPrivate.event_lift]
end SmallT
abbrev CaseABSrc (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  SmallT.CaseABEv SmallT.srcEvent adversary z
theorem caseABSrc_le_reference (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => WotsExtract.WotsPrimitiveSrc sample.answers sample.trace | referenceExperiment adversary q] :=
  SmallT.caseABEv_le_reference SmallT.srcEvent adversary q hq
theorem completed_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hcomp : BPB.SignerComplete z.2) :
    CaseABSrc adversary z ∨ CaseC.CaseCFreshPinned adversary z ∨ CaseC.CaseCSignedPinned adversary z := by
  by_cases hab : CaseABSrc adversary z
  · exact Or.inl hab
  right
  unfold CaseABSrc SmallT.CaseABEv SmallT.CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated, interaction, checked, hsplit, forgery, hf, hnot⟩ := hab
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  set result := QueryRecorded.recordedTrace z.1 with hresult
  have hrs : ∀ input answer, SourceReplay.known result.state input = some answer → z.2 input = answer := ha
  have hsplit' := hsplit
  obtain ⟨hg, hi, hc, heq⟩ := hsplit'
  have hstate : result.state = checked.state := by rw [heq]
  have hvalue : result.value = checked.value := by rw [heq]
  have hgext : SourceReplay.Extends generated.state result.state :=
    (SourceReplay.run_extends _ generated.state (interaction.value, interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hsplit.extends
  have hgen : evalWithAnswerFn z.2 keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hrs input answer (SourceReplay.known_mono generated.state result.state hgext hk))
  have hpk : generated.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → z.2 input = answer := by
    rw [← hstate]; exact hrs
  have hwin : checked.value = true := by rw [← hvalue]; exact hclean.1
  obtain ⟨hlen, forgery', hf', hfresh, message, witness, hof, hconc⟩ :=
    PaddedExtraction.verdict_recorded generated.value.1 interaction.value interaction.state checked hc z.2 hac hpk hwin
  have hff : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst hff
  have hvd : evalWithAnswerFn z.2 (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value) =
      true := by
    rw [(SourceReplay.resolves_of_run _ (Ref.verdict_hashOnly _ _) interaction.state (checked.value, checked.state)
      (FirstHit.recorded_support _ _ _ hc)).eval z.2 hac]
    exact hwin
  obtain ⟨forgery'', hf'', hcheck, -⟩ := Ref.verdict_accepts z.2 _ _ hvd
  obtain ⟨-, message', witness', hof', hv, -⟩ := PaddedExtraction.check_accepting z.2 _ _ forgery'' hcheck
  have hff' : forgery'' = forgery' := Option.some.inj (hf''.symm.trans hf')
  subst hff'
  obtain ⟨rfl, rfl⟩ := Ref.witnessOf_unique hof' hof
  obtain ⟨N, hdc, hN, -, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_src z.2 message' generated.value.1 witness' hpk hv
  rcases hcase with hprim | ⟨hgood, hfts⟩
  · exact absurd ⟨message', witness', hof', hv, hprim⟩ hnot
  obtain ⟨N', hdc', hN', hevent, hS', -⟩ := hconc
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  have hCat : BPB.CaseCAt z.2 message' witness' result.events := by
    refine ⟨N', hdc, hN, ?_, hS, hgood, hfts, hcomp⟩
    obtain ⟨prior, hp⟩ := hevent
    refine ⟨prior, ?_⟩
    rw [heq]
    exact List.mem_append_right _ (List.mem_append_right _ hp)
  by_cases hsigned : BPB.SignedDigest interaction.value.2 message' witness'
  · exact Or.inr ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
  · exact Or.inl ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.Paired.verifyP ClaudeWCT.W9.T3M.Paired.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF PairedOuter.GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
open ClaudeWCT.W9.T3.Security.Wots.PairedReference ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
open SigGolfCandidate.T3.Security.Wots.Ref (ShortAgree cap_recorded_le chargeSum cut eagerSide eval_congr_queried fixedRecord
  pmf_probEvent_mono pureRecord pureRecord_value entriesOf_congr fillAnswers_empty fixedRecord_counted fixedRecord_hashOnly
  fixedRecord_mem_record recorded_bind agrees_empty chargeSum_append cut_cached cut_shortAgree pureRecord_charge
  pureRecord_inputs ticks_recorded verdict_recorded_fixed embed traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public)
def CheckerEv (Ev : TraceEvent) (answers : Answers) (publicKey : Digest)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery) = true ∧
    Ev.holds answers (entriesOf answers (queried answers
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery)))
def CaseABEvAt (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  ∀ generated interaction checked, PairedReference.GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → CheckerEv Ev answers generated.value.1 interaction.value.2 forgery
def CaseABEv (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEvAt Ev adversary (QueryRecorded.recordedTrace z.1) z.2
def GoodEv (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABEvAt Ev adversary result answers
def PsiEv (Ev : TraceEvent) (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Prop :=
  evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true ∧
    Ev.holds T (entriesOf T (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result)))
theorem psiEv_of_checkerEv (Ev : TraceEvent) (A T : Answers) (publicKey : Digest)
    (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → CheckerEv Ev A publicKey result.2 forgery) :
    PsiEv Ev T publicKey result := by
  refine ⟨haccept, ?_⟩
  obtain ⟨forgery, hf, hcheck, hsub⟩ := PairedReference.Ref.verdict_accepts T publicKey result haccept
  obtain ⟨_,hprim⟩ := hab forgery hf
  have hagree : ∀ query ∈ SourceReplay.queried T
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery), A query = T query :=
    fun query hq => hverdict query (hsub query hq)
  have hq := (eval_congr_queried _ A T hagree).2
  have he : entriesOf A (SourceReplay.queried A
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery)) =
      entriesOf T (SourceReplay.queried T
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery)) := by
    rw [hq]
    exact entriesOf_congr A T _ hagree
  change Ev.holds A (entriesOf A (SourceReplay.queried A
    (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery))) at hprim
  rw [he] at hprim
  have hprimT := Ev.transfer hshort (fun e he' => ?_) hprim
  · exact Ev.mono hprimT (WotsExtract.entriesOf_mono hsub)
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1,e.2) ∈ _ from he')
    exact hagree _ hmem

theorem goodEv_imp (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests))
    (hi : interaction ∈ support (PairedReference.Ref.fixedInteraction adversary T))
    (hgood : GoodEv Ev adversary q (PairedReference.Ref.combine T interaction) (cut (PairedReference.Ref.combine T interaction).state T)) :
    PsiEv Ev T (evalWithAnswerFn T keygen).1 interaction.value ∧
      SigGolfCandidate.T3.Security.Wots.keygenCharge T + chargeSum interaction.events +
        PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hg0val : (pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen := pureRecord_value T keygen (∅, ∅)
  have hg0 : pureRecord T keygen (∅, ∅) ∈ support (fixedRecord T keygen (∅, ∅)) := by
    rw [fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := fixedRecord_mem_record T keygen (∅, ∅) (agrees_empty T) _ hg0
  unfold PairedReference.Ref.fixedInteraction at hi
  rw [← hg0val] at hi
  obtain ⟨hirec, hagi⟩ := fixedRecord_mem_record T _ _ hag0 interaction hi
  have hci : PairedReference.Ref.verdictRecord T interaction ∈ support (fixedRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
      (pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [fixedRecord_hashOnly T _ (PairedReference.Ref.verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : PairedReference.GameSplit adversary (PairedReference.Ref.combine T interaction) (pureRecord T keygen (∅, ∅)) interaction
      (PairedReference.Ref.verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hwin, hcharge, hab⟩ := hgood
  have hacc : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1
      interaction.value) = true := by
    rw [← pureRecord_value]
    exact hwin
  rw [hg0val] at hcirec
  have hknown := FirstHit.recorded_query_known _ (PairedReference.Ref.verdict_hashOnly _ _) interaction.state _ hcirec
  have hinputs : (PairedReference.Ref.verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
      SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) :=
    pureRecord_inputs T _ interaction.state
  have hverdict : ∀ query ∈ SourceReplay.queried T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value),
      cut (PairedReference.Ref.verdictRecord T interaction).state T query = T query := by
    intro query hq
    rw [← hinputs] at hq
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hq
    apply cut_cached
    intro x hx
    have hk := (hknown event hevent).1
    rcases event with ⟨before, input, answer⟩
    change input = .inl (.inr x) at hx
    subst hx
    change (PairedReference.Ref.verdictRecord T interaction).state.2 x = some answer at hk
    rw [hk]
    rfl
  refine ⟨psiEv_of_checkerEv Ev (cut (PairedReference.Ref.verdictRecord T interaction).state T) T _ interaction.value
    (cut_shortAgree _ _) hverdict hacc ?_, ?_⟩
  · intro forgery hf
    have h := hab _ interaction _ hsplit forgery hf
    rw [hg0val] at h
    exact h
  · have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = SigGolfCandidate.T3.Security.Wots.keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hv : chargeSum (PairedReference.Ref.verdictRecord T interaction).events =
        PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
      pureRecord_charge T _ (PairedReference.Ref.verdict_hashOnly _ _) interaction.state
    have hc : chargeSum (PairedReference.Ref.combine T interaction).events = chargeSum (pureRecord T keygen (∅, ∅)).events +
        (chargeSum interaction.events + chargeSum (PairedReference.Ref.verdictRecord T interaction).events) := by
      simp only [PairedReference.Ref.combine, chargeSum_append]
    omega
theorem offlineEv_le (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => PsiEv Ev T (evalWithAnswerFn T keygen).1 x.1 ∧
        SigGolfCandidate.T3.Security.Wots.keygenCharge T + x.2 + PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (PairedReference.offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | PairedReference.offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (PairedReference.offlineGame T adversary) q
    (fun queries => Ev.holds T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold PairedReference.offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PairedOuter.PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change Ev.holds T (traceOf T (List.replicate (SigGolfCandidate.T3.Security.Wots.keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact Ev.mono hprim (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (SigGolfCandidate.T3.Security.Wots.keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PairedOuter.PaddedGame.verdict_public _ _)]
    unfold PairedReference.Ref.verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_gameEv_le (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => GoodEv Ev adversary q result (cut result.state T) |
        fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | PairedReference.offlineRun T adversary q] := by
  rw [PairedReference.Ref.fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => goodEv_imp Ev adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [PairedReference.Ref.interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offlineEv_le Ev adversary q T)
  rw [← hcount, probEvent_map]
  rfl
theorem caseABEv_le_recorded (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 | PairedReference.Ref.recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => GoodEv Ev adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        PairedSeccLaw.completedExperiment adversary q hq] := by
        apply SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (PairedSeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PairedOuter.PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> PairedSeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [PairedReference.Ref.completed_map, MonitoredPrivate.event_lift]
theorem eagerEv_le_reference (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun pair => GoodEv Ev adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (PairedReference.referenceInputs adversary) (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | PairedReference.referenceComp adversary q] := by
  unfold eagerSide PairedReference.referenceComp
  apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
  intro privateTable
  apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_gameEv_le Ev adversary q _
theorem caseABEv_le_reference (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | PairedReference.referenceExperiment adversary q] := by
  refine (caseABEv_le_recorded Ev adversary q hq).trans ?_
  rw [PairedReference.Ref.recorded_eq_eager adversary (GoodEv Ev adversary q)]
  refine (eagerEv_le_reference Ev adversary q).trans (le_of_eq ?_)
  unfold PairedReference.referenceExperiment
  rw [MonitoredPrivate.event_lift]

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open CanonicalRef
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem wotsPrimitiveSrc_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : CanonicalExtract.WotsPrimitiveSrc A (CanonicalRef.sourceMessages A) trace) :
    CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T) trace := by
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) = CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  have hfront : CanonicalRef.frontierValue A (CanonicalRef.sourceMessages A) = CanonicalRef.frontierValue T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.frontierValue_short hAT)
  have hrefi : CanonicalRef.referenceInput A (CanonicalRef.sourceMessages A) = CanonicalRef.referenceInput T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.referenceInput_short hAT)
  have hrefd : CanonicalRef.referenceDigits A (CanonicalRef.sourceMessages A) = CanonicalRef.referenceDigits T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.referenceDigits_short hAT)
  rcases h with ⟨L, hsrc, hL⟩ | hS | ⟨a, hsrc, ha⟩ | ⟨a, b, hsa, hsb, hab, ha, hb⟩ | ⟨a, hsrc, ha, hc⟩
  · refine Or.inl ⟨L, hsrc, ?_⟩
    have hns : CanonicalRef.NotSearched A (CanonicalRef.sourceMessages A) =
        CanonicalRef.NotSearched T (CanonicalRef.sourceMessages T) := by
      funext L' x
      unfold CanonicalRef.NotSearched
      rw [CanonicalRef.referenceSearch_short hAT, CanonicalRef.sourceMessages_short hAT]
    simpa only [CanonicalRef.EncodingMatchAt, hrefi, hrefd, hns] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hsource, hclass, hmain, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, hsource, ?_, hmain, ?_⟩
    · cases position <;> simpa only [CanonicalRef.StructuralClass, CanonicalRef.OtherChainRow, hdepth] using hclass
    · rw [← Ref.honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem, ← hAT.public _ (Ref.honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, hsrc, ?_⟩))
    simpa only [CanonicalRef.TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsa, hsb, hab, ?_, ?_⟩)))
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using ha
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsrc, ?_, ?_⟩)))
    · simpa only [CanonicalRef.MarkerAt, hrefi, hrefd] using ha
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using hc

def srcEvent : TraceEvent where
  holds := fun T => CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T)
  mono := fun h hsub => CanonicalExtract.WotsPrimitiveSrc.mono h hsub
  transfer := fun hAT htrace h => wotsPrimitiveSrc_transfer hAT htrace h

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem structuralHitSrc_paired {T : Answers} {trace : List Entry} {inputs : Finset HashInput}
    (h : StructuralHitSrc T (CanonicalRef.sourceMessages T) trace)
    (hin : ∀ entry ∈ trace, entry.1 ∈ inputs) : PairedReference.StructuralHitIn inputs T trace := by
  obtain ⟨p,x,a,hmem,hpos,hb,hsrc,hcls,hmain,hhit⟩ := h
  cases p with
  | chain lay tree leaf i step =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_chain]; exact hhit⟩
  | leaf lay tree leaf =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_leaf]; exact hhit⟩
  | node lay tree level node =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_node]; exact hhit⟩
  | forest | wctChain | wctLeaf | wctNode => exact hmain.elim
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def StructuralHitTrace (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧
    Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧
    CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position ∧
    Extract.Paired.HashHitAt answers position (Extract.Paired.honestInput answers position) input

theorem StructuralHitTrace.mono {T : Answers} {trace trace' : List Entry}
    (h : StructuralHitTrace T trace) (hsub : ∀ entry ∈ trace, entry ∈ trace') : StructuralHitTrace T trace' := by
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  exact ⟨p,x,a,hsub _ hm,hp,hb,hs,hc,hh⟩

theorem StructuralHitTrace.toHitIn {T : Answers} {trace : List Entry} {inputs : Finset HashInput}
    (h : StructuralHitTrace T trace) (hin : ∀ entry ∈ trace, entry.1 ∈ inputs) : StructuralHitIn inputs T trace := by
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  exact ⟨p,x,a,hm,hin _ hm,hp,hb,hs,hc,hh⟩

theorem structuralHitTrace_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : StructuralHitTrace A trace) : StructuralHitTrace T trace := by
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) =
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  refine ⟨p,x,a,hm,hp,hb,hs,?_,?_⟩
  · cases p <;> simpa only [CanonicalRef.StructuralClass,CanonicalRef.OtherChainRow,hdepth] using hc
  · rw [← honestInput_short hAT p hb]
    obtain ⟨hne,heq⟩ := hh
    refine ⟨hne,?_⟩
    rw [← htrace (x,a) hm,← hAT.public _ (honestInput_length A p)]
    exact heq

theorem ftsHitIn_structuralHitTrace {T : Answers} {qs : List Spec.Domain}
    (h : Extract.Paired.FtsHitIn T qs) : StructuralHitTrace T (entriesOf T qs) := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := h
  -- #866: `SameHeader` is `length ∧ hdrKey`; `posOf_sameHeader` is its paired `posOf_key_eq`.
  have hp : Extract.posOf x = some p := Extract.Paired.posOf_sameHeader T p hb.legacy x hs
  refine ⟨p,x,_,SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf hq,hp,hb,?_,?_,hh⟩
  · cases p with
    | chain | leaf | node | forest => exact hfts.elim
    | wctChain | wctLeaf => exact hb.legacy
    | wctNode => exact hb.legacy
  · cases p <;> first | exact hfts.elim | trivial

end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
def combinedEvent : TraceEvent where
  holds := fun T trace => CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T) trace ∨
    PairedReference.StructuralHitTrace T trace
  mono := fun h hsub => h.elim (fun hp => Or.inl (hp.mono hsub)) (fun hs => Or.inr (hs.mono hsub))
  transfer := fun hAT htrace h => h.elim
    (fun hp => Or.inl (wotsPrimitiveSrc_transfer hAT htrace hp))
    (fun hs => Or.inr (PairedReference.structuralHitTrace_transfer hAT htrace hs))
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_Final ====
section

section
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
theorem reference_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : s.trace.length ≤ q := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, hrun, rfl⟩ := hs
  have h1 := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hrun
  have h2 : run ∈ support (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) := by
    revert h1
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl (restTable R))
      (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) run
  have hcount : (run.1, SphincsSecurity.QueryCap.calls RefCharged run.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (restTable R) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨run, h2, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (restTable R) adversary q) _ hcount
  refine le_trans ?_ hle
  show (traceOf (restTable R) run.2).length ≤ _
  have hf := traceOf_filter_length (restTable R) (fun _ => True) run.2
  simp only [decide_true, List.filter_true] at hf
  rw [hf]
  unfold SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨x, rfl, -⟩ := hq
  trivial
theorem prefixClassCount_le_length (s : RefSample) : prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  have hsize : ∀ c : ChainAddr, WotsExtract.SourceChain c → c.key.tree < 2 ^ 40 ∧ c.key.leaf < 2 ^ 24 := by
    intro c hc
    refine ⟨by have := hc.1.1; omega, ?_⟩
    have h1 := hc.1.2
    have h2 : 2 ^ height c.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le c.key.lay; omega)
    omega
  unfold ContactAt
  rw [depth_maskAt_all T a b (Mask.maskOK_of_lt (hsize a ha).2),
    frontierValue_maskAt_bounded T a b (hsize a ha) (hsize b hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRowW a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; rw [hm]
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (prefixRowAt_unique (answers := T) ha hb ⟨_, va, by omega, rfl⟩ ⟨_, vb, by omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(mem_sourceChains b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]
theorem probEvent_le_six {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] + Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p] := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  exact probEvent_or_le _ _ _
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _
end SmallP
open SmallP
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
end SmallR
open SmallR
end SigGolfCandidate.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
open SigGolfCandidate.T3.Security.Wots.SmallP (mem_take_succ probEvent_le_six)
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRowW_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf7 L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩
theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, chainOf p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
end SmallP
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
    (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q
/-- Selected-half contact rate is at most 93; the uniform marker sum is at most 54*93 = 5022. -/
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    93 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (5022 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
noncomputable def prefixCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    (912 / 1000 : ENNReal) * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeffW9 (q : Nat) : ENNReal :=
  7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    (912 / 1000 : ENNReal) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))
theorem chainOf_injective : Function.Injective SmallP.chainOf := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [SmallP.chainOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) ≤ Leaf.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) =
      ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain, Leaf.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Leaf.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain ⊆ sourceChains := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (mem_sourceChains a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
/-- Together with 248/100000, this rate gives the scalar closing coefficient 196327/100000. -/
noncomputable def classRateW9 : ENNReal := 196079 / 100000
theorem inv_one_sub_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 4194304 / 4193304 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (4193304 / 4194304 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosingW9.one_sub_x_ge_of_small q hs)
    _ = 4194304 / 4193304 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))
theorem prefixCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : prefixCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold prefixCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ (1 - x),
    ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * (((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 93 * x * u) +
        (912 / 1000 : ENNReal) * 2 * u
      ≤ (88 / 1000 : ENNReal) *
          (((3 / 2 : ENNReal) + 4 * (1000 / 4194304 : ENNReal) + 2 * ((1000 / 4194304 : ENNReal))^2) * (4194304/4193304) +
            4 * (1000 / 4194304 : ENNReal) * (4194304/4193304)^2 + 2 * 93 * (1000 / 4194304 : ENNReal) * (4194304/4193304)) +
          (912 / 1000 : ENNReal) * 2 * (4194304/4193304) := by
        gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num
theorem encodingCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : encodingCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold encodingCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x)]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (7 / 4 : ENNReal) + (88 / 1000 : ENNReal) * 2 * 5022 * x * u
      ≤ 7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * (1000 / 4194304 : ENNReal) * (4194304/4193304) := by gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem errCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : errCoeffW9 q ≤ 2 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  have e1 : twoEdgeRate q * q = ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) +
      2 * ((q : ENNReal) / 2 ^ 128) ^ 2) * ((q : ENNReal) / 2 ^ 128) := by
    unfold twoEdgeRate
    simp only [div_eq_mul_inv]
    ring
  have e2 : (2 / 2 ^ 128 : ENNReal) * q = 2 * ((q : ENNReal) / 2 ^ 128) := by
    simp only [div_eq_mul_inv]
    ring
  unfold errCoeffW9
  rw [e1, e2]
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  simp only [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * ((1 + (3 / 2 + 4 * x + 2 * x ^ 2) * x) * u +
        (2 * x * (1 + 2 * x) * u ^ 2 + (1 + 2 * x) * u) + (1 + 2 * x) * u  + 93 * x * ((1 + 2 * x) * u)) +
        912 / 1000 * ((1 + 2 * x) * u)
      ≤ (88 / 1000 : ENNReal) *
          ((1 + (3 / 2 + 4 * (1000 / 4194304 : ENNReal) + 2 * (1000 / 4194304 : ENNReal) ^ 2) * (1000 / 4194304 : ENNReal)) *
              (4194304 / 4193304) +
            (2 * (1000 / 4194304 : ENNReal) * (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) ^ 2 +
              (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) +
            (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) +
            93 * (1000 / 4194304 : ENNReal) * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304))) +
          912 / 1000 * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) := by
        gcongr
    _ ≤ 2 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem one_le_classRateW9 : (1 : ENNReal) ≤ classRateW9 := by
  unfold classRateW9
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem digestRate_leW9 : 1 + SeccClosingW9.cacheRate ≤ classRateW9 := by
  unfold classRateW9
  rw [SeccClosingW9.cacheRate_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem excess_leW9 (q : Nat) :
    (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 ≤ (247 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  rw [SeccClosingW9.excessRate_def]
  simp only [div_eq_mul_inv]
  exact le_of_eq (by ring)
theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    nearTerm q ≤ (1501 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  unfold nearTerm nearPrice SigGolfCandidate.T3.Security.Wots.signRatio
  rw [SeccClosingW9.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (150 : ENNReal) * q / 2 ^ 128 + 63 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700 =
      (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 63 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (4194304 / 4193304 * x) * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (4194304 / 4193304 * (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (4194304 / 4193304 * (63 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ (1501 / 10) * x ^ 2 + (1 / 100000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num
theorem pairTerm_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    BPair.pairTerm q ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  have hc : (q.choose 2 : ENNReal) ≤ (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by
    have hc2 : ((q.choose 2 * 2 : Nat) : ENNReal) ≤ ((q * q : Nat) : ENNReal) :=
      Nat.cast_le.mpr (by rw [Nat.choose_two_right]; exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    calc (q.choose 2 : ENNReal) = (1 / 2 : ENNReal) * ((q.choose 2 * 2 : Nat) : ENNReal) := by
          push_cast
          rw [one_div, mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      _ ≤ (1 / 2 : ENNReal) * ((q * q : Nat) : ENNReal) := mul_le_mul' le_rfl hc2
      _ = (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by push_cast; rfl
  unfold BPair.pairTerm
  calc (q.choose 2 : ENNReal) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2
      ≤ ((1 / 2 : ENNReal) * ((q : ENNReal) * q)) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2 := by gcongr
    _ = (1 / 2 : ENNReal) * ((q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal)) ^ 2 := by simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ (1 / 2 : ENNReal) * (4194304 / 4193304 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = ((1 / 2 : ENNReal) * (4194304 / 4193304 : ENNReal) ^ 2) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        rw [mul_pow]; ring
    _ ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
end SmallR
/-- The clean win splits into cases A/B, case C without FTS overflow, signer incompleteness, and the FTS overflow
event (campaign X1 stage A; bounded by `fts_overflow_le`). -/
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
        SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ClaudeWCT.W9.T3.Security.FtsOverflow z.1 |
        SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) ((probEvent_or_le _ _ _).trans
    (add_le_add ((probEvent_or_le _ _ _).trans (add_le_add (probEvent_or_le _ _ _) le_rfl)) le_rfl))
  intro z hz hclean
  by_cases hov : ClaudeWCT.W9.T3.Security.FtsOverflow z.1
  · exact Or.inr ⟨hclean, hov⟩
  by_cases hcomp : BPB.SignerComplete z.2
  · rcases completed_split_src adversary q hq z hz hclean hcomp with h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hclean, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hclean, h, WPair.noOverflow_of_outIdx adversary z fun g i c hs =>
        ClaudeWCT.W9.T3.Security.logNoOverflow_of_not_ftsOverflow adversary q hq z hz hov g i c hs⟩))
    · exact absurd h (CaseC.caseCSignedPinned_impossible adversary q hq z hz hclean)
  · exact Or.inl (Or.inr hcomp)
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Secc
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security (QueryRecorded.CleanWin)
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (budgetSplit largeBound)
open ClaudeWCT.W9.T3M.Final (AdversaryP SecurityP)
def LargeRouteBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq] ≤
      largeBound q
/-- The small case-C bound from the near and pair bounds on runs without FTS overflow (campaign X1 stage A). -/
theorem caseCSmallBound_of
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBoundOn ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.WPair.NoOverflow
      ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBoundNO SigGolfCandidate.T3.Security.BPair.pairTerm) :
    ClaudeWCT.W9.T3.Security.Wots.CaseCSmallBound :=
  ClaudeWCT.W9.T3.Security.CaseC.caseC_small_bound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    ClaudeWCT.W9.T3.Security.CaseC.caseCSplitInterface ClaudeWCT.W9.T3.Security.WPair.NoOverflow
    ClaudeWCT.W9.T3.Security.Wots.nearTerm SigGolfCandidate.T3.Security.BPair.pairTerm
    ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 hnear hpair
end ClaudeWCT.W9.T3.Secc
end

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (LeafAddr entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceMessages_lower (answers : Answers) (index : Nat) (hidx : index < 2^31)
    (n : Nat) (hn : 1 ≤ n) (hn4 : n < 4) :
    CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      WCT9.LayerMsg.pair
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2 := by
  have hl : (Fin.ofNat 4 (n-1) : Layer).val < 3 := by
    rw [Extract.ofNat_val (n-1) (by omega)]; omega
  have hm : CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      leafMsg answers (routeLeaf index (Fin.ofNat 4 (n-1))) := by
    unfold CanonicalRef.sourceMessages leafMsg
    simp only [routeLeaf, hl, dite_true]
  rw [hm, WotsExtract.leafMsg_route answers index _ hidx]
  exact Extract.honestMsg_lower answers index n hn (by omega)

theorem sourceMessages_bottom (answers : Answers) (index : Nat) (hidx : index < 2^31) :
    CanonicalRef.sourceMessages answers (routeLeaf index 3) =
      WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2 := by
  have hroute : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
    change index / 64 * 64 + (index / 1) % 64 = index
    rw [Nat.div_one]
    omega
  simp only [CanonicalRef.sourceMessages, routeLeaf, show ¬ (3 : Layer).val < 3 by decide,
    dite_false, hroute, Nat.mod_eq_of_lt hidx]

theorem layers_source_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2^31)
    (msg : WCT9.LayerMsg) (hfit : Extract.msgFits 3 msg)
    (h : evalWithAnswerFn answers (layersCanonicalBC w index 4 msg) = some (Extract.honestRoot answers 0 0)) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
      (entriesOf answers (queried answers (layersCanonicalBC w index 4 msg))) ∨
    ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w index lay) ∧
      msg = WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2) := by
  have hs := layersCanonicalBC_wots_walk answers (CanonicalRef.sourceMessages answers) w index hidx
    (fun lay => CanonicalRef.sourceMessages_fit answers (routeLeaf index lay))
    (sourceMessages_lower answers index hidx) 4 (by decide) le_rfl msg hfit h
  rcases hs with hp | ⟨hg, hm⟩
  · exact Or.inl hp
  · right
    refine ⟨fun lay => hg lay lay.isLt, ?_⟩
    change msg = CanonicalRef.sourceMessages answers (routeLeaf index 3) at hm
    exact hm.trans (sourceMessages_bottom answers index hidx)
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_source_walk (answers : Answers) (message : Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk w) = true) :
    ∃ output : HashOutput,
      (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk w) ∧
      output.toNat / 2^242 % 16384 < 791 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk w))) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w (WCT9.digestIndex output) lay) ∧
          evalWithAnswerFn answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) =
            CanonicalRef.forestCommitment answers (WCT9.digestIndex output) ∧
          ∀ q ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
            q ∈ queried answers (Paired.verifyP message pk w))) := by
  obtain ⟨output, top, hd, hf, hl, hqD, hqF, hqL⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨hcounter, houtput, hquery⟩ := Paired.digestP_success answers message w output hd
  obtain ⟨hgate, hrank, hforest, hforestQ⟩ := Paired.ftsP_success answers w output top hf
  refine ⟨output, hcounter, houtput, hqD _ ?_, hgate, hrank, ?_⟩
  · rw [hquery]
    exact List.mem_singleton_self _
  · have hidx : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by norm_num)
    rcases layers_source_walk answers w (WCT9.digestIndex output) hidx (.pair top.1 top.2) trivial
      (hpk ▸ hl) with hp | ⟨hg, hmsg⟩
    · exact Or.inl (hp.mono (entriesOf_mono hqL))
    · refine Or.inr ⟨hg, hforest.trans ?_, ?_⟩
      · exact Prod.ext (WCT9.LayerMsg.pair.inj hmsg).1 (WCT9.LayerMsg.pair.inj hmsg).2
      · intro q hq
        exact hqF q (hforestQ ▸ hq)
end ClaudeWCT.W9.T3.Security.CanonicalExtract
/-! r3h HonestN: the honest expand output is `witEncN` (img-v6 nonce pads). -/
namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] T3M.Paired.witEncN

theorem forest_openings_shape_N (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (ho : ForestOpenings answers (T3M.Paired.witEncN output w) (digestIndex output)
      (rawChildFromOutput output) (fun coord => embed (forestRank output coord.val))) :
    w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  apply T3M.Paired.forest_eq_of_coordinates
  · intro coord i
    rw [buildForest_coordinateValues]
    have hc := ((ho.2 coord).2.1 i).1
    change V3.reveal (T3M.Paired.witEncN output w) coord.val i.val
      (wordDigit (forestRank output coord.val) i) =
      ClaudeWCT.WCT9.chainValue answers (digestIndex output) coord.val
        (rawChildFromOutput output coord).val (forestRank output coord.val) i at hc
    have hr : V3.reveal (T3M.Paired.witEncN output w) coord.val i.val
        (wordDigit (forestRank output coord.val) i) =
        T3M.Paired.coordinateValues w.signature.forest coord i := by
      unfold V3.reveal
      split
      · exact T3M.Paired.wleafValue_witEncN output w coord i
      · exact T3M.Paired.wchainValue_witEncN output w coord i
    exact hr.symm.trans hc
  · intro coord level hl
    rw [buildForest_coordinatePath answers output coord level hl]
    have hp := SharedV3.physical_lt coord.val (rawChildFromOutput output coord).val
      (rawChildFromOutput output coord).isLt
    have hmax : level≤SharedV3.lastLevel coord.val+1 := by
      by_cases he : coord.val < 8 ∧ coord.val % 2 = 0
      · simp only [if_pos he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
      · simp only [if_neg he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
    have hc := (ho.2 coord).2
    by_cases hle : level≤SharedV3.lastLevel coord.val
    · have hl6 : level<6 := by
        unfold SharedV3.lastLevel at hle
        split_ifs at hle <;> omega
      have hs := PathStepGood.sibling_eq answers (T3M.Paired.witEncN output w)
        (digestIndex output) coord.val (SharedV3.physical coord.val (rawChildFromOutput output coord).val)
        level hp hl6 _ (hc.2.1 level hle)
      rw [T3M.Paired.wsibling_witEncN output w coord level (by omega)] at hs
      exact hs
    · have he : level=SharedV3.lastLevel coord.val+1 := by omega
      subst level
      rw [←T3M.Paired.wtopOther_witEncN output w coord]
      exact hc.2.2
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (LeafAddr)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Paired.witEncN CanonicalRef.sourceMessages

theorem good_shape_witEncN (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay) :
    ∀ lay, HonestHint answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay → ∃ digits, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay)) (w.counters lay)))) =
      some digits ∧ w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 digits) := by
  exact good_shape_readout answers (CanonicalRef.sourceMessages answers) (WCT9.digestIndex output)
    (Paired.witEncN output w) w.signature w.counters hg (PairedNonce.wbcCtr_witEncN output w)
    (fun lay => sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) lay))
    (Paired.wvalueFor_witEncN output w) (Paired.wpath_witEncN output w)
end ClaudeWCT.W9.T3.Security.CanonicalExtract


namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoveredMessage_top_source (answers : Answers) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (index : Nat) (input : WCT9.LayerMsg) (result : RecoveredLayers) (messages : Layer → WCT9.LayerMsg)
    (topFloor : Nat)
    (hinput : input = messages 3)
    (hlower : ∀ n, n < 3 → messages (Fin.ofNat 4 n) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).2)
    (hselections : ∀ lay : Layer, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (if lay = 0 then topFloor else hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1
        (recoveredMessage answers sig index 4 input result.digits lay) 0 (WCT9.searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true))
    (hshape : ∀ lay : Layer, lay ≠ 0 → ∃ digits,
      WCT9.CanonicalPolicy.decode lay (evalWithAnswerFn answers (WCT9.encodingHash lay
        (WCT9.layerEncodingInput lay (route index lay).2 (route index lay).1 (messages lay)
          (result.counters.getD lay.val 0)))) = some digits ∧
      sig.layers lay = piecesSignature lay
        (WCT9.wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    recoveredMessage answers sig index 4 input result.digits 0 = messages 0 := by
  have step (lay : Layer) (hl : lay ≠ 0)
      (hm : recoveredMessage answers sig index 4 input result.digits lay = messages lay) :
      sig.layers lay = piecesSignature lay
        (WCT9.wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) ∧
      Cost.ValidDigits lay (result.digits.getD lay.val []) := by
    have hs := hselections lay
    rw [hm] at hs
    have hlim := WCT9.searchLimit_le lay
    have hp := (canonical_search_some' answers lay
      (if lay = 0 then topFloor else hintFloor sig.policyHints lay)
      (route index lay).2 (route index lay).1 (messages lay) (WCT9.searchLimit lay) 0
      (result.counters.getD lay.val 0) (result.digits.getD lay.val []) (result.lows.getD lay.val true)
      (by unfold counterLimit at hlim; omega) hs).2.2.2
    have hd := (WCT9.CanonicalPolicy.producerDecodeAt_spec hp).1
    obtain ⟨ds, hds, hfields⟩ := hshape lay hl
    have heq := Option.some.inj (hds.symm.trans hd)
    subst ds
    exact ⟨hfields, canonical_decode_valid hd⟩
  have h3 := step 3 (by decide) (by change input = messages 3; exact hinput)
  have h2 := step 2 (by decide) (by
    change WCT9.LayerMsg.pair
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).1
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).2 = messages 2
    have hp := recoveredPair_of_pieces answers sig index 3 (by decide) _ h3.2 h3.1
    change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3
      (result.digits.getD 3 [])) = WCT9.builtPair answers 3 (route index 3).2 at hp
    rw [hp]
    exact (hlower 2 (by decide)).symm)
  have h1 := step 1 (by decide) (by
    change WCT9.LayerMsg.pair
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).1
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).2 = messages 1
    have hp := recoveredPair_of_pieces answers sig index 2 (by decide) _ h2.2 h2.1
    change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2
      (result.digits.getD 2 [])) = WCT9.builtPair answers 2 (route index 2).2 at hp
    rw [hp]
    exact (hlower 1 (by decide)).symm)
  change WCT9.LayerMsg.pair
    (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).1
    (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).2 = messages 0
  have hp := recoveredPair_of_pieces answers sig index 1 (by decide) _ h1.2 h1.1
  change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1
    (result.digits.getD 1 [])) = WCT9.builtPair answers 1 (route index 1).2 at hp
  rw [hp]
  exact (hlower 0 (by decide)).symm

theorem expanded_canonical_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
        forestCommitment answers (WCT9.digestIndex output)) :
    ∃ (digits : List (List Nat)) (lows : List Bool),
      policyHintsValid w.signature.policyHints digits lows
        (conditionalCredit output) = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (if lay = 0 then conditionalTopFloor output else hintFloor w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay, digits.getD lay.val [], lows.getD lay.val true)) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨_, counter, result, c, _, hr, hvalid, hsig, _, hcs, hhigh⟩ := Paired.expandN_selections answers message pk sig output w he
  have hs := recoverHintedLayers_selections_at answers (fillTopSignature sig 0)
    (WCT9.digestIndex output) (((fillTopSignature sig 0).layers 0).path WCT9.topJ)
    (conditionalTopFloor output) 4 le_rfl _ result hr
  let input : WCT9.LayerMsg := .pair
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2
  have hsel : ∀ lay, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (if lay = 0 then conditionalTopFloor output else hintFloor w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers w.signature (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
          result.lows.getD lay.val true) := by
    intro lay
    have hx := hs.2.2.2 lay lay.isLt
    change evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (if lay = 0 then conditionalTopFloor output else hintFloor sig.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers (fillTopSignature sig 0) (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = _ at hx
    rw [recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt 0] at hx
    rw [hsig, hints_retained, recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt c]
    exact hx
  have hshape0 := good_shape_witEncN answers output w hg
  have hi : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by decide)
  have lower : ∀ n, n < 3 → CanonicalRef.sourceMessages answers
      (routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 n)) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).2 := by
    intro n hn
    have hm := sourceMessages_lower answers (WCT9.digestIndex output) hi (n+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, Extract.honestPair_eq] using hm
  have hin : input = CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 3) := by
    dsimp only [input]
    rw [hf, sourceMessages_bottom answers _ hi]
  have hshapeL : ∀ lay : Layer, lay ≠ 0 → ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay hl
    simpa only [hcs lay] using hshape0 lay (honestHint_lower answers _ _ _ hl)
  have htop := recoveredMessage_top_source answers w.signature (WCT9.digestIndex output) input result
    (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    (conditionalTopFloor output) hin lower hsel hshapeL
  -- The expander's hint is the producer's choice at the (source) top row.
  have hhint0 : HonestHint answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) 0 := by
    have hs0 := hsel 0
    rw [htop] at hs0
    have hlim := WCT9.searchLimit_le 0
    have hlow := (canonical_search_some' answers 0 (conditionalTopFloor output)
      (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
      (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (WCT9.searchLimit 0) 0
      (result.counters.getD 0 0) (result.digits.getD 0 []) (result.lows.getD 0 true)
      (by unfold counterLimit at hlim; omega) hs0).2.2.1
    obtain ⟨-, hpad, hhi⟩ := hg 0
    obtain ⟨left, right, hm⟩ := sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) 0)
    unfold HonestHint
    rw [PairedNonce.wbcCtr_witEncN, hpad, hhi, Paired.wtopHigh_witEncN, hhigh]
    have hrow : pad64 (layerEncodingInputP 0 (route (WCT9.digestIndex output) 0).2
        (route (WCT9.digestIndex output) 0).1 (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0))
        (w.counters 0) 0 (wbcRight (Paired.witEncN output w)) 1) =
        pad64 (WCT9.layerEncodingInput 0 (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
          (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (w.counters 0)) := by
      rw [hm]; rfl
    rw [hrow, hcs 0, hlow]
    exact WCT9.verificationAnswer_honest 0 _
  have hshape' : ∀ lay, ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay
    by_cases hl : lay = 0
    · subst hl
      simpa only [hcs 0] using hshape0 0 hhint0
    · exact hshapeL lay hl
  have hall := recoveredSelections_canonical_at answers w.signature (WCT9.digestIndex output)
    input result (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    (conditionalTopFloor output) hin lower hsel hshape'
  refine ⟨result.digits, result.lows, ?_, ?_, fun lay => (hall lay).2⟩
  · rw [hsig, hints_retained]
    exact hvalid
  · intro lay
    rw [hcs lay]
    exact (hall lay).1
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_canonical_or_collision (answers : Answers) (message : Message) (pk : Digest)
    (wb : ClaudeWCT.W9.T3M.WBytes) (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk wb) = true) :
    ∃ output : HashOutput,
      (wdc wb).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk wb) ∧
      output.toNat / 2^242 % 16384 < 791 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk wb))) ∨
        Extract.Paired.FtsHitIn answers (queried answers (Paired.verifyP message pk wb)) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
          Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))) := by
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ := verifyP_source_walk answers message pk wb hpk hv
  refine ⟨output,hc,hd,hq,hgate,hrank,?_⟩
  rcases hcases with hp | ⟨hg,hforest,hsub⟩
  · exact Or.inl hp
  · rcases Extract.Paired.forest_extract answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) (Extract.Paired.branchCompatible_output output) hforest with ho | hh
    · exact Or.inr (Or.inr ⟨hg,ho⟩)
    · exact Or.inr (Or.inl ((Extract.Paired.forest_hit_fts answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) hh).mono hsub))
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_canonical_selections (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ (digits : List (List Nat)) (lows : List Bool),
      policyHintsValid w.signature.policyHints digits lows
        (conditionalCredit output) = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (if lay = 0 then conditionalTopFloor output else hintFloor w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay,digits.getD lay.val [],lows.getD lay.val true)) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨result,hs,hrho,hhints,hforest,hpieces,hdigest,hcounters⟩ :=
    signFromOutput_components answers cache rho counter output w he
  have facts := searchPreparedLayers_some_at answers cache (WCT9.digestIndex output) _ _ result
    (conditionalCredit output) (conditionalTopFloor output) hs
  have hi : WCT9.digestIndex output<2^31 := WCT9.digestIndex_lt output
  refine ⟨result.digits, result.lows, ?_, ?_, ?_⟩
  · rw [hhints]
    exact facts.hints_valid
  · intro lay
    rw [hhints,hcounters lay]
    have hx := facts.hinted_searches_at lay
    rw [buildForest_commitment] at hx
    have hm : CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay) =
        (if lay=3 then .pair (forestCommitment answers (WCT9.digestIndex output)).1
          (forestCommitment answers (WCT9.digestIndex output)).2 else
          let lower : Layer := Fin.ofNat 4 (lay.val+1)
          .pair (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).1
            (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).2) := by
      by_cases h3 : lay = 3
      · subst lay
        exact sourceMessages_bottom answers _ hi
      · have hl : lay.val < 3 := by
          have hn : lay.val ≠ 3 := fun h => h3 (Fin.ext h)
          have := lay.isLt
          omega
        have he : (Fin.ofNat 4 lay.val : Layer) = lay := Fin.ext (Nat.mod_eq_of_lt lay.isLt)
        have hx := sourceMessages_lower answers _ hi (lay.val+1) (by omega) (by omega)
        simpa only [if_neg h3,Nat.add_sub_cancel,he,Extract.honestPair_eq] using hx
    rw [hm]
    exact hx
  · intro lay
    rw [hpieces lay,facts.honest_pieces hcache hi lay]
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expanded_eq_signer_signature (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w signed : SigGolfCandidate.Research.SharedForest.Witness) (counter : BitVec 32)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (signFromOutput cache sig.rho counter output) = some signed) :
    w.signature = signed.signature := by
  have hforest := Extract.Paired.forest_openings_shape_N answers output w ho
  obtain ⟨_, _, _, c, _, _, _, hsig, _, _⟩ := Paired.expandN_selections answers message pk sig output w he
  have hforestSig : sig.forest = w.signature.forest := by rw [hsig];rfl
  have hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
      forestCommitment answers (WCT9.digestIndex output) := by
    rw [hforestSig,hforest]
    exact recoverForest_commitment answers _ _ _
  obtain ⟨da,la,hva,hsa,hpa⟩ := expanded_canonical_selections answers message pk sig output w he hg hf
  obtain ⟨db,lb,hvb,hsb,hpb⟩ := signFromOutput_canonical_selections answers cache hcache sig.rho counter output signed hs
  obtain ⟨_,_,hrho,_,hfs,_,_,_⟩ := signFromOutput_components answers cache sig.rho counter output signed hs
  apply signature_unique_of_selections_at answers (WCT9.digestIndex output)
    (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    w.signature signed.signature w.counters signed.counters da db la lb
    (conditionalCredit output) (conditionalTopFloor output) _ (hforest.trans hfs.symm)
    hva hvb hsa hsb hpa hpb
  rw [hsig,nonce_retained,hrho]

 theorem same_nonce_signed_wire (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig signedSig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) = some signedSig)
    (hrho : sig.rho = signedSig.rho) :
    SharedCodec.sigBC sig = SharedCodec.sigBC signedSig := by
  obtain ⟨counter,N,signed,hd,hsigned,hsig⟩ := signPayload_components answers cache message signedSig hs
  obtain ⟨_,_,hnonce,_,_,_,_,_⟩ := signFromOutput_components answers cache
    (evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message)) counter N signed hsigned
  have hr : sig.rho = evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message) :=
    hrho.trans ((congrArg (fun s : SigGolfCandidate.Research.SharedForest.Signature => s.rho) hsig).symm.trans hnonce)
  obtain ⟨_,ec,_,c,hed,_,_,hw,_,_⟩ := Paired.expandN_selections answers message pk sig output w he
  rw [hr,hd] at hed
  have hout : N=output := congrArg Prod.snd (Option.some.inj hed)
  subst N
  have heq := expanded_eq_signer_signature answers cache hcache message pk sig output w signed counter he hg ho
    (by rw [hr];exact hsigned)
  calc
    SharedCodec.sigBC sig = SharedCodec.sigBC (fillTopSignature sig c) := (SharedCodec.sigBC_fillTopSignature sig c).symm
    _ = SharedCodec.sigBC w.signature := by rw [hw]
    _ = SharedCodec.sigBC signedSig := by rw [heq,hsig]
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem fresh_witness_not_signed_digest (log : QueryLog Requests) (message : Message)
    (wb : WBytes) (rho : Digest) (hfresh : Final.Paired.Fresh log (.witness message wb)) :
    ¬ SignedDigest log message rho := by
  rintro ⟨entry,hin,hm,sig,he,_⟩
  exact hfresh ⟨entry,hin,hm,by rw [he];rfl⟩

theorem fresh_signature_not_signed_digest (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (log : QueryLog Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (authenticatedSign published entry.1))
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hfresh : Final.Paired.Fresh log (.signature message sig))
    (he : evalWithAnswerFn answers (T3M.Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, CanonicalExtract.Good answers (CanonicalRef.sourceMessages answers)
      (T3M.Paired.witEncN output w) (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (T3M.Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val))) :
    ¬ SignedDigest log message sig.rho := by
  rintro ⟨entry,hin,hm,signed,hsigned,hrho⟩
  have hreply := hlog entry hin
  rw [hsigned,eval_authenticatedSign] at hreply
  have hsource : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload published message) = some signed := by
    by_cases hc : entry.1.cache = published
    · rw [if_pos hc,hc,hm] at hreply
      exact hreply.symm
    · rw [if_neg hc] at hreply
      cases hreply
  have hwire := CanonicalExtract.same_nonce_signed_wire answers published hcache message pk sig signed output w
    he hg ho hsource hrho.symm
  apply hfresh
  refine ⟨entry,hin,hm,?_⟩
  rw [hsigned,Option.map_some,hwire]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem checkForgery_canonical_or_collision (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (pk : Digest)
    (hpk : pk = Extract.honestRoot answers 0 0) (log : QueryLog Final.Paired.Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (WPair.Paired.authenticatedSign published entry.1))
    (forgery : Final.Paired.ForgeryP)
    (haccept : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
        (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      Extract.Paired.FtsHitIn answers (queried answers (Final.Paired.checkForgeryP pk log forgery)) ∨
      ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 791 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb) := by
  obtain ⟨hfresh,message,wb,hw,hv,hsub⟩ := Final.Paired.check_accepting answers pk log forgery haccept
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ :=
    verifyP_canonical_or_collision answers message pk wb hpk hv
  rcases hcases with hp | hh | ⟨hg,ho⟩
  · exact Or.inl (hp.mono (entriesOf_mono hsub))
  · exact Or.inr (Or.inl (hh.mono hsub))
  · refine Or.inr (Or.inr ⟨message,wb,output,hw,hc,hd,hsub _ hq,hgate,hrank,hg,ho,?_⟩)
    cases forgery with
    | witness sourceMessage sourceWitness =>
        obtain ⟨hm,hb⟩ := hw
        subst sourceMessage sourceWitness
        exact WPair.Paired.fresh_witness_not_signed_digest log message wb (wrho wb) hfresh
    | signature sourceMessage sig =>
        obtain ⟨hm,he⟩ := hw
        subst sourceMessage
        obtain ⟨N,w,hn,rfl⟩ := Paired.expandB_some answers message pk sig wb he
        have hout : N = output := (Paired.expandN_digest answers message pk sig N w hn).symm.trans hd
        subst N
        rw [Paired.expandN_nonce answers message pk sig output w hn]
        exact WPair.Paired.fresh_signature_not_signed_digest answers published hcache log hlog
          message pk sig output w hfresh hn hg ho
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.CanonicalExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FreshForestAt (answers : Answers) (pk : Digest) (log : QueryLog Final.Paired.Requests)
    (forgery : Final.Paired.ForgeryP) : Prop :=
  ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 791 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb)

def FreshForestCase (adversary : Final.Paired.AdversaryP)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = Extract.honestRoot z.2 0 0 ∧
    generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop z.2) ∧
    (∀ entry ∈ interaction.value.2,
      entry.2 = evalWithAnswerFn z.2 (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    ∃ forgery, interaction.value.1 = some forgery ∧
      evalWithAnswerFn z.2 (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) = true ∧
      FreshForestAt z.2 generated.value.1 interaction.value.2 forgery

theorem completed_split_canonical (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) :
    CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z := by
  by_cases hab : CaseABEv combinedEvent adversary z
  · exact Or.inl hab
  right
  unfold CaseABEv CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated,interaction,checked,hsplit,forgery,hf,hnot⟩ := hab
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  obtain ⟨_,hpk,hcache,hlog,hverdict⟩ := hsplit.facts z.2 ha hclean.1
  obtain ⟨forgery',hf',hcheck,_⟩ := PairedReference.Ref.verdict_accepts z.2 _ _ hverdict
  have heq : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst forgery'
  rcases CanonicalExtract.checkForgery_canonical_or_collision z.2 generated.value.2 hcache
      generated.value.1 hpk interaction.value.2 hlog forgery hcheck with hp | hh | hgood
  · exact (hnot ⟨hcheck,Or.inl hp⟩).elim
  · exact (hnot ⟨hcheck,Or.inr (PairedReference.ftsHitIn_structuralHitTrace hh)⟩).elim
  · exact ⟨generated,interaction,checked,hsplit,hpk,hcache,hlog,forgery,hf,hcheck,hgood⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [← PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) (probEvent_or_le _ _ _)
  intro z hz hclean
  rcases completed_split_canonical adversary q hq z hz hclean with hab | hf
  · exact Or.inl ⟨hclean,hab⟩
  · exact Or.inr ⟨hclean,hf⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_forest_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    ∀ query ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
      query ∈ queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  obtain ⟨_,m',w',hw',hv,hq⟩ := Final.Paired.check_accepting answers pk log forgery hcheck
  obtain ⟨rfl,rfl⟩ := PairedReference.Ref.witnessOf_unique hw hw'
  obtain ⟨out,top,hd',hf,_,_,hqF,_⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨_,hout,_⟩ := Paired.digestP_success answers message w out hd'
  have he : out = output := hout.symm.trans hd
  rw [he] at hf hqF
  obtain ⟨_,_,_,hforestQ⟩ := Paired.ftsP_success answers w output top hf
  intro query hquery
  exact hq query (hqF query (hforestQ ▸ hquery))

theorem checker_slot_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WPair.Paired.deficit output k t) :
    (.inl (.inr (Guess.honestProbe answers (WPair.Paired.chainOf output k t,p))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  apply checker_forest_queries answers pk log forgery message w output hw hd hcheck
  rw [WPair.Paired.honestProbe_slot]
  have hp' : p.val = 4-WCT9.digit (WCT9.embed (forestRank output k.val)) t := hp
  rw [hp']
  apply Extract.Paired.active_slot_queried answers w (WCT9.digestIndex output)
    (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) (WCT9.digestIndex_lt output) ho
  have hplt := p.isLt
  omega

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FullCovered (answers : Answers) (log : QueryLog Final.Paired.Requests) (output : HashOutput) : Prop :=
  ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k t

def NearGuess (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (output : HashOutput) (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ (k : Fin 9) (t : Fin 6) (cell : Guess.GCoord),
    cell.1 = WPair.Paired.chainOf output k t ∧
    cell.2.val = 4-WPair.Paired.deficit output k t ∧
    WPair.Paired.GuessedIn answers log trace cell ∧
    ∀ k' t', (k',t') ≠ (k,t) →
      WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k' t'

def PairGuessIn (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ cell cell' : Guess.GCoord, cell.1 ≠ cell'.1 ∧
    WPair.Paired.GuessedIn answers log trace cell ∧ WPair.Paired.GuessedIn answers log trace cell'

theorem checker_coverage_cases (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) :
    FullCovered answers log output ∨
      NearGuess answers log output (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      PairGuessIn answers log (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) := by
  let trace := entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))
  let slot (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t) : Guess.GCoord :=
    (WPair.Paired.chainOf output k t,⟨4-WPair.Paired.deficit output k t,by omega⟩)
  have make (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t)
      (hu : ¬WPair.Paired.ChainCovered (WPair.Paired.loggedOutputs answers log)
        (WPair.Paired.chainOf output k t) (4-WPair.Paired.deficit output k t)) :
      WPair.Paired.GuessedIn answers log trace (slot k t ha) := by
    refine ⟨hu,answers (.inl (.inr (Guess.honestProbe answers (slot k t ha)))),?_⟩
    exact WotsExtract.mem_entriesOf (checker_slot_queries answers pk log forgery message w output
      hw hd hcheck ho k t (slot k t ha).2 rfl)
  rcases WPair.Paired.caseC_slots (WPair.Paired.loggedOutputs answers log) output with
    hall | ⟨k,t,ha,hu,hrest⟩ | ⟨k,t,k',t',hne,ha,hu,ha',hu'⟩
  · exact Or.inl hall
  · exact Or.inr (Or.inl ⟨k,t,slot k t ha,rfl,rfl,make k t ha hu,hrest⟩)
  · exact Or.inr (Or.inr ⟨slot k t ha,slot k' t' ha',WPair.Paired.chainOf_ne hne,
      make k t ha hu,make k' t' ha' hu'⟩)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The fully covered fresh-forest case, restricted to complete source tables. -/
def FullForestEvent (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<791 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      FullCovered A interaction.value.2 output

theorem paired_recordMatches (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Prod.fst <$> ClaudeWCT.Bank.Paired.bankSpec.authenticatedRecord
      ClaudeWCT.Bank.Paired.payAfterDigest published request =
        PairedOuter.FullGame.authenticatedSign published request :=
  ClaudeWCT.Bank.Paired.record_erasure published request

theorem paired_bank_search (rho : Digest) (message : Message) :
    ClaudeWCT.Bank.Paired.bankSpec.search rho message 0 ClaudeWCT.Bank.Paired.bankSpec.limit =
      sharedDigestSearch rho message 0 WCT9.digestAttemptLimit :=
  (ClaudeWCT.Bank.Paired.digestSearch_public rho message WCT9.digestAttemptLimit 0).symm

theorem paired_bank_covered (X : List HashOutput) (N : HashOutput)
    (h : ∀ k t, WPair.Paired.SlotCovered X N k t) :
    ClaudeWCT.Bank.Paired.bankSpec.covered X N := by
  apply (ClaudeWCT.Bank.Paired.covered_source X N).mpr
  exact h

theorem full_event_potential (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.bankSpec.potential q b.2 := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  apply PairedBankLink.full_potential ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
    ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
    paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
    generated interaction checked hsplit hlen
    (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
  · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
      message (wrho w) (wdc w) hcomp hfresh
  · change ClaudeWCT.Bank.Paired.admissible N=true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  · exact hcover

theorem completed_full_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-(1023/1024 : ENNReal))≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (CaseC.theta+1/64)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  apply PairedBankLink.completed_event_le_shared ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches ClaudeWCT.Bank.Paired.payNotDigest
    ClaudeWCT.Bank.Paired.payAvoids (FullForestEvent adversary q) adversary q hq rate hrate
  intro b hb tables hfull
  exact full_event_potential adversary q hq b hb _
    (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) hfull
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem full_event_target_covered (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    b.2.1.dead=false ∧ ∃ N∈b.2.1.targets, ClaudeWCT.Bank.Paired.admissible N=true ∧
      ClaudeWCT.Bank.Paired.Covered b.2.1.exposures N := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  have hadm : ClaudeWCT.Bank.Paired.admissible N=true := by
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  have hc : b.2.1.dead=false ∧ N∈b.2.1.targets ∧
      ClaudeWCT.Bank.Paired.bankSpec.covered b.2.1.exposures N := by
    apply PairedBankLink.full_target_covered ClaudeWCT.Bank.Paired.bankSpec
      ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
      ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
      paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
      generated interaction checked hsplit hlen
      (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
    · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
        message (wrho w) (wdc w) hcomp hfresh
    · change ClaudeWCT.Bank.Paired.admissible N=true
      rw [ClaudeWCT.Bank.Paired.admissible_source]
      simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
    · exact hcover
  
  exact ⟨hc.1,N,hc.2.1,hadm,hc.2.2⟩

theorem full_event_flexible_potential (theta : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.flexiblePotential theta q b.2 := by
  obtain ⟨halive,N,hN,hadm,hcov⟩ := full_event_target_covered adversary q hq b hb A hA hfull
  exact ClaudeWCT.Bank.Paired.flexible_potential_win theta q b.2 halive hfull.2.1
    (Or.inr ⟨N,hN,hadm,hcov⟩)

theorem completed_flexible_full_bound (theta rate : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-theta)≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (theta+1/1024)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  rw [PairedBankLink.completed_event_eq]
  have he := congrArg (fun law : PMF (Bool × QueryRecorded.State) =>
    expectedValue law (PairedBankLink.completedWeight (FullForestEvent adversary q)))
      (PairedBankLink.recordedExperiment_eq ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)
  rw [PMF.monad_map_eq_map,CaseC.expectedValue_pmf_map] at he
  rw [he]
  refine (ClaudeWCT.Bank.Paired.flexible_event_le theta rate hrate (PairedBankLink.rest adversary) q
    (PairedBankLink.completedWeight (FullForestEvent adversary q)) (fun _ => probEvent_le_one) ?_).trans ?_
  · intro b hb hnonzero
    by_cases hex : ∃ tables, FullForestEvent adversary q (b.1,b.2.2)
        (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables)
    · obtain ⟨tables,ht⟩ := hex
      exact full_event_flexible_potential theta adversary q hq b hb _
        (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) ht
    · exfalso
      apply hnonzero
      unfold PairedBankLink.completedWeight
      simp only [probEvent_eq_tsum_ite]
      have hfalse : ∀ tables, ¬FullForestEvent adversary q (b.1,b.2.2)
          (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables) :=
        fun tables ht => hex ⟨tables,ht⟩
      simp [hfalse]
  · exact add_le_add (mul_le_mul' le_rfl
      (PairedBankLink.expectedBirths_le_shared ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)) le_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The remaining fresh-forest cases, with a predicate on the actual checker trace. -/
def PartialForestEvent
    (Q : Answers → QueryLog Final.Paired.Requests → HashOutput → List Entry → Prop)
    (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<791 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      Q A interaction.value.2 output
        (entriesOf A (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)))

abbrev NearForestEvent := PartialForestEvent NearGuess
abbrev PairForestEvent := PartialForestEvent (fun A log _ => PairGuessIn A log)

def IncompleteForestEvent (adversary : Final.Paired.AdversaryP)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    ¬∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature

theorem completed_forest_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1)
    (hfresh : FreshForestCase adversary z) :
    FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 := by
  obtain ⟨generated,interaction,checked,hsplit,hpk,hcache,hsig,forgery,hforgery,hcheck,
    message,w,N,hw,hctr,hN,hquery,hgate,hranks,hgood,hopen,hfresh⟩ := hfresh
  by_cases hcomp : ∀ message, ∃ signature, evalWithAnswerFn z.2
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature
  · obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
    obtain ⟨_,_,_,_,hverdict⟩ := hsplit.facts z.2 ha hclean.1
    have hlen : interaction.value.2.length≤2^32 := by
      simp only [PairedOuter.GameWith.verdict,hforgery,PairedOuter.PaddedGame.checker,
        evalWithAnswerFn_bind,evalWithAnswerFn_pure,Bool.and_eq_true,decide_eq_true_eq] at hverdict
      exact hverdict.1
    rcases checker_coverage_cases z.2 generated.value.1 interaction.value.2 forgery
      message w N hw hN hcheck hopen with hc | hc | hc
    · exact Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩
    · exact Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨generated,interaction,checked,hsplit,hcomp⟩))

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem completed_forest_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  have h := Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq)
    (fun z hz (h : QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z) =>
      completed_forest_cases adversary q hq z hz h.1 h.2)
  refine h.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem GameSplit.unique_log_events {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool}
    {generated generated' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction interaction' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked checked' : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked)
    (h' : GameSplit adversary result generated' interaction' checked') :
    generated=generated' ∧ interaction=interaction' ∧ checked.events=checked'.events := by
  have hev : result.events=generated'.events++(interaction'.events++checked'.events) := by rw [h'.2.2.2]
  obtain ⟨hg,hi⟩ := PairedBankLink.split_unique adversary result generated' h'.1 interaction' h'.2.1
    checked'.events hev generated interaction checked h
  refine ⟨hg,hi,?_⟩
  have hev' : result.events=generated.events++(interaction.events++checked.events) := by rw [h.2.2.2]
  rw [hg,hi] at hev'
  exact List.append_cancel_left (List.append_cancel_left (hev'.symm.trans hev))

theorem GameSplit.checker_entries {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (hA : CaseC.Agrees A result.state)
    (forgery : Final.Paired.ForgeryP) (hf : interaction.value.1=some forgery) :
    ∀ entry∈SigGolfCandidate.T3.Security.Wots.entriesOf A
      (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)),
      entry∈BPair.publicEntries checked.events := by
  rintro ⟨input,answer⟩ he
  obtain ⟨hq,ha⟩ := SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf_iff.mp he
  obtain ⟨prior,hprior⟩ := h.checker_event A hA forgery hf _ hq
  have hm := SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hprior
  rwa [ha] at hm
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_pair_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hpair : PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) :
    WPair.Paired.PairGuess adversary z := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hpair⟩ := hpair
  intro generated' interaction' checked' hsplit'
  obtain ⟨_,hi,hc⟩ := hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub := hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨cell,cell',hne,hg,hg'⟩ := hpair
  exact ⟨cell,cell',hne,WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hg,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell' hg'⟩

theorem completed_pair_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans (WPair.Paired.pair_guess_bound_budget adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,completed_pair_implies adversary q hq z hz h.1,h.2⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hnear : NearForestEvent adversary q (z.1.1,z.1.2.2) z.2)
    (generated' interaction' checked')
    (hsplit' : PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
      generated' interaction' checked') :
    WPair.Paired.NearIn z.2 interaction'.value.2 (BPair.publicEntries checked'.events) := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hnear⟩:=hnear
  obtain ⟨_,hi,hc⟩:=hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub:=hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨k,t,cell,hcell,hdepth,hguess,hcover⟩:=hnear
  refine ⟨hlen,WPair.Paired.cacheCompleteLog_of_complete z.2 generated.value.2
    interaction.value.2 hsig hcomp,message,wrho w,wdc w,N,cell,?_,?_,hfresh,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hguess,k,t,hcover⟩
  · apply hsub
    rw [←hN]
    exact SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf hquery
  · rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks

variable {P : Type} [Fintype P] [SampleableType P]

theorem completed_near_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.near_bound_budget S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,fun generated interaction checked hs=>
    ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
      h.2 generated interaction checked hs⟩⟩

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
theorem prefixClassCount_le_length (s : RefSample) : Contacts.prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  unfold ContactAt maskAt CanonicalRef.ContactAt
  rw [CanonicalRef.depth_source_maskAt T a b (source_bounds ha).2,
    CanonicalRef.frontierValue_source_maskAt T a b (source_bounds ha) (source_bounds hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain7 b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRowW a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; exact congrArg some hm.symm
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (Contacts.prefixRowAt_unique (answers := T) ha hb ⟨_, va, by change depth T a - 1 < depth T a; omega, rfl⟩ ⟨_, vb, by change depth T b - 1 < depth T b; omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ Contacts.contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold Contacts.contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(Contacts.mem_sourceChains7 b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _

noncomputable def prefixCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    v * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  7 / 4 + w * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    v * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))

theorem weighted_union_le {α : Type} (law : PMF α)
    (E Failed Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst : α → Prop)
    (q : Nat) (w v EP EE EO error : ENNReal) (hwv : w+v=1)
    (hsplit : ∀ s, E s → Failed s ∨ Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    (hmatch : Pr[Match | law] ≤ 7/(4*2^128) * EE)
    (hstruct : Pr[Structural | law] ≤ (2^128:ENNReal)⁻¹ * EO)
    (hedge : Pr[TwoEdge | law] ≤ (twoEdgeRate q * EP + (1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128))
    (htwo : Pr[TwoContacts | law] ≤
      (4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error)
    (hmarker : Pr[MarkerFirst | law] ≤
      2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error)
    (hcontact : Pr[ContactFirst | law] ≤
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))
    (hany : Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] ≤
      ((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)) :
    Pr[E | law] ≤ Pr[Failed | law] + prefixCoeff q w v/2^128*EP +
      encodingCoeff q w v/2^128*EE + (2^128:ENNReal)⁻¹*EO + errCoeff q w v*error := by
  have h0 : Pr[E | law] ≤ Pr[Failed | law] +
      Pr[fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] :=
    (probEvent_mono'' hsplit).trans (probEvent_or_le _ _ _)
  have h1 := probEvent_le_six_split law
    (fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst (fun _ h => h) w v hwv
  refine (h0.trans (add_le_add le_rfl h1)).trans ?_
  calc _ ≤ Pr[Failed | law] +
      ((7/(4*2^128):ENNReal)*EE + (2^128:ENNReal)⁻¹*EO +
      (w*((twoEdgeRate q*EP+(1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128) +
      ((4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error) +
      (2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error) +
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128))) +
      v*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))) := by
        gcongr
    _ = _ := by
      unfold prefixCoeff encodingCoeff errCoeff twoEdgeRate
      simp only [div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by norm_num : (4:ENNReal)≠0)) (Or.inl (by norm_num : (4:ENNReal)≠⊤))]
      ring
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩

theorem chainOf_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) ≤ Contacts.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, Core.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Core.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]

def MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a

def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a

def ReferenceFailed (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none

def EncodingMatch (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L ≠ none ∧
   CanonicalRef.EncodingMatchAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace L

def Structural (s : RefSample) : Prop :=
 CanonicalExtract.StructuralHitSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace

def TwoEdge (s : RefSample) : Prop :=
 ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a

def TwoContacts (s : RefSample) : Prop :=
 ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace b

def MarkerFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a
def ContactFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst s.answers s.trace a

def Combined (s : RefSample) : Prop :=
 CanonicalExtract.WotsPrimitiveSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace
/-- Stage 2 (C3, #866): `RowPad` is a triple (the row tweak's high word is a witness pad), so this is #866's
`SmallA.chainRowW_ne_encRow` (chain headers and row tweaks differ in their marker byte). -/
theorem chainRowW_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRowW a s v ≠ encRow L m c pad :=
  ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRowW_ne_encRow a s v L m c pad

theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a) (hc : CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact chainRowW_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩

theorem combined_cases (s : RefSample) (h : Combined s) :
 ReferenceFailed s ∨ EncodingMatch s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s := by
 rcases h with hp | hs
 · rcases hp with hm | hs | he | ht | ⟨a,ha,hm,hc⟩
   · obtain ⟨L,hL,hm⟩ := hm
     by_cases hf : CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none
     · exact Or.inl ⟨L,hL,hf⟩
     · exact Or.inr (Or.inl ⟨L,hL,hf,hm⟩)
   · exact Or.inr (Or.inr (Or.inl (Or.inl hs)))
   · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
   · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
   · rcases markerContact_split s.answers s.trace a hm hc with hm | hc
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a,ha,hm⟩)))))
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a,ha,hc⟩)))))
 · exact Or.inr (Or.inr (Or.inl (Or.inr hs)))

theorem structural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat)
 (hstruct : Pr[fun s => PairedReference.StructuralHitIn (PairedReference.referenceInputs adversary) s.answers s.trace |
   PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
     (2^142:ENNReal)⁻¹) :
 Pr[Structural | PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
     (2^142:ENNReal)⁻¹ := by
 refine le_trans (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ fun s hs h => ?_) hstruct
 have hin := PairedReference.reference_trace_mem adversary q s hs
 exact h.elim (fun h => CanonicalExtract.structuralHitSrc_paired h hin)
   (fun h => PairedReference.StructuralHitTrace.toHitIn h hin)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nonstructural_contact (s : RefSample)
 (h : TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s) :
 ∃a∈Contacts.sourceChains7,CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a := by
 rcases h with ⟨a,ha,hd,_,middle,_,h2⟩ | ⟨a,_,ha,_,_,hc,_⟩ | ⟨a,ha,_,_,_,hc⟩ | ⟨a,ha,_,⟨hd,value,answer,hm,hl⟩,_,_⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,by omega,middle,h2⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hd,value,answer,List.mem_of_mem_take hm,hl⟩

theorem nonstructural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
 Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s |
   PairedReference.referenceExperiment adversary q] ≤
 ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.contactCount s:ENNReal) := by
 rw [probEvent_eq_tsum_ite]
 apply ENNReal.tsum_le_tsum
 intro s
 split_ifs with h
 · obtain ⟨a,ha,hc⟩ := nonstructural_contact s h
   rw [PMF.probOutput_eq_apply]
   apply le_mul_of_one_le_right'
   have hp : 0 < Contacts.contactCount s := Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hc⟩⟩
   exact_mod_cast hp
 · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem GameSplit.keygen_value {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (ha:∀input answer,SourceReplay.known result.state input=some answer → A input=answer) :
    evalWithAnswerFn A keygen=generated.value := by
  obtain ⟨hg,hi,hc,heq⟩:=h
  have hs:result.state=checked.state:=by rw[heq]
  have hiext:SourceReplay.Extends interaction.state result.state:=by
    rw[hs]
    exact SourceReplay.run_extends _ interaction.state (checked.value,checked.state)
      (FirstHit.recorded_support _ _ _ hc)
  have hgext:SourceReplay.Extends generated.state result.state:=
    (SourceReplay.run_extends _ generated.state (interaction.value,interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hiext
  exact (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
    (generated.value,generated.state) (FirstHit.recorded_support _ _ _ hg)).eval A
    (fun input answer hk=>ha input answer (SourceReplay.known_mono _ _ hgext hk))
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_incomplete_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138 := by
  refine (Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq) ?_).trans
    (PairedSearchTable.completed_signer_failure adversary q hq)
  intro z hz hevent hcomplete
  obtain ⟨generated,interaction,checked,hsplit,hbad⟩:=hevent
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hk:=hsplit.keygen_value z.2 ha
  apply hbad
  intro message
  obtain ⟨sig,hsig⟩:=hcomplete message
  rw[hk] at hsig
  refine ⟨sig,?_⟩
  unfold SigGolfCandidate.Research.SharedForest.sign at hsig
  rw[evalWithAnswerFn_bind] at hsig
  split_ifs at hsig with hm
  · simp only[evalWithAnswerFn_pure,reduceCtorEq] at hsig
  · exact hsig

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>WPair.Paired.NearIn A log entries ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨WPair.Paired.nearIn_short h log entries hp.1,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨WPair.Paired.nearIn_mono A log entries entries' hsub hp.1,hp.2⟩)
      (fun _ _ _ hp=>hp.2) ?_)
  · intro z hz h
    exact ⟨h.1.2.1,fun generated interaction checked hs=>
      ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
        h.2 generated interaction checked hs⟩⟩
  · intro A log entries hp
    obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hp.1
    exact ⟨cell,hguess⟩

theorem completed_near_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧
      WPair.Paired.NoOverflow adversary z | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_near_le_other adversary q hq)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceSearch_complete (answers : Answers) (hgood : ContextGood answers)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceSearch answers (sourceMessages answers) L ≠ none := by
  let cache : SigGolfCandidate.T3.Cache := ⟨0,fun _=>0⟩
  exact referenceSearch_complete_of_routes answers cache
    (fun index hi => searchPreparedLayers_complete answers hgood cache index hi _ _) L hL
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.CanonicalSearch
attribute [local instance] Classical.propDecidable

theorem reference_failed_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
    Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139 := by
  refine (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ ?_).trans
    (PairedSearchTable.context_failure adversary q)
  rintro s _ ⟨L,hL,hs⟩ hgood
  exact CanonicalRef.referenceSearch_complete s.answers hgood L hL hs
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable

def PartialForestNoOverflow (adversary : Final.Paired.AdversaryP) (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  (NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨ PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) ∧
    WPair.Paired.NoOverflow adversary z

theorem completed_partial_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>(∃cell,WPair.Paired.GuessedIn A log entries cell) ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_short h log entries cell hcell⟩,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_mono A log entries entries' hsub cell hcell⟩,hp.2⟩)
      (fun _ _ _ hp=>hp.2) (fun _ _ _ hp=>hp.1))
  intro z hz h
  refine ⟨h.1.elim (fun hn=>hn.2.1) (fun hp=>hp.2.1),?_⟩
  intro generated interaction checked hs
  refine ⟨?_,h.2 generated interaction checked hs⟩
  rcases h.1 with hn | hp
  · obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=
      completed_near_implies adversary q hq z hz hn generated interaction checked hs
    exact ⟨cell,hguess⟩
  · obtain ⟨cell,cell',hne,hg,hg'⟩:=completed_pair_implies adversary q hq z hz hp generated interaction checked hs
    exact ⟨cell,hg⟩

theorem completed_partial_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[PartialForestNoOverflow adversary q |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_partial_le_other adversary q hq)

variable {P : Type} [Fintype P] [SampleableType P]
theorem completed_partial_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128)+BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans ((probEvent_or_le _ _ _).trans (add_le_add
    (completed_near_bound S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
    (completed_pair_bound adversary q hq)))
  intro z hz h
  exact h.1.elim (fun hn=>Or.inl ⟨hn,h.2⟩) (fun hp=>Or.inr ⟨hp,h.2⟩)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Nonstructural (s : RefSample) : Prop := EncodingMatch s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_union_cases_of_split (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hsplit : ∀ z, z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
    Pr[fun s=>combinedEvent.holds s.answers s.trace | PairedReference.referenceExperiment adversary q] +
    Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z=>
      (QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z) ∨
      FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
      PartialForestNoOverflow adversary q z ∨
      IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 ∨
      (QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Ref.pmf_probEvent_mono
    intro z hz hclean
    rcases Classical.em (WPair.Paired.NoOverflow adversary z) with hno | hno
    · rcases hsplit z hz hclean with hab | hf
      · exact Or.inl ⟨hclean,hab⟩
      · rcases completed_forest_cases adversary q hq z hz hclean hf with hfull | hnear | hpair | hinc
        · exact Or.inr (Or.inl hfull)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hnear,hno⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr hpair,hno⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hinc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add (caseABEv_le_reference combinedEvent adversary q hq) (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem queryRatio_lt_one (q : Nat) (hq : q<2^128) : (q:ENNReal)/2^128<1 := by
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)),one_mul]
  exact_mod_cast hq

theorem denominator_ne_zero (q : Nat) (hq : q<2^128) : 1-(q:ENNReal)/2^128≠0 :=
  ne_of_gt (tsub_pos_iff_lt.mpr (queryRatio_lt_one q hq))

theorem prefixCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    prefixCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold prefixCoeff
  finiteness

theorem encodingCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) :
    encodingCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff
  finiteness

theorem errCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    errCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold errCoeff twoEdgeRate
  finiteness

theorem denominator_toReal (q : Nat) (hq : q<2^128) :
    (1-(q:ENNReal)/2^128).toReal=1-(q:ℝ)/2^128 := by
  rw [ENNReal.toReal_sub_of_le (le_of_lt (queryRatio_lt_one q hq)) (by simp)]
  simp

theorem prefixCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (prefixCoeff q w v).toReal=canonicalPrefix ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold prefixCoeff canonicalPrefix
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq,hvw]
  ring

theorem encodingCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) :
    (encodingCoeff q w v).toReal=canonicalEncoding ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff canonicalEncoding
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq]
  ring

theorem errCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (errCoeff q w v).toReal=canonicalError ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold errCoeff twoEdgeRate canonicalError
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,denominator_toReal q hq,hvw]
  ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

theorem query_card_lt_one (q : Nat) (hq : q<2^128) : (Fintype.card Digest:ℝ)⁻¹*q<1 := by
  have hcard : (Fintype.card Digest:ℝ)=2^128 := by rw [Fintype.card_bitVec];norm_num
  rw [hcard]
  have hq' : (q:ℝ)<2^128 := by exact_mod_cast hq
  rw [mul_comm,←div_eq_mul_inv]
  exact (div_lt_one (by positivity)).2 hq'

theorem kconst_le (q : Nat) : (ClaudeWCT.Arith.SideChannel.kconst q:ℝ)≤5*(q:ℝ)^2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q:ℝ)]

theorem errConst_nonneg (q : Nat) (hq : q<2^128) : 0≤Core.errConst q := by
  have hd : 0<1-(Fintype.card Digest:ℝ)⁻¹*q := sub_pos.mpr (query_card_lt_one q hq)
  unfold Core.errConst
  positivity

/-- With the one-sided side-channel constant (`kconst q = q²`, r3-lean-seedfam) the seed error is `2·54 = 108`
instead of `540` (`10·54`): the per-test charge `C` enters as `2 C y³ / (1 - y)`. -/
theorem kconst_le_sq (q : Nat) : (ClaudeWCT.Arith.SideChannel.kconst q:ℝ)≤(q:ℝ)^2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q:ℝ)]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open PairedReference.Classes
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q encodingCount
noncomputable def otherMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q PairedReference.otherCount
noncomputable def digestMass (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) : ENNReal :=
  PairedSeccLaw.expectedCharge adversary q hq PairedReference.Classes.digestClass

theorem masses_finite (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    prefixMass adversary q≠⊤ ∧ encodingMass adversary q≠⊤ ∧ otherMass adversary q≠⊤ ∧
      digestMass adversary q hq≠⊤ := by
  have hf := ne_top_of_le_ne_top (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq≠⊤ at hf
  rcases ENNReal.add_ne_top.mp hf with ⟨hpeo,hm⟩
  rcases ENNReal.add_ne_top.mp hpeo with ⟨hpe,ho⟩
  exact ⟨(ENNReal.add_ne_top.mp hpe).1,(ENNReal.add_ne_top.mp hpe).2,ho,hm⟩

theorem masses_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    (prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
      (otherMass adversary q).toReal/2^128+(digestMass adversary q hq).toReal/2^128≤(q:ℝ)/2^128 := by
  have hf:=masses_finite adversary q hq
  have h:=ENNReal.toReal_mono (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change (prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq).toReal≤(q:ENNReal).toReal at h
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩,hf.2.2.1⟩) hf.2.2.2,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩) hf.2.2.1,ENNReal.toReal_add hf.1 hf.2.1,ENNReal.toReal_natCast] at h
  simpa only [add_div] using div_le_div_of_nonneg_right h (show (0:ℝ)≤2^128 by positivity)

theorem full_probability_real (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤)
    (hmin:1/1024≤theta) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate) :
    (Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
        theta.toReal*((digestMass adversary q hq).toReal/2^128)+(q:ℝ)/2^128*rate.toReal := by
  have h := completed_flexible_full_bound (theta-1/1024) rate adversary q hq hrate
  rw [tsub_add_cancel_of_le hmin] at h
  have hcls : (fun (_ : PairedOuter.PaddedGame.TraceResult × SigGolfCandidate.T3.Correctness.Answers) =>
      CreationGame.publicClass CaseC.IsDigestInput)=PairedReference.Classes.digestClass := by
    funext z input
    apply propext
    rcases input with (coin | x) | priv
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
    · constructor
      · rintro ⟨rho,m,ctr,rfl⟩;exact ⟨rho,m,ctr,rfl⟩
      · rintro ⟨rho,m,ctr,h⟩;cases h;exact ⟨rho,m,ctr,rfl⟩
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
  rw [hcls] at h
  change _≤theta/2^128*digestMass adversary q hq+(q:ENNReal)*rate/2^128 at h
  have hm: digestMass adversary q hq≠⊤ := (masses_finite adversary q hq).2.2.2
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at hreal
  convert hreal using 1 <;> ring

theorem partial_probability_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      ((378+1/1024)/(2*(1-(q:ℝ)/2^128))+1/(2*(1-(q:ℝ)/2^128)^2))*((q:ℝ)/2^128)^2 := by
  have hqN : q<2^128 := by omega
  have hN : (0:ℝ)<2^128 := by positivity
  have hqr : (q:ℝ)<2^128 := by exact_mod_cast hqN
  have hd : 0<(2:ℝ)^128-q := sub_pos.mpr hqr
  have hsub : ((2^128-q:Nat):ℝ)=(2:ℝ)^128-q := by rw [Nat.cast_sub (by omega),Nat.cast_pow,Nat.cast_ofNat]
  have hsub0 : ((2^128-q:Nat):ENNReal)≠0 := by exact_mod_cast (by omega : 2^128-q≠0)
  have hchoose : (q.choose 2:ℝ)≤(q:ℝ)^2/2 := by
    have hc : q.choose 2*2≤q*q := by
      rw [Nat.choose_two_right]
      exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left q (Nat.sub_le q 1))
    have hc' : (q.choose 2:ℝ)*2≤(q:ℝ)*q := by exact_mod_cast hc
    nlinarith
  have hprod : ((q*(q-1):Nat):ℝ)≤(q:ℝ)^2 := by
    have hp : q*(q-1)≤q*q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
    simpa only [pow_two] using (show ((q*(q-1):Nat):ℝ)≤(q:ℝ)*q by exact_mod_cast hp)
  have hr := ENNReal.toReal_mono (by unfold BPair.pairTerm;finiteness) h
  simp (disch:=finiteness) only [BPair.pairTerm,ENNReal.toReal_add,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,ENNReal.toReal_one] at hr
  rw [hsub] at hr
  refine hr.trans ?_
  calc
    _ ≤ ((2:ℝ)^128-q)⁻¹*(q:ℝ)^2*(378+1/1024)/(2*2^128)+
      ((q:ℝ)^2/2)*(((2:ℝ)^128-q)⁻¹)^2 := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hd.le)) (by norm_num)
      · exact mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
    _ = _ := by
      have hdy : 1-(q:ℝ)/2^128≠0 := ne_of_gt (sub_pos.mpr ((div_lt_one hN).2 hqr))
      field_simp [ne_of_gt hd,hdy]
      <;> ring

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_of (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139)
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(710/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  have habs : (1:ℝ)/2^139+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_outer_ennreal (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_active_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WCT9.wordDigit (forestRank output k.val) t) :
    (.inl (.inr (Extract.Paired.honestInput answers (.wctChain (WCT9.digestIndex output) k.val
      (rawChildFromOutput output k).val t.val p.val))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  have h := checker_slot_queries answers pk log forgery message w output hw hd hcheck ho k t p hp
  rw [WPair.Paired.honestProbe_slot] at h
  exact h
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsHitIn_false (A : Answers) (K : LargeResidual.Coord → Prop) (qs : List Spec.Domain)
    (h : Extract.Paired.FtsHitIn A qs) (hclear : AllClear A K qs) : False := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := h
  -- #866: `SameHeader` is `length ∧ hdrKey`; `posOf_sameHeader` is its paired `posOf_key_eq`.
  have hp : Extract.posOf x = some p := Extract.Paired.posOf_sameHeader A p hb.legacy x hs
  apply paired_hit_false A K qs p x hq hp hb _ hh hclear
  cases p with
  | chain | leaf | node | forest => exact hfts.elim
  | wctChain | wctLeaf | wctNode => exact hb.legacy

theorem checker_bankFresh (A : Answers) (published : SigGolfCandidate.T3.Cache) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (hgen : evalWithAnswerFn A keygen = (pk,published))
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn A (PairedOuter.FullGame.authenticatedSign published entry.1))
    (hcheck : evalWithAnswerFn A (Final.Paired.checkForgeryP pk log forgery) = true)
    (hcomplete : ∀ m, ∃ sig, evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.signPayload published m) = some sig)
    (hsource : ∀ L, WotsExtract.SourceLeaf7 L →
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L ≠ none)
    (hclear : AllClear A (LargeResidual.Paired.Known (Disclosed A published))
      (queried A (Final.Paired.checkForgeryP pk log forgery))) :
    BankFresh A published log (queried A (Final.Paired.checkForgeryP pk log forgery)) := by
  have hpk : pk = Extract.honestRoot A 0 0 := by
    have h := Extract.keygen_pk A
    change (evalWithAnswerFn A keygen).1 = Extract.honestRoot A 0 0 at h
    rw [hgen] at h
    exact h
  have hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop A) := by
    have h := (Correctness.keygen_correct A).2.1
    rw [hgen] at h
    exact h
  rcases CanonicalExtract.checkForgery_canonical_or_collision A published hcache pk hpk log hlog forgery hcheck
    with hprim | hhit | ⟨m,w,N,hw,hdc,hd,hdq,hgate,hrank,hgood,hopen,hfresh⟩
  · exact (wotsPrimitive_false A published _ hsource hprim hclear).elim
  · exact (ftsHitIn_false A _ _ hhit hclear).elim
  refine ⟨m,wrho w,wdc w,N,?_,hdq,?_,?_,?_⟩
  · exact hd
  · change ClaudeWCT.Bank.Paired.admissible N = true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨hgate,?_⟩
    simpa only [ranksAccepted,List.all_eq_true,List.mem_finRange,forall_true_left,decide_eq_true_eq] using hrank
  · intro k t s hs
    exact Wots.PairedSmallT.checker_active_queries A pk log forgery m w N hw hd hcheck hopen k t s hs
  · exact WPair.Paired.fresh_digest_not_signer_eval A published log hlog m (wrho w) (wdc w) hcomplete hfresh
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cert_of_clean (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z)
    (hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2)
    (hcontext : ContextGood z.2) : CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  apply cert_of_clean_of_checker adversary q hq z hz hwin hno
  intro published pk log forgery hgen hlog hcheck hclear
  apply checker_bankFresh z.2 published pk log forgery hgen hlog hcheck _ _ hclear
  · intro message
    obtain ⟨sig,hsig⟩ := hcomp message
    rw [hgen] at hsig
    refine ⟨sig,?_⟩
    unfold SigGolfCandidate.Research.SharedForest.sign at hsig
    rw [evalWithAnswerFn_bind] at hsig
    split_ifs at hsig with hm
    · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hsig
    · exact hsig
  · exact Wots.CanonicalRef.referenceSearch_complete z.2 hcontext
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_noOvR_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137 := by
  simpa only [one_div] using! FtsOverflow.Paired.cleanWin_logOverflow_le adversary q hq

theorem clean_le_contact_cert (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z=>CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137 := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun z=> ContactNO adversary q z ∨
        (CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) ∨
        ¬ContextGood z.2 ∨ ¬SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2 ∨
        (QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Wots.Ref.pmf_probEvent_mono
    intro z hz hclean
    by_cases hno : NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
    by_cases hcontext : ContextGood z.2
    swap
    · exact Or.inr (Or.inr (Or.inl hcontext))
    by_cases hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcomp)))
    by_cases hcontact : Contact adversary q z
    · exact Or.inl ⟨hcontact,hno⟩
    · exact Or.inr (Or.inl ⟨cert_of_clean adversary q hq z hz hclean hcontact hcomp hcontext,hno⟩)
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl
      (add_le_add (Wots.PairedSearchTable.completed_context_failure adversary q hq)
        (add_le_add (Wots.PairedSearchTable.completed_signer_failure adversary q hq)
          (clean_noOvR_failure adversary q hq))))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_clean_closing (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128)
    (hclean : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      ENNReal.ofReal (2*((q:ℝ)/2^128)-((q:ℝ)/2^128)^2)+
      (q:ENNReal)*ENNReal.ofReal ((993/1000)*((q:ℝ)/2^128))/2^128+
      ((2 ^ 142 : ENNReal)⁻¹+(2 ^ 142 : ENNReal)⁻¹)+
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply Wots.PairedSmallT.clean_outer_ennreal adversary q hq
  let y : ℝ := (q:ℝ)/2^128
  have hy : 0≤y := by dsimp [y];positivity
  have hhalf : y≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    dsimp [y]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hpoly : 0≤2*y-y^2 := by nlinarith
  have hrate : 0≤(993/1000:ℝ)*y := mul_nonneg (by norm_num) hy
  have hr := ENNReal.toReal_mono (by finiteness) hclean
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_inv] at hr
  -- top-nonce layer (r3-lean-nonsec): the large route carries 2·Pr[CapFail] ≤ 2·(2^142)⁻¹
  change _ ≤ ENNReal.toReal (ENNReal.ofReal (2*y-y^2))+
    (q:ℝ)*ENNReal.toReal (ENNReal.ofReal ((993/1000)*y))/2^128+(((2:ℝ)^142)⁻¹+((2:ℝ)^142)⁻¹)+
    1/2^139+1/2^138+1/2^137 at hr
  rw [ENNReal.toReal_ofReal hpoly,ENNReal.toReal_ofReal hrate] at hr
  have hmul : (q:ℝ)*((993/1000)*y)/2^128=y*((993/1000)*y) := by dsimp [y];ring
  rw [hmul] at hr
  have hc := ContinuousPricing.large_closing_real_cap777 y ((993/1000)*y) hlow le_rfl
  have he : ((2:ℝ)^142)⁻¹+((2:ℝ)^142)⁻¹+1/2^139+1/2^138+1/2^137≤1/2^131 := by norm_num
  have hp1 : 0≤y*((1:ℝ)/2^25) := mul_nonneg hy (by positivity)
  have hp2 : 0≤y*((1:ℝ)/2^50) := mul_nonneg hy (by positivity)
  change _+ (y/2^18+1/2^700+1/2^152+y/2^128)≤2*y
  linarith

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hhalf : (q:ℝ)/2^128≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hexc := ClaudeWCT.Bank.Paired.excess_large_certified ((q:ℝ)/2^128) hlow hhalf
  have hexc' : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-ENNReal.ofReal (Flexible.budgetRate q-1/1024))≤
      ENNReal.ofReal ((993/1000)*((q:ℝ)/2^128)) := by
    simpa only [Flexible.budgetRate,mul_div_assoc] using hexc
  apply large_clean_closing adversary q hq hlow
  exact (clean_le_contact_cert adversary q hq).trans
    (add_le_add (add_le_add (add_le_add
      (contact_cert_bound_of_excess adversary q hq _ hexc') le_rfl) le_rfl) le_rfl)
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_FinalG ====
section

/-! # The live small route parametrized by the seed-error bound (r3-lean-seedfam, family closing for `g ≤ 7`)

`SeedErrorBound`: on the small window `y = q/2^128 ≤ 3/2500`, `errTot ≤ (733/1000) y²`. It holds for every per-test
chain charge `C ≤ 305` once `errTot ≤ 2 C y³ / (1 - y)` (the one-sided side-channel constant, `kconst q = q²`):
`seedErrorBound_of_charge`. Today's leaf families (`C = 54`, `errTot_toReal_sharp`) satisfy it
(`seedErrorBound_current`); `g = 7` lower families (`C = 43·7 = 301`) need `errTot ≤ 602 y³/(1-y)` from the family
restart. Copies of the Paired small-route chain (`…G`) use the weighted error `799/1000` (`grouped_weighted_error`)
and the middle closing `grouped_middle_closing` (`767/1000 + 799/1000`); the large route is unchanged.
`t3_securityP_of_seedError` : `SeedErrorBound → SecurityP`, and `t3_securityP_kappa2` instantiates it today.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open ENNReal SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
/-- The seed-error hypothesis of the small route. -/
def SeedErrorBound : Prop :=
  ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 → (q : ℝ) / 2 ^ 128 ≤ 3 / 2500 →
    (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2

/-- Any per-test chain charge `C ≤ 305` with `errTot ≤ 2 C y³/(1-y)` gives the seed-error bound. -/
theorem seedErrorBound_of_charge (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 305)
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        2 * C * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  fun adversary q hq hy => (h adversary q hq).trans (grouped_seed_error C _ hC0 hC (by positivity) hy)

/-- `g = 7`: the family restart must deliver `errTot ≤ 602 y³/(1-y)`. -/
theorem seedErrorBound_g7
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        602 * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  seedErrorBound_of_charge 301 (by norm_num) (by norm_num) fun adversary q hq =>
    (h adversary q hq).trans (le_of_eq (by ring))
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_ofG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142))
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(778/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  -- top-nonce layer (r3-lean-nonsec): the primitive constant carries Pr[CapFail] ≤ 1/2^142
  have habs : (1:ℝ)/2^139+1/2^142+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith


end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : 1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh : (q:ℝ)/2^128≤3/2500)
    (rate : ℝ) (hrate : rate≤1153/1000000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (99847/50000)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hquad := paired_partial_denominatorRC _ _ hhigh (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := grouped_middle_closingRC ((q:ℝ)/2^128) rate hlow hhigh hrate
  linarith

theorem tiny_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive : 1≤q) (hhigh : (q:ℝ)/2^128≤1/2^28)
    (rate : ℝ) (hrate : rate≤18/5000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (249/125)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hsmall : (q:ℝ)/2^128≤3/2500 := hhigh.trans (by norm_num)
  have hlow : 1/(2:ℝ)^128≤(q:ℝ)/2^128 := div_le_div_of_nonneg_right (by exact_mod_cast hpositive) (by positivity)
  have hquad := paired_partial_denominatorRC _ _ hsmall (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := tiny_class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := tiny_closing_rows18 ((q:ℝ)/2^128) rate hlow hhigh hrate
  nlinarith [sq_nonneg ((q:ℝ)/2^128)]

theorem clean_outer_ennrealG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring




end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_partial_certifiedG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q := by
  apply completed_partial_bound ClaudeWCT.Bank.Paired.nearLawSpec
    ClaudeWCT.Bank.Paired.nearLawSpec_producer rfl ClaudeWCT.Bank.Paired.nearCovered_mono
    (fun X N h => by
      obtain ⟨k,t,h⟩:=h
      exact WPair.Paired.nearCovered_bank X N k t h)
    378 ClaudeWCT.Bank.Paired.nearLawSpec_mean adversary q hq

theorem excess_middle_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((99847:ENNReal)/50000-1/1024))≤1153/1000000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_middle_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

theorem excess_tiny_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((249:ENNReal)/125-1/1024))≤18/5000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_tiny_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from ClaudeWCT_WCT9_SeedFamG ====
section

/-!
# `g`-leaf lower seed families (opus-crumbs retune; g = 4..7 under study, 16 in the original plan), scheme side, additive

Every group of `g` consecutive leaves of a lower tree shares one GF(2^128) polynomial family of
`lowerFamCoefCount g = 5g + 3` coefficients. Coefficient `j` of family `f` has ordinal `(5g+3)·f + j` and is read with
the existing carry packing `packedSecret (lowerSeedPair lay tree)` (ordinal `k` is half `k % 2` of private pair
`k / 2`; the carry is threaded across families, so a family with an odd first ordinal starts with the high half left by
the previous one). The seed of chain `i` of leaf `L` is the family of `L / g` evaluated at
`groupedPoint g L i = (L % g)·43 + i + 1` (points `1 ..= 43 g`, `< 1024` for `g ≤ 23`, distinct within a family).

These definitions sit alongside `lowerCoefs` / `buildLeafPF` / `buildTreeP` (Core.lean); nothing existing is changed.
Installing them is the one-line switch `buildTreeP ↦ buildTreePG` in `signLayersBC` (see the porter notes).
-/

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness

/-- Point stride per leaf of a family (the lower chain count). -/
def lowerFamStride : Nat := 43
/-- Coefficients per lower family of `g` leaves: 5 revealed seeds per leaf, plus 3. -/
def lowerFamCoefCount (g : Nat) : Nat := 5 * g + 3
/-- The family of a lower leaf. -/
def lowerFamOf (g leaf : Nat) : Nat := leaf / g
/-- Ordinal of coefficient `j` of family `fam` (the packed-half index in `lowerSeedPair lay tree`). -/
def lowerFamCoefOrdinal (g fam j : Nat) : Nat := lowerFamCoefCount g * fam + j
/-- Evaluation point of chain `chain` of leaf `leaf` in its family. -/
def groupedPoint (g leaf chain : Nat) : Nat := leaf % g * lowerFamStride + chain + 1

/-- The `5g + 3` coefficients of family `fam` (carry threaded through `packedSecret`). -/
def lowerCoefsG (g : Nat) (lay : Layer) (tree fam : Nat) (carry : Digest) : M (List Digest × Digest) :=
  (List.range (lowerFamCoefCount g)).foldlM (fun (state : List Digest × Digest) j => do
    let (coef, carry) ← packedSecret (lowerSeedPair lay tree) (lowerFamCoefOrdinal g fam j) state.2
    pure (state.1 ++ [coef], carry)) ([], carry)

/-- The seed of chain `chain` of leaf `leaf` from its family's coefficients. -/
def lowerFamilySeedG (g : Nat) (coefs : List Digest) (leaf chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (groupedPoint g leaf chain)

/-- A lower leaf from its family's coefficients (no private query: the family is built once per `g` leaves). -/
def buildLeafPG (g : Nat) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (Digest × List Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chainW lay tree leaf i 0 digit (lowerFamilySeedG g coefs leaf i)
      let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← lowerLeafHash lay tree leaf state.1
  pure (root, state.2)

/-- Lower tree of layer `lay ≥ 1` with `g`-leaf families: the family is (re)built at every leaf `≡ 0 (mod g)`, the
coefficients are kept for the next `g - 1` leaves, and the packing carry is threaded across families. -/
def buildTreePG (g : Nat) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × List Digest × Digest) leaf => do
      let (coefs, carry) ← if leaf % g = 0 then
          lowerCoefsG g lay tree (lowerFamOf g leaf) state.2.2.2
        else pure (state.2.2.1, state.2.2.2)
      let (root, values) ← buildLeafPG g lay tree leaf (if leaf = selected then digits else []) coefs
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), coefs, carry)) ([], [], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)

/-- `signLayersBC` with `g`-leaf lower families (the only change: `buildTreePG g`). -/
def signLayersBCG (g : Nat) (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreePG g lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBCG g cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))

/-! ### Security-facing view (answers-level), alongside `famCoefN` / `wotsSeed` (Correctness.lean). -/

/-- Coefficient `j` of lower family `fam`: the packed half `(5g+3)·fam + j` of `lowerSeedPair lay tree`. -/
def lowerFamCoefNG (g : Nat) (answers : Answers) (lay : Layer) (tree fam j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerFamCoefOrdinal g fam j / 2)))
    (lowerFamCoefOrdinal g fam j)
/-- The lower WOTS seed of chain `i` of leaf `leaf` under `g`-leaf families. -/
def lowerSeedG (g : Nat) (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval
    (List.ofFn fun j : Fin (lowerFamCoefCount g) => lowerFamCoefNG g answers lay tree (lowerFamOf g leaf) j.val)
    (groupedPoint g leaf i)

/-! ### Arithmetic facts -/

theorem groupedPoint_pos (g leaf chain : Nat) : 1 ≤ groupedPoint g leaf chain := by
  unfold groupedPoint; omega

/-- Points stay at most `43 g`. -/
theorem groupedPoint_le {g : Nat} (hg : 0 < g) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain ≤ 43 * g := by
  have hm := Nat.mod_lt leaf hg
  unfold groupedPoint lowerFamStride at *
  have : leaf % g * 43 ≤ (g - 1) * 43 := Nat.mul_le_mul_right _ (by omega)
  have : (g - 1) * 43 + 43 = 43 * g := by
    rcases g with _ | g
    · omega
    · simp only [Nat.add_sub_cancel]; ring
  omega

/-- Points are below `1024` (the `gfMulPt` / `HornRun` domain `< 2^10`) for `g ≤ 23`. -/
theorem groupedPoint_lt_1024 {g : Nat} (hg : 0 < g) (hg23 : g ≤ 23) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain < 1024 :=
  lt_of_le_of_lt (groupedPoint_le hg leaf chain hc) (by omega)

/-- Points are distinct within a family: equal family and equal point give equal leaf and chain. -/
theorem groupedPoint_inj {g leaf leaf' chain chain' : Nat} (hg : 0 < g) (hc : chain < lowerFamStride)
    (hc' : chain' < lowerFamStride) (hf : lowerFamOf g leaf = lowerFamOf g leaf')
    (hp : groupedPoint g leaf chain = groupedPoint g leaf' chain') : leaf = leaf' ∧ chain = chain' := by
  unfold groupedPoint lowerFamOf lowerFamStride at *
  have h1 := Nat.div_add_mod leaf g
  have h2 := Nat.div_add_mod leaf' g
  have hm := Nat.mod_lt leaf hg
  have hm' := Nat.mod_lt leaf' hg
  have hmod : leaf % g = leaf' % g := by omega
  refine ⟨?_, by omega⟩
  rw [← h1, ← h2, hf, hmod]

/-- Coefficient ordinals are distinct across families. -/
theorem lowerFamCoefOrdinal_inj {g f f' j j' : Nat} (hj : j < lowerFamCoefCount g) (hj' : j' < lowerFamCoefCount g)
    (h : lowerFamCoefOrdinal g f j = lowerFamCoefOrdinal g f' j') : f = f' ∧ j = j' := by
  unfold lowerFamCoefOrdinal at h
  rcases Nat.lt_or_ge f f' with hlt | hge
  · exfalso
    have : lowerFamCoefCount g * f + lowerFamCoefCount g ≤ lowerFamCoefCount g * f' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge f' f with hlt' | hge'
    · exfalso
      have : lowerFamCoefCount g * f' + lowerFamCoefCount g ≤ lowerFamCoefCount g * f := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hff : f = f' := by omega
      subst hff
      exact ⟨rfl, by omega⟩

/-- A family's chain slots `(leaf in family, chain)` revealing at most 5 per leaf reveal at most `5g`, so `|S| + 3`
fits the `5g + 3` coefficients. -/
theorem lowerFam_revealed_card_le {g : Nat} (S : Finset (Fin g × Fin 43))
    (h : ∀ l : Fin g, (S.filter fun p => p.1 = l).card ≤ 5) : S.card + 3 ≤ lowerFamCoefCount g := by
  have hs : S.card = ∑ l : Fin g, (S.filter fun p => p.1 = l).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  have hle : ∑ l : Fin g, (S.filter fun p => p.1 = l).card ≤ ∑ _l : Fin g, 5 := Finset.sum_le_sum fun l _ => h l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  unfold lowerFamCoefCount
  omega

/-- Private-pair queries of one lower tree with `g · nf` leaves: the even ordinals below `(5g+3)·nf`, i.e.
`⌈(5g+3)·nf / 2⌉`. For `g = 4`: L1 (32 families) 368 (was 512), L2/L3 (16) 184 (was 256). -/
theorem lowerFam_pairs_g4 : (23 * 32 + 1) / 2 = 368 ∧ (23 * 16 + 1) / 2 = 184 := by decide

end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamProg ====
section

/-! # Family decomposition of the rest tables, any layer and group size (r3-lean-seedfam, port step R1)

The family analogue of the leaf decomposition (`Normalized.RawLeaf.ovL` / `rdL` / `restLaw_resampleL`). A family of
shape `(g, w, n)` — `g` leaves of `w` chains, `n` coefficients — at `F = (lay, tree, fam)` covers the leaves `g·fam + l`
(`l < g`); its data are the `n` coefficient halves (ordinals `n·fam + j` of `lowerSeedPair lay tree`) and the used halves
of the step-0 rows of its `g w` chains (`GChainW g w = Fin g × Fin w`). `ovF F R (K, f)` overrides them, `rdF` reads
them back, and the rest-table law is invariant under resampling them (`restLaw_resampleF`).
Instances: lower 7-leaf families `(7, 43, 38)` (`5·7 + 3`), top 4-leaf families `(4, 54, 4 r + 3)` (`r` reveals per top
leaf); `(1, 43, 8)` and `(1, 54, 24)` are today's leaf families.

Hypothesis `FamOk g w b n F`: `0 < g`, `w < 2^24`, the leaves of `F` below `2^24`, its tree below `2^40`, its ordinals' pair
indices below `2^32` (header injectivity).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

/-- A lower seed family: layer, tree and family index (`leaf / g`). -/
structure FamAddr where
  lay : Layer
  tree : Nat
  fam : Nat
  deriving DecidableEq

/-- Leaf `l` of family `F`. -/
def famLeaf (g : Nat) (F : FamAddr) (l : Fin g) : LeafAddr := ⟨F.lay, F.tree, g * F.fam + l.val⟩
/-- Chain `c = (l, i)` of family `F`. -/
def chainOfF (g w : Nat) (F : FamAddr) (c : GChainW g w) : ChainAddr := ⟨famLeaf g F c.1, c.2.val⟩

/-- Admissible family: `n ≤ b` coefficients at ordinals `b·fam + j`. -/
structure FamOk (g w b n : Nat) (F : FamAddr) : Prop where
  pos : 0 < g
  width : w < 2 ^ 24
  leaf : g * F.fam + g ≤ 2 ^ 24
  tree : F.tree < 2 ^ 40
  pair : b * F.fam + b ≤ 2 ^ 33
  size : n ≤ b

/-- Ordinal of coefficient `j` of family `F` (ordinal base `b` per family). -/
def ordF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : Nat := b * F.fam + j
/-- Tweak of the cell holding coefficient `j` of `F`. -/
def cellHdrF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : BitVec 128 :=
  WCT9.lowerSeedHeader F.lay F.tree (ordF b F j / 2)

/-- Lower `g`-leaf families use the scheme's ordinals `WCT9.lowerFamCoefOrdinal`. -/
theorem ordF_lower (g : Nat) (F : FamAddr) (j : Fin (WCT9.lowerFamCoefCount g)) :
    ordF (WCT9.lowerFamCoefCount g) F j = WCT9.lowerFamCoefOrdinal g F.fam j := rfl

variable {g w b n : Nat} {F : FamAddr}

theorem ordF_pair_lt (hF : FamOk g w b n F) (j : Fin n) : ordF b F j / 2 < 2 ^ 32 := by
  have h1 := j.isLt
  have h2 := hF.pair
  have h3 := hF.size
  unfold ordF
  omega

theorem cellHdrF_inj (hF : FamOk g w b n F) {j j' : Fin n} (h : cellHdrF b F j = cellHdrF b F j') :
    ordF b F j / 2 = ordF b F j' / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j), Nat.mod_eq_of_lt (ordF_pair_lt hF j')] at this

theorem ordF_inj {j j' : Fin n} (h1 : ordF b F j / 2 = ordF b F j' / 2)
    (h2 : ordF b F j % 2 = ordF b F j' % 2) : j = j' := by
  apply Fin.ext; unfold ordF at h1 h2; omega

/-- The coefficient of `F` stored in half `bit` of the cell with tweak `tw`, if any. -/
noncomputable def slotAtF (b n : Nat) (F : FamAddr) (tw : BitVec 128) (bit : Nat) : Option (Fin n) :=
  if h : ∃ j : Fin n, cellHdrF b F j = tw ∧ ordF b F j % 2 = bit then some (Classical.choose h)
  else none

theorem slotAtF_some {tw : BitVec 128} {bit : Nat} {j : Fin n} (h : slotAtF b n F tw bit = some j) :
    cellHdrF b F j = tw ∧ ordF b F j % 2 = bit := by
  unfold slotAtF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem slotAtF_self (hF : FamOk g w b n F) (j : Fin n) :
    slotAtF b n F (cellHdrF b F j) (ordF b F j % 2) = some j := by
  have hex : ∃ j' : Fin n, cellHdrF b F j' = cellHdrF b F j ∧ ordF b F j' % 2 = ordF b F j % 2 :=
    ⟨j, rfl, rfl⟩
  unfold slotAtF
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordF_inj (cellHdrF_inj hF h1) h2]

/-- `priv` with `F`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivF (b n : Nat) (F : FamAddr) (priv : FullGame.FullTable) (K : Fin n → Digest) :
    FullGame.FullTable
  | .inl tw => ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw))))
  | .inr x => priv (.inr x)

theorem ovPrivF_inl (priv : FullGame.FullTable) (K : Fin n → Digest) (tw : BitVec 128) :
    ovPrivF b n F priv K (.inl tw) = ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))) := rfl

theorem ovPrivF_cell (hF : FamOk g w b n F) (priv : FullGame.FullTable) (K : Fin n → Digest)
    (j : Fin n) : halfOf (ordF b F j % 2) (ovPrivF b n F priv K (.inl (cellHdrF b F j))) = K j := by
  rw [ovPrivF_inl]
  unfold halfOf
  by_cases h0 : ordF b F j % 2 = 0
  · rw [if_pos h0]
    have hs := slotAtF_self hF j
    rw [h0] at hs
    rw [hs, low, ChainGraph.joinOutput_low]
    rfl
  · rw [if_neg h0]
    have hs := slotAtF_self hF j
    rw [show ordF b F j % 2 = 1 by omega] at hs
    rw [hs, high, ChainGraph.joinOutput_high]
    rfl

/-! ### Step-0 rows of the family's chains -/

theorem famLeaf_lt (hF : FamOk g w b n F) (l : Fin g) : (famLeaf g F l).leaf < 2 ^ 24 := by
  have := l.isLt; have := hF.leaf
  unfold famLeaf; simp only; omega

/-- Step-0 rows of distinct family chains are distinct. -/
theorem chainRowF_zero_inj (hF : FamOk g w b n F) {c c' : GChainW g w} {v v' : Digest}
    (h : chainRowW (chainOfF g w F c) 0 v = chainRowW (chainOfF g w F c') 0 v') : c = c' ∧ v = v' := by
  have hc := c.2.isLt; have hc' := c'.2.isLt
  have hw := hF.width
  obtain ⟨hal, hcc, -, hv⟩ := chainInputW_eq_chainRowW (a := chainOfF g w F c')
    (by unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) (by omega) (by omega) h
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF c'.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hcc
  simp only at hleaf hcc
  have e1 : c.1 = c'.1 := Fin.ext (by omega)
  exact ⟨Prod.ext e1 (Fin.ext hcc), hv⟩

/-- If `input` is the step-0 row of a chain of `F` at `v`, that `(c, v)`. -/
noncomputable def zeroOfF (g w : Nat) (F : FamAddr) (input : HashInput) : Option (GChainW g w × Digest) :=
  if h : ∃ p : GChainW g w × Digest, input = chainRowW (chainOfF g w F p.1) 0 p.2 then some (Classical.choose h) else none

theorem zeroOfF_some {input : HashInput} {p : GChainW g w × Digest} (h : zeroOfF g w F input = some p) :
    input = chainRowW (chainOfF g w F p.1) 0 p.2 := by
  unfold zeroOfF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem zeroOfF_chainRow (hF : FamOk g w b n F) (c : GChainW g w) (v : Digest) :
    zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) = some (c, v) := by
  cases h : zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) with
  | none =>
      unfold zeroOfF at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOfF_some h
      obtain ⟨h1, h2⟩ := chainRowF_zero_inj hF he
      rw [show p = (c, v) from Prod.ext h1.symm h2.symm]

/-- The used half of family chain `c`'s step-0 row. -/
def zhF (g w : Nat) (F : FamAddr) (c : GChainW g w) : Bool := zh (famLeaf g F c.1) c.2.val

/-! ### Override and readback in the normalized tables -/

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

/-- Family data: the `5g + 3` coefficients and the step-0 row functions of the `43 g` chains. -/
abbrev FamData (g w n : Nat) := (Fin n → Digest) × (GChainW g w → Digest → Digest)

/-- `pub` with the used halves of `F`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubF (g w : Nat) (F : FamAddr) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) :
    U → HashOutput := fun x =>
  match zeroOfF g w F x.val with
  | some p => joinHalf (zhF g w F p.1) (f p.1 p.2) (WCT9.halfOf (!zhF g w F p.1) (pub x))
  | none => pub x

noncomputable def ovF (g w b n : Nat) (F : FamAddr) (R : Tables U) (y : FamData g w n) : Tables U :=
  (ovPrivF b n F R.1 y.1, ovPubF g w F R.2 y.2)

noncomputable def rdF (g w b n : Nat) (F : FamAddr) (R : Tables U) : FamData g w n :=
  (fun j => halfOf (ordF b F j % 2) (R.1 (.inl (cellHdrF b F j))),
    fun c v => WCT9.halfOf (zhF g w F c) (R.2 ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩))

include hU in
theorem ovPubF_zero (hF : FamOk g w b n F) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) (c : GChainW g w)
    (v : Digest) :
    ovPubF g w F pub f ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩ =
      joinHalf (zhF g w F c) (f c v)
        (WCT9.halfOf (!zhF g w F c) (pub ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩)) := by
  unfold ovPubF
  simp only [zeroOfF_chainRow hF]

include hU in
theorem rdF_ovF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) : rdF hU g w b n F (ovF g w b n F R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdF ovF
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivF_cell hF R.1 K j
  · funext c v
    simp only
    rw [ovPubF_zero hU hF, halfOf_joinHalf]

include hU in
theorem ovF_ovF_rdF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) :
    ovF g w b n F (ovF g w b n F R y) (rdF hU g w b n F R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovF rdF
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivF b n F (ovPrivF b n F priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivF_inl, ovPrivF_inl]
      have e0 : ((slotAtF b n F tw 0).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (low (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAtF b n F tw 1).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (high (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubF
    cases hp : zeroOfF g w F x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW (chainOfF g w F p.1) 0 p.2, RawPrefix.chainRowW_mem hU _ _ _⟩ :=
          Subtype.ext (zeroOfF_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

include hU in
/-- **Resampling a family's coefficients and step-0 rows preserves the rest-table law.** -/
theorem restLaw_resampleF (hF : FamOk g w b n F) {β : Type} (Φ : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind Φ =
      (PMF.uniformOfFintype (Tables U)).bind
        (fun R => (PMF.uniformOfFintype (FamData g w n)).bind (fun y => Φ (ovF g w b n F R y))) := by
  have : Nonempty (FamData g w n) := ⟨(fun _ => 0, fun _ _ => 0)⟩
  have h := uniform_resample (Ω := Tables U) (X := fun _ => FamData g w n) (fun _ => 0)
    (fun _ R y => ovF g w b n F R y) (fun _ R => rdF hU g w b n F R) (fun R y => rdF_ovF hU hF R y)
    (fun R y => ovF_ovF_rdF hU hF R y) (fun _ _ => rfl)
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map]
  rfl

/-- After the override the coefficient cell half of `j` reads `K j`. -/
theorem raw_ovF_cell (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (j : Fin n) :
    halfOf (ordF b F j % 2) ((ovF g w b n F R y).1 (.inl (cellHdrF b F j))) = y.1 j :=
  ovPrivF_cell hF R.1 y.1 j

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCongr ====
section

/-! # Family restart, step P1/P3a: the abstract family scheme and family agreement (r3-lean-seedfam)

`FamScheme`: the scheme-side interface of the family restart. Per layer, `grp lay` consecutive leaves share one family
of `cnt lay` coefficients; coefficient `j` of family `f` is the packed half `cnt·f + j` of `lowerSeedPair lay tree`, and
the WOTS seed of chain `i` of leaf `leaf` is the family of `leaf / grp` evaluated at `(leaf % grp)·chainCount + i + 1`.
Today's scheme is the instance `leafScheme` (`grp = 1`, `cnt = famCount`); the switched scheme will be lower
`grp = 7, cnt = 38` and top `grp = 4, cnt = 4 r + 3`.

`FamOut S F`: queries outside family `F`'s chain rows (all `grp` leaves, steps `< 7`) and coefficient cells;
`FamAgree S F T T'`: agreement there and on the other halves of `F`'s cells; `wotsSeed_outF`: seeds of leaves outside
`F` are unchanged under `FamAgree`. (Family analogues of `Leaf.LeafOut` / `LeafAgree` / `wotsSeed_out`.)
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The scheme-side interface of the family restart. Per layer: `grp` leaves per family, ordinal base `cnt` (family `f`
owns ordinals `cnt·f + j`, `j < size lay f ≤ cnt`; the last family of a tree may be shorter), point stride `stride`
(`≥ chainCount`; lower 43, top 64). -/
structure FamScheme where
  grp : Layer → Nat
  cnt : Layer → Nat
  size : Layer → Nat → Nat
  stride : Layer → Nat
  /-- Evaluation point of chain `i` of leaf `leaf` (chains `≥ chainCount` may use a separate junk region). -/
  point : Layer → Nat → Nat → Nat
  grp_pos : ∀ lay, 0 < grp lay
  cnt_le : ∀ lay, cnt lay ≤ 512
  size_le : ∀ lay f, size lay f ≤ cnt lay
  point_eq : ∀ lay leaf i, i < chainCount lay → point lay leaf i = (leaf % grp lay) * stride lay + i + 1
  seed : ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- The scheme of the `Correctness` layout (`famGrp`, `famBase`, `famSize`, `famStride`, `famPoint`); valid for any
layout, so after the v6 flip it is the v6 scheme. -/
def layoutScheme : FamScheme where
  grp := WCT9.famGrp
  cnt := WCT9.famBase
  size := WCT9.famSize
  stride := WCT9.famStride
  point := WCT9.famPoint
  grp_pos := WCT9.famGrp_pos
  cnt_le lay := (WCT9.famBase_le lay).trans (by norm_num)
  size_le := WCT9.famSize_le_base
  point_eq lay leaf i hi := by unfold WCT9.famPoint; rw [if_pos (Or.inr hi)]
  seed T lay tree leaf i := by
    rw [WCT9.wotsSeed_fam]
    rfl

variable (S : FamScheme)

/-- Ordinal of coefficient `j` of family `F`. -/
def ordS (F : FamAddr) (j : Nat) : Nat := S.cnt F.lay * F.fam + j

/-- Queries outside family `F`: its chain rows (every leaf of the family, steps `< 7`) and its coefficient cells. -/
def FamOut (F : FamAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ l : Fin (S.grp F.lay), ∀ c step value, c < chainCount F.lay → step < 7 →
      input ≠ chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < S.cnt F.lay → tweak ≠ WCT9.lowerSeedHeader F.lay F.tree (ordS S F j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `FamOut F`. -/
def coverAddrsF (F : FamAddr) : List ChainAddr :=
  (List.finRange (S.grp F.lay)).flatMap (fun l =>
      (List.range (chainCount F.lay)).map (fun c => (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr))) ++
    (List.range (S.cnt F.lay)).map (fun j => (⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩ : ChainAddr))

theorem famOut_of_cover {F : FamAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, Untouched c q) :
    FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    have hmem : (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) ∈ coverAddrsF S F :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
        List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)
    have hu := h _ hmem step value (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (ordS S F j / 2) / 2 = ordS S F j / 2 by omega]
  · trivial

/-- A program respecting every chain's `Untouched` class respects `FamOut F`. -/
theorem respects_famOut {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (Leaf.respects_cover h (coverAddrsF S F)) fun _ hq => famOut_of_cover S hq

/-- `T'` agrees with `T` outside `F` and on the other halves of `F`'s coefficient cells. -/
structure FamAgree (F : FamAddr) (T T' : Answers) : Prop where
  out : ∀ q, FamOut S F q → T' q = T q
  half : ∀ o, (∃ j, j < S.cnt F.lay ∧ o / 2 = ordS S F j / 2) → (∀ j, j < S.cnt F.lay → o ≠ ordS S F j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o

/-- `(lay, tree, leaf)` is a leaf of family `F` up to the header aliasing of the tree index. -/
def FamAlias (F : FamAddr) (lay : Layer) (tree leaf : Nat) : Prop :=
  lay = F.lay ∧ tree % 2 ^ 40 = F.tree % 2 ^ 40 ∧ leaf / S.grp F.lay = F.fam

/-- Ordinal pair indices stay below `2^32` for leaves below `2^24` (`cnt ≤ 512`). -/
theorem ord_pair_lt (S : FamScheme) (lay : Layer) {leaf j : Nat} (hleaf : leaf < 2 ^ 24) (hj : j < S.cnt lay) :
    (S.cnt lay * (leaf / S.grp lay) + j) / 2 < 2 ^ 32 := by
  have h1 := S.cnt_le lay
  have h2 : leaf / S.grp lay ≤ leaf := Nat.div_le_self _ _
  have h3 : S.cnt lay * (leaf / S.grp lay) ≤ 512 * leaf :=
    (Nat.mul_le_mul_right _ h1).trans (Nat.mul_le_mul_left _ h2)
  omega

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
include hC

theorem eval_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    evalWithAnswerFn T' p = evalWithAnswerFn T p :=
  h.eval_eq hC.out

/-- **Seeds of leaves outside `F` are unchanged** (they read other cells, or the other halves of `F`'s cells). -/
theorem wotsSeed_outF (hF : F.fam * S.grp F.lay < 2 ^ 24) {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24)
    (hna : ¬FamAlias S F lay tree leaf) (i : Nat) :
    WCT9.wotsSeed T' lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  set o := S.cnt lay * (leaf / S.grp lay) + j.val with ho
  have hj : j.val < S.cnt lay := lt_of_lt_of_le j.isLt (S.size_le _ _)
  have ho2 : o / 2 < 2 ^ 32 := ord_pair_lt S lay hleaf hj
  by_cases hcell : ∃ j', j' < S.cnt F.lay ∧ WCT9.lowerSeedHeader lay tree (o / 2) =
      WCT9.lowerSeedHeader F.lay F.tree (ordS S F j' / 2)
  · obtain ⟨j', hj', he⟩ := hcell
    unfold WCT9.lowerSeedHeader at he
    obtain ⟨-, hl, ht, hp, -⟩ := header_fields he
    have hlay : lay = F.lay := Fin.ext (by
      rwa [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
        Nat.mod_eq_of_lt (lt_trans F.lay.isLt (by decide))] at hl)
    have hFl : F.fam < 2 ^ 24 := by
      have := S.grp_pos F.lay
      have : F.fam ≤ F.fam * S.grp F.lay := Nat.le_mul_of_pos_right _ this
      omega
    have hoF : ordS S F j' / 2 < 2 ^ 32 := by
      have h1 := S.cnt_le F.lay
      have : S.cnt F.lay * F.fam ≤ 512 * F.fam := Nat.mul_le_mul_right _ h1
      unfold ordS; omega
    rw [Nat.mod_eq_of_lt ho2, Nat.mod_eq_of_lt hoF] at hp
    have hpair : WCT9.lowerSeedPair lay tree (o / 2) = WCT9.lowerSeedPair F.lay F.tree (o / 2) := by
      unfold WCT9.lowerSeedPair privatePair
      rw [header_congr (by rw [hlay]) ht rfl]
    rw [hpair]
    subst hlay
    apply hC.half o ⟨j', hj', hp⟩
    intro j'' hj'' hoe
    apply hna
    refine ⟨rfl, ht, ?_⟩
    -- equal ordinals: same family
    unfold ordS at hoe
    rw [ho] at hoe
    rcases Nat.lt_trichotomy (leaf / S.grp F.lay) F.fam with hlt | heq | hgt
    · exfalso
      have : S.cnt F.lay * (leaf / S.grp F.lay) + S.cnt F.lay ≤ S.cnt F.lay * F.fam := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · exact heq
    · exfalso
      have : S.cnt F.lay * F.fam + S.cnt F.lay ≤ S.cnt F.lay * (leaf / S.grp F.lay) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hgt
      omega
  · have hq : T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) =
        T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) :=
      hC.out _ (fun j' hj' he => hcell ⟨j', hj', he⟩)
    unfold WCT9.lowerSeedPair privatePair privateHash
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change WCT9.seedHalf ((T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o =
      WCT9.seedHalf ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o
    rw [hq]
end Agree

end ClaudeWCT.W9.T3.Security.Wots.FamRestart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamProg2 ====
section

/-! # Family restart, step P2b: the family override against a `FamScheme` (r3-lean-seedfam)

Family analogues of `Normalized.RawLeaf.{raw_ovL_zero, raw_ovL_pub, raw_ovL_tweak, famCoef_ovL, wotsSeed_ovL,
leafAgree_ovL, search_ovL, referenceSearch_ovL, depth_ovL, restDepth_ovL}`: for a family `F` of a scheme `S`
(`g = S.grp F.lay` leaves of `chainCount F.lay` chains, `n = S.cnt F.lay` coefficients), the override
`ovF g w b n F R (K, f)` makes the family read `K` (seeds `familyEval K` at `l·w + c + 1`), agrees with `R` outside the
family (`famAgree_ovF`), and leaves every reference depth unchanged.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable {g w b n : Nat} {F : FamAddr}

include hU in
theorem raw_ovF_zero (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (c : GChainW g w) (v : Digest) :
    raw (ovF g w b n F R y) (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))) =
      joinHalf (zhF g w F c) (y.2 c v) (WCT9.halfOf (!zhF g w F c) (raw R (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _)]
  exact ovPubF_zero hU hF R.2 y.2 c v

theorem raw_ovF_pub (R : Tables U) (y : FamData g w n) (input : HashInput) (h : zeroOfF g w F input = none) :
    raw (ovF g w b n F R y) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [RawPrefix.raw_mem _ _ hm, RawPrefix.raw_mem _ _ hm]
    show ovPubF g w F R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubF
    simp only [h]
  · rw [RawPrefix.raw_nonmem _ _ hm, RawPrefix.raw_nonmem _ _ hm]

theorem slotAtF_none {tw : BitVec 128} {bit : Nat} (h : ∀ j : Fin n, cellHdrF b F j = tw → ordF b F j % 2 ≠ bit) :
    slotAtF b n F tw bit = none := by
  unfold slotAtF
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

theorem raw_ovF_tweak (R : Tables U) (y : FamData g w n) (tw : BitVec 128) (h : ∀ j : Fin n, cellHdrF b F j ≠ tw) :
    raw (ovF g w b n F R y) (.inr (.inl tw)) = raw R (.inr (.inl tw)) := by
  rw [RawPrefix.raw_private, RawPrefix.raw_private]
  show ovPrivF b n F R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivF_inl, slotAtF_none (fun j hj => absurd hj (h j)), slotAtF_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _

/-- The family coefficient `j` read through the scheme's packed half after the override is `K j`. -/
theorem famCoef_ovF (hF : FamOk g w b n F) (R : Tables U) (K : Fin n → Digest) (f : GChainW g w → Digest → Digest)
    (j : Fin n) :
    WCT9.seedHalf (evalWithAnswerFn (raw (ovF g w b n F R (K, f))) (WCT9.lowerSeedPair F.lay F.tree (ordF b F j / 2)))
      (ordF b F j) = K j := by
  rw [eval_lowerSeedPair]
  have hc := ovPrivF_cell hF R.1 K j
  rw [show ovPrivF b n F R.1 K (.inl (cellHdrF b F j)) = raw (ovF g w b n F R (K, f)) (.inr (.inl (cellHdrF b F j))) from rfl]
    at hc
  unfold halfOf at hc
  unfold WCT9.seedHalf
  unfold cellHdrF at hc
  split_ifs with h1 h2 h2
  · rw [if_pos h1] at hc; exact hc
  · rw [if_neg h1] at hc; exact hc

/-- A family cell with the header of pair index `o / 2` has ordinal pair `o / 2`. -/
theorem cellHdrF_eq_hdr (hF : FamOk g w b n F) (j' : Fin n) {o : Nat} (ho : o / 2 < 2 ^ 32)
    (h : cellHdrF b F j' = WCT9.lowerSeedHeader F.lay F.tree (o / 2)) : ordF b F j' / 2 = o / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j'), Nat.mod_eq_of_lt ho] at this

variable (S : FamScheme)

/-- Admissible family of a scheme. -/
abbrev FamOkS (F : FamAddr) : Prop := FamOk (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F

/-- **Seed readout after the override**: leaf `l` of `F`, chain `c`, reads `familyEval K` at `l·w + c + 1`. -/
theorem wotsSeed_ovF (hF : FamOkS S F) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f))) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [S.seed]
  have hg := S.grp_pos F.lay
  have hdiv : (S.grp F.lay * F.fam + l) / S.grp F.lay = F.fam := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt l.isLt, Nat.zero_add]
  have hmod : (S.grp F.lay * F.fam + l) % S.grp F.lay = l := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l.isLt]
  rw [S.point_eq _ _ _ hc, hdiv, hmod]
  congr 2
  funext j
  exact famCoef_ovF hF R K f j

/-- The family override changes nothing outside `F`'s own halves and step-0 rows. -/
theorem famAgree_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    FamAgree S F (raw R) (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) := by
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | (tw | x)
    · rfl
    · apply raw_ovF_pub
      cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
      | none => rfl
      | some p => exact absurd (zeroOfF_some hz) (hq p.1.1 p.1.2 0 p.2 p.1.2.isLt (by omega))
    · exact raw_ovF_tweak R y tw (fun j he => hq j (lt_of_lt_of_le j.isLt (S.size_le _ _)) he.symm)
    · rfl
  · obtain ⟨j, hj, hoj⟩ := ho
    rw [eval_lowerSeedPair, eval_lowerSeedPair]
    have ho2 : o / 2 < 2 ^ 32 := by
      rw [hoj]; have := hF.pair; unfold ordS; omega
    have hnone : slotAtF (S.cnt F.lay) (S.size F.lay F.fam) F (WCT9.lowerSeedHeader F.lay F.tree (o / 2)) (o % 2) = none := by
      apply slotAtF_none
      intro j' h1 h2
      have e1 := cellHdrF_eq_hdr hF j' ho2 h1
      apply hno j' (lt_of_lt_of_le j'.isLt (S.size_le _ _))
      unfold ordF at e1 h2
      unfold ordS at hoj ⊢
      omega
    rw [RawPrefix.raw_private, RawPrefix.raw_private]
    show WCT9.seedHalf ((ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 0 128,
      (ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 128 128) o = _
    rw [ovPrivF_inl]
    unfold WCT9.seedHalf
    split_ifs with h0
    · rw [h0] at hnone
      rw [hnone, ChainGraph.joinOutput_low]
      rfl
    · rw [show o % 2 = 1 by omega] at hnone
      rw [hnone, ChainGraph.joinOutput_high]
      rfl

theorem search_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K remaining =
      CanonicalRef.searchOf (raw R) zeroMessages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF (famAgree_ovF S hF R y)
    (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (K : LeafAddr) :
    CanonicalRef.referenceSearch (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K =
      CanonicalRef.referenceSearch (raw R) zeroMessages K :=
  CanonicalRef.referenceSearch_congr (fun K remaining _ => search_ovF S hF R y K remaining) K

theorem depth_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (a : ChainAddr) :
    CanonicalRef.depth (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages a =
      CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ovF S hF]

theorem restDepth_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (a : ChainAddr) :
    RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) = RawPrefix.restDepth a R := by
  rw [RawPrefix.restDepth_eq, RawPrefix.restDepth_eq, depth_ovF S hF]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamFill ====
section

/-! # Family restart, step P2c: the prefix-game fill with a family overridden (r3-lean-seedfam)

Family analogues of the `Fill` section of `Normalized.RawLeaf` (WotsLeafProg): the chain `a = chainOfF F ca` of
family `F` is filled (`fillTable a (ovF … X) e`); the other step-0 rows of the family read `X.2`, private cells read the
override, every reference depth is unchanged, and the family seeds read `familyEval X.1`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf (fillTable raw_ov_const)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

/-- Seeds depend on the answers only through the private cells of their layer and tree (any `FamScheme`). -/
theorem wotsSeed_congr_cellsS (S : FamScheme) {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  rw [eval_lowerSeedPair, eval_lowerSeedPair, h]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

section Fill
variable (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hF haF hd1

theorem fill_pubF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (input : HashInput)
    (h : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), c ≠ ca → ∀ v,
      input ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inl (.inr input)) =
      match PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (raw R (.inl (.inr input))))
      | none => raw R (.inl (.inr input)) := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega), hdX]
  cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
  | some p =>
    simp only
    have hin := PrefixGame.rowOf_some hp
    obtain ⟨⟨step, hs⟩, v⟩ := p
    simp only at hin ⊢
    subst hin
    congr 1
    by_cases hz : step = 0
    · subst hz
      have hrow : chainRowW a 0 v = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F ca) 0 v := by rw [haF]
      have h0 : WCT9.chainHigh a.key.lay a.chain 0 = zhF (S.grp F.lay) (chainCount F.lay) F ca := by subst haF; rfl
      rw [h0, hrow, raw_ovF_zero hU hF]
      exact halfOf_not_joinHalf _ _ _
    · congr 1
      rw [raw_ovF_pub]
      cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F (chainRowW a step v) with
      | none => rfl
      | some q =>
          have he := zeroOfF_some hzo
          have hw := hF.width
          have hc1 := q.1.2.isLt
          obtain ⟨-, -, hs', -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F q.1)
            (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
            (by unfold chainOfF; simp only; omega)
            (by have := RawPrefix.restDepth_le a R; omega) (by omega) he
          exact absurd hs' hz
  | none =>
    simp only
    have hc := (PrefixGame.rowOf_none_iff a input).mp hp
    apply raw_ovF_pub
    cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
    | none => rfl
    | some q =>
        have he := zeroOfF_some hzo
        by_cases hqa : q.1 = ca
        · exfalso
          apply hc
          refine ⟨0, q.2, hd1, ?_⟩
          rw [he, hqa, haF]
        · exact absurd he (h q.1 hqa q.2)

theorem fill_privF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (coord : Coordinate) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inr coord) =
      raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

theorem fill_zeroF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest)
    (c : GChainW (S.grp F.lay) (chainCount F.lay)) (hca : c ≠ ca) (v : Digest) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e
        (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))) =
      joinHalf (zhF (S.grp F.lay) (chainCount F.lay) F c) (X.2 c v)
        (WCT9.halfOf (!zhF (S.grp F.lay) (chainCount F.lay) F c)
          (raw R (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))))) := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix, raw_ovF_zero hU hF]
  rw [PrefixGame.rowOf_none_iff]
  rintro ⟨step, value, hs, he⟩
  have hw := hF.width
  have hc1 := c.2.isLt
  obtain ⟨hal, hc, -, -⟩ := chainInputW_eq_chainRowW (a := a)
    (by unfold chainOfF; simp only; omega) (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
    (by omega) (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega) he
  apply hca
  subst haF
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF ca.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hc
  simp only at hleaf hc
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hc)

theorem famAgree_fill (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    FamAgree S F (raw R) (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) := by
  have hA := famAgree_ovF S hF R X
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | coord
    · rfl
    · rw [fill_pubF hU S hF ca haF R hd1 X e input (fun c _ v he => hq c.1 c.2 0 v c.2.isLt (by omega) he)]
      cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | none => rfl
      | some p =>
          exfalso
          have hin := PrefixGame.rowOf_some hp
          apply hq ca.1 ca.2 p.1 p.2 ca.2.isLt (by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega)
          rw [hin]; exact congrArg (fun b => chainRowW b p.1.val p.2) haF
    · rw [fill_privF hU S hF ca haF R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_privF hU S hF ca haF R hd1]
    exact this

theorem depth_fillF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (b : ChainAddr) :
    CanonicalRef.depth (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) zeroMessages b =
      CanonicalRef.depth (raw R) zeroMessages b := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.depth_ov _ (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega),
    depth_ovF S hF]

theorem wotsSeed_fillF (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (e : Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) e) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [← wotsSeed_ovF S hF R K f l c hc]
  apply wotsSeed_congr_cellsS S
  intro p
  exact fill_privF hU S hF ca haF R hd1 (K, f) e _

theorem fill_frontier_selfF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    CanonicalRef.frontierValue (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e)
      zeroMessages a = e := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.frontierValue_ov hU]
  obtain ⟨d', hd'⟩ : ∃ d', RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) = d' + 1 :=
    ⟨RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) - 1, by omega⟩
  generalize RawPrefix.ovSeed a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e = s0
  revert s0
  rw [hd']
  intro s0
  exact PrefixGame.evaluate_const_succ d' e s0
end Fill

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamGame ====
section

/-! # Family restart, step P3b: family congruence leaves the honest reference game unchanged (r3-lean-seedfam)

Port of the leaf route (`WotsLeafCongr` legacy helpers + normalized `CanonicalRef.Leaf.Congr`, and the game part of
`WotsLeafProg`: `referenceGame_leaf`) from one WOTS leaf to a family `F` of `grp` leaves sharing one seed polynomial,
against the abstract `FamScheme` interface.

* `FamRestart`: family `respects` lemmas (`respectsF_*`), `famOut_chainInput`, and the legacy-namespace helpers
  `eval_chain_outF`, `wotsEnd_outF`, `wotsRoot_outF`, `wotsTree_layF`, `honestForest_outF`, `leafMsg_layF`,
  `referenceSearch_layF`, `depth_layF`.
* `CanonicalRef.FamGame`: `FamCongr S messages F T T'` (`FamAgree` plus rows/front of every chain of every leaf of `F`),
  `wotsEnd/Value/Root/Tree_congrF`, `sourceMessages_congrF`, the signer/keygen invariance and
  **`referenceGame_fam`**.

Aliasing split: a leaf either `FamAlias`es `F` — then it is the family member `famLeaf F (leaf % grp)` up to the
`2^40` tree aliasing, and the one-leaf lemmas `Mask.chainW_alias` / `wotsSeed_alias` / `sourceLeaf_alias` apply to that
member — or not, and then `wotsSeed_outF` / `eval_chain_outF` apply.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

variable (S : FamScheme)

/-! ## Family members and aliasing -/

/-- Leaves of an admissible family are below `2^24`. -/
theorem famLeaf_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (l : Fin (S.grp F.lay)) :
    (famLeaf (S.grp F.lay) F l).leaf < 2 ^ 24 := by
  show S.grp F.lay * F.fam + l.val < 2 ^ 24
  have := l.isLt
  omega

theorem famBound_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    F.fam * S.grp F.lay < 2 ^ 24 := by
  have := S.grp_pos F.lay
  rw [Nat.mul_comm]
  omega

/-- A family-aliasing leaf is (up to tree aliasing) the member `leaf % grp` of the family. -/
theorem famAlias_member {F : FamAddr} {lay : Layer} {tree leaf : Nat} (h : FamAlias S F lay tree leaf) :
    ∃ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) ∧
      (famLeaf (S.grp F.lay) F l).leaf = leaf := by
  have hleq : (famLeaf (S.grp F.lay) F ⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩).leaf = leaf := by
    show S.grp F.lay * F.fam + leaf % S.grp F.lay = leaf
    rw [← h.2.2, Nat.div_add_mod]
  exact ⟨⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨h.1, h.2.1, by rw [hleq]⟩, hleq⟩

/-- A small leaf aliasing a member of the family family-aliases the family. -/
theorem famAlias_of_leafAlias {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer}
    {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : FamAlias S F lay tree leaf := by
  refine ⟨h.1, h.2.1, ?_⟩
  have h2 : leaf % 2 ^ 32 = (S.grp F.lay * F.fam + l.val) % 2 ^ 32 := h.2.2
  have hl := famLeaf_lt S hF l
  change S.grp F.lay * F.fam + l.val < 2 ^ 24 at hl
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  rw [h2, Nat.mul_add_div (S.grp_pos _), Nat.div_eq_of_lt l.isLt, Nat.add_zero]

theorem leafAlias_famLay {F : FamAddr} {lay : Layer} {tree leaf : Nat} {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : lay = F.lay := h.1

/-! ## Programs respecting `FamOut` -/

section Programs
variable (F : FamAddr)
theorem respectsF_signForest (index : Nat) (output : HashOutput) :
    Respects (FamOut S F) (ClaudeWCT.WCT9.signForest index output) :=
  respects_famOut S (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) F
theorem respectsF_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (FamOut S F) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_famOut S (fun c => respects_digest c _ _ _) F) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsF_privateMac (region : Region) : Respects (FamOut S F) (privateMac region) :=
  respects_famOut S (fun c => respects_privateMac c region) F
theorem respectsF_privateNonce (message : Message) : Respects (FamOut S F) (privateNonce message) :=
  respects_famOut S (fun c => respects_privateNonce c message) F
theorem respectsF_mask (level index : Nat) : Respects (FamOut S F) (mask level index) :=
  respects_famOut S (fun c => respects_mask c level index) F
theorem respectsF_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (FamOut S F) (buildLevels tag lay tree h leaves) :=
  respects_famOut S (fun c => respects_buildLevels c tag lay tree h leaves ht) F
theorem respectsF_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (FamOut S F) (leafHash lay tree leaf ends) :=
  respects_famOut S (fun c => respects_leafHash c lay tree leaf ends) F
theorem respectsF_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (FamOut S F) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  respects_famOut S (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) F
theorem famOut_ftsQuery {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    FamOut S F q :=
  famOut_of_cover S fun c _ => ClaudeWCT.WCT9.Wots.ftsQuery_untouched c h
/-- Chain rows outside `F` (a leaf not aliasing the family, or a chain index beyond the leaves' chains). -/
theorem famOut_chainInput (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer} {tree leaf i s : Nat}
    (v : Digest) (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24) (hs : s < 256)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) :
    FamOut S F (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro l c step value hc hstep heq
  rw [pad64_chainInputW] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le F.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ :=
    chainInputW_eq_chainRowW (a := ⟨famLeaf (S.grp F.lay) F l, c⟩) hi hc' hs (by omega) heq
  exact hna ⟨famAlias_of_leafAlias S hF hleaf hal, hc⟩
theorem respectsF_topPath (cache : Cache) (leaf : Nat) : Respects (FamOut S F) (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsF_mask S F _ _) fun _ => Respects.pure' _
theorem famOut_of_hdr (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = SphincsSecurity.bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    FamOut S F (.inl (.inr input)) := by
  intro l c step value _ hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value) =
      SphincsSecurity.bytesLE 16 (chainHeader (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
        (famLeaf (S.grp F.lay) F l).leaf c step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (SphincsSecurity.bytesLE_injective hblock).symm
theorem famOut_of_length (input : HashInput) (hl : input.length ≠ 64) : FamOut S F (.inl (.inr input)) := by
  intro l c step value _ _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem foldOK_famOut (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : Mask.FoldOK (FamOut S F) lay tree h := by
  intro level i left right hlev hi
  refine famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (Mask.lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsF_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.lowerLevels lay tree h leaves) :=
  Mask.respects_lowerLevels' (foldOK_famOut S F lay tree h h7) leaves hlen
/-! Top-nonce layer (r3-lean-nonsec): the img-v6 top tree leaves the family classes untouched. -/
theorem respectsF_topNodeHashN (heap n : Nat) (left right : Digest) :
    Respects (FamOut S F) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  rw [Mask.pad64_topNodeInput_block4]
  exact famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ _ right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs
theorem respectsF_topNonceSearch (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (FamOut S F) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respectsF_topNonceSearch h heap left right fuel (n + 1)
theorem respectsF_buildTopLevels (leaves : List Digest) : Respects (FamOut S F) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact Mask.respects_lowerNodeHash' _ _ _ _ _ (famOut_of_hdr S F _ _
      (SigGolfCandidate.T3M.Extract.hdrBlock_block4 _ _ 0 _)
      fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs)
  · unfold topNodeAt
    exact Respects.map _ (respectsF_topNonceSearch S F _ _ _ _ _ _)
theorem respectsF_buildLevelsBelowW (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  Mask.respects_buildLevelsBelow' (foldOK_famOut S F lay tree h h7) tag leaves hlen
theorem respectsF_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (FamOut S F) (WCT9.lowerLeafHash lay tree leaf ends) :=
  Mask.respects_lowerLeafHash' _ _ _ _ (famOut_of_length S F _ (Mask.pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end Programs

/-! ## Legacy-namespace helpers under `FamAgree` -/

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
  (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

theorem queried_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    SourceReplay.queried T' p = SourceReplay.queried T p :=
  h.queried_eq hC.out

include hF in
theorem eval_chain_outF {lay : Layer} {tree leaf i : Nat} (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) {start count : Nat} (hc : start + count ≤ 256)
    (v : Digest) :
    evalWithAnswerFn T' (WCT9.chainW lay tree leaf i start count v) =
      evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count v) := by
  apply eval_outF hC
  exact Mask.respects_chainW' _ _ _ _ _ _ _ fun step value _ hhi =>
    famOut_chainInput S F hF value hleaf hi (by omega) hna

include hF in
theorem wotsEnd_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf)
    (i : Nat) (hi : i < chainCount lay) : WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_outF hC (famBound_lt S hF) hleaf hna]
  exact eval_chain_outF hC hF hleaf (by have := chainCount_le lay; simp only [Nat.reducePow]; omega)
    (fun h => hna h.1) (by have := width_le lay i; omega) _

include hF in
theorem wotsRoot_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_outF hC hF hleaf hna i (List.mem_range.mp hi))]
  exact eval_outF hC (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_layF {lay : Layer} (hl : lay ≠ F.lay) (tree : Nat) :
    WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_outF hC hF
    (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega) (fun h => hl h.1))]
  split_ifs
  · exact eval_outF hC (respectsF_buildTopLevels S F _)
  · exact eval_outF hC (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))

theorem honestForest_outF (index : Nat) : Extract.honestTop T' index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hC.out _ (famOut_ftsQuery S F hq))

include hF in
/-- Messages of leaves on `F`'s layer come from the layer above (or the forest), which `F` does not touch. -/
theorem leafMsg_layF {K : LeafAddr} (hK : K.lay = F.lay) : leafMsg T' K = leafMsg T K := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_layF hC hF (fun he => by
      have := congrArg Fin.val he
      rw [← hK] at this
      simp only at this
      omega)]
  · rw [honestForest_outF hC]

include hF in
theorem referenceSearch_layF {K : LeafAddr} (hK : K.lay = F.lay) :
    referenceSearch T' K = referenceSearch T K := by
  unfold referenceSearch
  rw [leafMsg_layF hC hF hK]
  exact eval_outF hC (respectsF_layerCounterSearch S F _ _ _ _ _ _)

include hF in
theorem depth_layF {a : ChainAddr} (ha : a.key.lay = F.lay) : depth T' a = depth T a := by
  unfold depth referenceDigits
  rw [referenceSearch_layF hC hF ha]
end Agree

end ClaudeWCT.W9.T3.Security.Wots.FamRestart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
variable (S : FamScheme)

/-- Family congruence: `FamAgree`, plus agreement on the rows of every chain of every REAL leaf of `F` (index below
`2 ^ height F.lay`; the last family of a tree may have phantom members) from its signed digit on, and on every such
chain's frontier value. -/
structure FamCongr (messages : LeafAddr → WCT9.LayerMsg) (F : FamAddr) (T T' : Answers) : Prop
    extends FamAgree S F T T' where
  rows : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay → ∀ s v,
    CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v))) =
      T (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v)))
  front : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay →
    CanonicalRef.frontierValue T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.frontierValue T messages ⟨famLeaf (S.grp F.lay) F l, c⟩

variable {S} {messages : LeafAddr → WCT9.LayerMsg} {F : FamAddr} {T T' : Answers}

theorem searchOf_congrF (hC : FamAgree S F T T') (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf T' messages K remaining = CanonicalRef.searchOf T messages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF hC (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_congrF (hC : FamAgree S F T T') (K : LeafAddr) :
    CanonicalRef.referenceSearch T' messages K = CanonicalRef.referenceSearch T messages K :=
  CanonicalRef.referenceSearch_congr (fun K r _ => searchOf_congrF hC K r) K

theorem depth_congrF (hC : FamAgree S F T T') (a : ChainAddr) :
    CanonicalRef.depth T' messages a = CanonicalRef.depth T messages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_congrF hC]

section Chains
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

/-- A member's own chains: from the frontier on, the rows agree. -/
theorem eval_chainF {L : LeafAddr} (hL : ∃ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay ∧ famLeaf (S.grp F.lay) F l = L) {c count : Nat}
    (hc : c < chainCount L.lay) (hd : CanonicalRef.depth T messages ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨l, hr, rfl⟩ := hL
  obtain ⟨e, rfl⟩ : ∃ e, count = CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ + e :=
    ⟨count - CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩, by omega⟩
  have hd' : CanonicalRef.depth T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ :=
    depth_congrF hC.toFamAgree ⟨famLeaf (S.grp F.lay) F l, c⟩
  rw [eval_chainW_add', eval_chainW_add' T, Nat.zero_add]
  have hf := hC.front l hr c hc
  unfold CanonicalRef.frontierValue honestChainValueW at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW]
  exact hC.rows l hr c hc step value hlo (by omega)

include hF in
theorem wotsEnd_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (i : Nat) (hi : i < chainCount lay) :
    WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsEnd
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb,
      show maxDigit lay i = maxDigit L.lay i by rw [hal.1]]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' (CanonicalRef.depth_le T messages ⟨L, i⟩ hi')
      (by have := width_le L.lay i; omega)
  · exact wotsEnd_outF hC.toFamAgree hF hleaf hfa i hi

include hF in
theorem wotsValue_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (digits : List Nat) (i : Nat)
    (hi : i < chainCount lay) (hdig : digits.getD i 0 ≤ 256)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    WCT9.wotsValue T' lay tree leaf digits i = WCT9.wotsValue T lay tree leaf digits i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    have hdl := halias l hal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll hdl
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsValue
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' hdl hdig
  · unfold WCT9.wotsValue
    rw [wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hleaf hfa]
    exact eval_chain_outF hC.toFamAgree hF hleaf
      (by have := chainCount_le lay; simp only [Nat.reducePow]; omega) (fun h => hfa h.1) (by omega) _

include hF in
theorem wotsRoot_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_congrF hC hF hreal i (List.mem_range.mp hi))]
  exact eval_outF hC.toFamAgree (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_congrF (lay : Layer) (tree : Nat) : WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_congrF hC hF (List.mem_range.mp hleaf))]
  split_ifs
  · exact eval_outF hC.toFamAgree (respectsF_buildTopLevels S F _)
  · exact eval_outF hC.toFamAgree (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
end Chains

theorem famOut_of_coverP {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, UntouchedP c q) : FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    exact h ⟨famLeaf (S.grp F.lay) F l, c⟩ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
      List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    rw [heq]
    unfold seedTweakP seedSlot seedTweak WCT9.lowerOrdinal WCT9.lowerSeedHeader
    simp only
    split <;> simp [Nat.mul_div_cancel_left]
  · trivial

variable (S) in
theorem respects_famOutP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf.respects_coverP h (coverAddrsF S F))
    fun _ hq => famOut_of_coverP hq

theorem buildForest_outF (hC : FamAgree S F T T') (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    ExecEq T T' (buildForest index selected words) (buildForest index selected words) := by
  have h := respects_famOutP S (fun a => CanonicalRef.respectsP_buildForest a index selected words) F
  exact ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem forestCommitment_outF (hC : FamAgree S F T T') (index : Nat) :
    CanonicalRef.forestCommitment T' index = CanonicalRef.forestCommitment T index := by
  have h := congrArg Prod.snd (buildForest_outF hC index (forestSelectionFromOutput 0) (forestWordsFromOutput 0)).1
  simpa only [buildForest_commitment] using h

theorem sourceMessages_congrF (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    CanonicalRef.sourceMessages T' = CanonicalRef.sourceMessages T := by
  funext K
  unfold CanonicalRef.sourceMessages
  split
  · unfold Extract.honestPair
    rw [wotsTree_congrF hC hF]
  · rw [forestCommitment_outF hC.toFamAgree]
end Congr

section Game
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
variable {S : FamScheme} {messages : LeafAddr → LayerMsg} {F : FamAddr} {T T' : Answers}

section Pieces
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC hF

theorem eval_signTop_fam (cache : Cache) (leaf : Nat) (hleaf : leaf < 2 ^ height 0) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias 0 0 leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    evalWithAnswerFn T' (signTop cache leaf digits) = evalWithAnswerFn T (signTop cache leaf digits) := by
  have hv : (List.range (chainCount 0)).map (WCT9.wotsValue T' 0 0 leaf digits) =
      (List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits) := by
    apply List.map_congr_left
    intro i hi
    apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
    · have := hvalid i (List.mem_range.mp hi)
      have := width_le 0 i
      omega
    · intro l hal
      exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)
  rw [Mask.eval_signTop_wots T' cache leaf digits hvalid, Mask.eval_signTop_wots T cache leaf digits hvalid, hv,
    eval_outF hC.toFamAgree (respectsF_topPath S F _ _)]

theorem wotsPieces_congrF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ height lay)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    wotsPieces T' lay tree leaf digits = wotsPieces T lay tree leaf digits := by
  unfold wotsPieces
  rw [wotsTree_congrF hC hF]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
  · have := hvalid i (List.mem_range.mp hi); have := width_le lay i; omega
  · intro l hal
    exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)

theorem fixedPrepared_pieces_congrF (index : Nat) (hi : index < 2 ^ 31) (lay : Layer) (hlay : lay ≠ 0)
    {counter : BitVec 32} {digits : List Nat} {low : Bool}
    (hsearch : CanonicalRef.referenceSearch T messages (sourceLeaf index lay) = some (counter, digits, low))
    (htree : F.tree < 2 ^ 40) :
    preparedPieces lay (route index lay).1 (fixedPrepared T' index lay) digits =
      preparedPieces lay (route index lay).1 (fixedPrepared T index lay) digits := by
  have hv := CanonicalRef.Mask.source_digits_valid T messages lay hsearch rfl
  have hp (X : Answers) : preparedPieces lay (route index lay).1 (fixedPrepared X index lay) digits =
      wotsPieces X lay (route index lay).2 (route index lay).1 digits := by
    unfold fixedPrepared
    rw [← eval_buildTreePrefixes_result X hlay _ _ (route_leaf_bound index lay)]
    exact preparedPieces_result X hlay _ _ digits hv (route_leaf_bound index lay)
  rw [hp, hp]
  apply wotsPieces_congrF hC hF (route_leaf_bound index lay) digits hv
  intro l hal i _
  exact CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi hsearch htree
    (famLeaf_lt S hF l) hal
end Pieces

theorem searchPreparedLayers_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index < 2 ^ 31)
    (forest : PairRoot) (hforest : LayerMsg.pair forest.1 forest.2 = sourceMessages T (sourceLeaf index 3)) :
    let prepared := (⟨fixedPrepared T index 1, fixedPrepared T index 2, fixedPrepared T index 3⟩ : PreparedRoots)
    let prepared' := (⟨fixedPrepared T' index 1, fixedPrepared T' index 2, fixedPrepared T' index 3⟩ : PreparedRoots)
    ExecEq T T' (searchPreparedLayers cache index prepared forest)
      (searchPreparedLayers cache index prepared' forest) := by
  let messages := sourceMessages T
  have hlevels (lay : Layer) : (fixedPrepared T' index lay).levels = (fixedPrepared T index lay).levels := by
    dsimp only [fixedPrepared]
    rw [wotsTree_congrF hC hF]
  have hs (lay : Layer) (remaining : Nat)
      (_hc : referenceContext T messages (sourceLeaf index lay) = some remaining) :
      ExecEq T T' (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay))
        (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay)) :=
    let h := respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F
    ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩
  have h0 : LayerMsg.pair (topPair 1 (fixedPrepared T index 1).levels).1
      (topPair 1 (fixedPrepared T index 1).levels).2 = messages (sourceLeaf index 0) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 0 (by decide)]; rfl
  have h1 : LayerMsg.pair (topPair 2 (fixedPrepared T index 2).levels).1
      (topPair 2 (fixedPrepared T index 2).levels).2 = messages (sourceLeaf index 1) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 1 (by decide)]; rfl
  have h2 : LayerMsg.pair (topPair 3 (fixedPrepared T index 3).levels).1
      (topPair 3 (fixedPrepared T index 3).levels).2 = messages (sourceLeaf index 2) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 2 (by decide)]; rfl
  have h3 : LayerMsg.pair forest.1 forest.2 = messages (sourceLeaf index 3) := hforest
  have hc0 : referenceContext T messages (sourceLeaf index 0) = some WCT9.CanonicalPolicy.totalCredit := rfl
  dsimp only
  unfold searchPreparedLayers
  dsimp only
  rw [hlevels 1, hlevels 2, hlevels 3, h0, h1, h2, h3]
  refine ExecEq.bind (hs 0 WCT9.CanonicalPolicy.totalCredit hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact ExecEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0, digits0, low0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1) =
        some (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0 digits0) := by
      apply context_parent_success (leaf := sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact ExecEq.pure' _ _ _
    · refine ExecEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact ExecEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1, digits1, low1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2) =
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
              digits0) 1 low1 digits1) := by
          apply context_parent_success (leaf := sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact ExecEq.pure' _ _ _
        · refine ExecEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact ExecEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2, digits2, low2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3) =
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
                    digits0) 1 low1 digits1) 2 low2 digits2) := by
              apply context_parent_success (leaf := sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact ExecEq.pure' _ _ _
            · refine ExecEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact ExecEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3, digits3, low3⟩
                have href3 := referenceSearch_of_run hc3 hr3
                have hv0 := CanonicalRef.Mask.source_digits_valid T messages 0 href0 rfl
                have ht : ExecEq T T' (signTop cache (route index 0).1 digits0)
                    (signTop cache (route index 0).1 digits0) := by
                  have hlt : (route index (0 : Layer)).1 < 2 ^ height (0 : Layer) := route_leaf_bound index (0 : Layer)
                  refine ⟨eval_signTop_fam hC hF cache _ hlt _ hv0 ?_, ?_⟩
                  · intro l hal i _
                    apply CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi href0
                      htree (famLeaf_lt S hF l)
                    rw [SigGolfCandidate.T3.route_top_tree index hi]
                    exact hal
                  · rw [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop,
                      SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop]
                refine ExecEq.bind ht ?_
                intro top _
                apply ExecEq.pure_eq
                rw [fixedPrepared_pieces_congrF hC hF index hi 1 (by decide) href1 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 2 (by decide) href2 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 3 (by decide) href3 htree]

theorem execEq_outF (hC : FamAgree S F T T') {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    ExecEq T T' p p :=
  ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem signFromOutput_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ExecEq T T' (signFromOutput cache rho counter output) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine ExecEq.bind (buildForest_outF hC.toFamAgree _ _ _) ?_
  intro forest hforest
  refine ExecEq.bind_effect (Mask.queried_length_prepareRoots_congr _ _ _) ?_
  simp only [prepareRoots_result]
  refine ExecEq.bind (searchPreparedLayers_famEq hC htree hF cache _ (digestIndex_lt output) forest.2 ?_) ?_
  · rw [← hforest, buildForest_commitment, sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem signPayload_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    ExecEq T T'
      (SigGolfCandidate.Research.SharedForest.signPayload cache message)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateNonce S F _)) ?_
  intro rho _
  refine ExecEq.bind (execEq_outF hC.toFamAgree
    (respects_famOutP S (fun a => CanonicalRef.respectsP_sharedDigestSearch a _ _ _ _) F)) ?_
  intro selected _
  cases selected with
  | none => exact ExecEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter, output⟩
    refine ExecEq.bind (signFromOutput_famEq hC htree hF _ _ _ _) ?_
    intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem authenticatedSign_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    ExecEq T T'
      (PairedOuter.FullGame.authenticatedSign published request)
      (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) ?_
  intro tag _
  split
  · exact signPayload_famEq hC htree hF _ _
  · exact ExecEq.pure' _ _ _

theorem keygen_famEq (hC : FamCongr S (sourceMessages T) F T T')
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    ExecEq T T' SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygen := by
  have hp : ExecEq T T' keygenPayload keygenPayload := by
    refine ⟨?_, ?_⟩
    · rw [Wots.Mask.eval_keygenPayload_wots, Wots.Mask.eval_keygenPayload_wots, wotsTree_congrF hC hF]
      exact eval_outF hC.toFamAgree (respects_famOut S (fun c => Wots.Mask.respects_keygenRest c _) F)
    · refine Wots.Mask.queried_length_keygenPayload_congr (S := FamOut S F)
        (fun L => respects_famOut S (fun c => Wots.Mask.respects_buildTopLevels c L) F) T' T hC.out ?_
      rw [(SigGolfCandidate.T3.Correctness.eval_buildTopTree T').trans (WCT9.wotsTree_top T').symm,
        (SigGolfCandidate.T3.Correctness.eval_buildTopTree T).trans (WCT9.wotsTree_top T).symm,
        wotsTree_congrF hC hF]
  unfold SigGolfCandidate.T3.keygen
  refine ExecEq.bind hp ?_
  rintro ⟨pk, region⟩ _
  exact ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) fun _ _ => ExecEq.pure' _ _ _

/-- **Family congruence of the reference game.** If `T'` agrees with `T` outside family `F` (and on the other halves
of its cells), and on the rows of all of `F`'s chains from their signed digits on and on their frontier values, the
honest reference game is unchanged. -/
theorem referenceGame_fam (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T' adversary q = PairedReference.referenceGame T adversary q :=
  PairedReference.referenceGame_congr _ _ (keygen_famEq hC hF).1 (keygen_famEq hC hF).2
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).1)
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).2) adversary q
end Game

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamTest ====
section

/-! # Family restart, step P4a: the seed-test program of a family (r3-lean-seedfam)

Family port of the per-leaf test program (`WotsLeafTest`: `Leaf.TParams/tY/fY/prefAns/isTestQ`,
`Normalized.Test.{publicAt, withPublic, pubAns, testImpl, evalT_testRun, tdepth_testImpl, enT_testImpl}` and the
`RawLeaf` route part, plus `WotsLeafCore.{PData, mkP, tY_mkP, evaluate_tY}`), with the chains of a leaf
`Fin (chainCount L.lay)` replaced by the chains `GChainW g w` of a family `F` of `g` leaves of `w` chains.

* `FamRestart`: `TParamsF`, `tYF`, `fYF`, `prefAnsF`, `isTestQF`, `PDataF`, `mkPF`, `tYF_mkPF`, `evaluate_tYF`.
* `CanonicalRef.Normalized.FamTest`: `publicAtF`, `withPublicF`, `pubAnsF`, `testImplF`, `evalT_pubAnsF`,
  `testImpl_bridgeF`, `evalT_testRunF`, `tdepth_testImplF`, `enT_testImplF`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF zeroOfF zhF)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable

/-- Parameters of the family test program: row functions and labels of the family's step-0 rows (`g`, `lab`), of
chain `a`'s prefix tables (`gt`, `labt`), and the revealed seeds `r`. -/
structure TParamsF (G W d : Nat) where
  g : GChainW G W → Digest → Digest
  lab : GChainW G W → Digest
  gt : Fin d → Digest → Digest
  labt : Fin d → Digest
  r : GChainW G W → Digest

section Defs
variable {G W : Nat} (d : Nat) (Rev : Finset (GChainW G W)) (aF : Free Rev) (P : TParamsF G W d)

/-- Chain `a`'s prefix tables, row `0` programmed at the seed `s` (the other rows at `0`). -/
def tYF (s : Digest) : Fin d → Digest → Digest :=
  fun i => Function.update (P.gt i) (if i.val = 0 then s else 0) (P.labt i)

/-- Step-0 rows of the family's chains: revealed chains programmed at `r`, unrevealed ones at `y`. -/
noncomputable def fYF (y : Free Rev → Digest) : GChainW G W → Digest → Digest :=
  fun c => Function.update (P.g c) (if hc : c ∈ Rev then P.r c else y ⟨c, hc⟩) (P.lab c)

/-- Answer to a prefix query of chain `a`: row `0` is a test on `a`'s seed. -/
noncomputable def prefAnsF (p : Fin d × Digest) : OracleComp (TSpec (Free Rev) Digest) Digest :=
  if p.1.val = 0 then (fun b => if b then P.labt p.1 else P.gt p.1 p.2) <$> testQ (aF, p.2)
  else pure (Function.update (P.gt p.1) 0 (P.labt p.1) p.2)
end Defs

theorem evalT_prefAnsF {G W d : Nat} {Rev : Finset (GChainW G W)} (aF : Free Rev) (P : TParamsF G W d)
    (y : Free Rev → Digest) (p : Fin d × Digest) :
    evalT y (prefAnsF d Rev aF P p) = PMF.pure (tYF d P (y aF) p.1 p.2) := by
  unfold prefAnsF tYF
  split_ifs with h0
  · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]
  · rfl

/-- Queries answered by a test: chain `a`'s prefix row `0`, and step-0 rows of unrevealed chains of the family. -/
noncomputable def isTestQF (G W : Nat) (F : FamAddr) (a : ChainAddr) (d : Nat) (Rev : Finset (GChainW G W)) :
    RefWorld.Domain → Prop
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => p.1.val = 0
      | none =>
          match zeroOfF G W F input with
          | some cv => cv.1 ∉ Rev
          | none => False
  | _ => False

/-- The free parameters of the programmed world: the family's step-0 row functions and labels, `a`'s prefix tables
and labels. -/
abbrev PDataF (G W d : Nat) :=
  ((GChainW G W → Digest → Digest) × (GChainW G W → Digest)) × ((Fin d → Digest → Digest) × (Fin d → Digest))
/-- Test-program parameters from the free parameters and the revealed seeds. -/
def mkPF {G W d : Nat} (p : PDataF G W d) (r : GChainW G W → Digest) : TParamsF G W d :=
  ⟨p.1.1, p.1.2, p.2.1, p.2.2, r⟩

theorem tYF_mkPF {G W d : Nat} (p : PDataF G W d) (r r' : GChainW G W → Digest) :
    tYF d (mkPF p r) = tYF d (mkPF p r') := rfl

/-- The endpoint of the programmed prefix tables: independent of the seed they are programmed at. -/
theorem evaluate_tYF {G W d : Nat} (hd : 1 ≤ d) (P : TParamsF G W d) (σ : Digest) :
    evaluate (tYF d P σ) σ = evaluate (tYF d P 0) 0 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [evaluate]
  have h1 : Fin.tail (tYF (d' + 1) P σ) = Fin.tail (tYF (d' + 1) P 0) := by
    funext i v
    simp only [Fin.tail, tYF, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : tYF (d' + 1) P σ 0 σ = tYF (d' + 1) P 0 0 0 := by
    simp only [tYF, Fin.val_zero, if_true, Function.update_self]
  rw [h1, h2]

end ClaudeWCT.W9.T3.Security.Wots.FamRestart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTest
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF zeroOfF zhF)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The public table `B` with the used halves of the family's step-0 rows replaced by `f`. -/
noncomputable def publicAtF (G W : Nat) (F : FamAddr) (B : Answers) (f : GChainW G W → Digest → Digest)
    (input : HashInput) : HashOutput :=
  match zeroOfF G W F input with
  | some cv => joinHalf (zhF G W F cv.1) (f cv.1 cv.2) (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input))))
  | none => B (.inl (.inr input))
noncomputable def withPublicF (G W : Nat) (F : FamAddr) (B : Answers) (f : GChainW G W → Digest → Digest) : Answers
  | .inl (.inr input) => publicAtF G W F B f input
  | .inl (.inl coin) => B (.inl (.inl coin))
  | .inr coordinate => B (.inr coordinate)

section Defs
variable (G W : Nat) (F : FamAddr) (a : ChainAddr) (d : Nat) (B : Answers)
  (Rev : Finset (GChainW G W)) (aF : Free Rev) (P : TParamsF G W d)
/-- Answer to any other public query: step-0 rows of unrevealed chains of the family are tests. -/
noncomputable def pubAnsF (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOfF G W F input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (joinHalf (zhF G W F cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input)))))
      else (fun b => joinHalf (zhF G W F cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (B (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world (family version). -/
noncomputable def testImplF : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
              record obs p w)) <$> prefAnsF d Rev aF P p
      | none => StateT.lift (pubAnsF G W F d B Rev P input)
  | .inr _ => pure ()
end Defs

section Bridge
variable {G W : Nat} {F : FamAddr} {a : ChainAddr} {d : Nat} (B : Answers)
  {Rev : Finset (GChainW G W)} (aF : Free Rev) (P : TParamsF G W d)

theorem evalT_pubAnsF (y : Free Rev → Digest) (input : HashInput) :
    evalT y (pubAnsF G W F d B Rev P input) = PMF.pure (publicAtF G W F B (fYF d Rev P y) input) := by
  unfold pubAnsF publicAtF
  cases hz : zeroOfF G W F input with
  | none => rfl
  | some cv =>
    simp only
    unfold fYF
    split_ifs with hc
    · rfl
    · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]

/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridgeF (y : Free Rev → Digest) (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImplF G W F a d B Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF d P (y aF)))
        (Route.routeImpl a d B (withPublicF G W F B (fYF d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImplF, Route.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImplF, Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
            record s p w)) <$> prefAnsF d Rev aF P p) = _
        rw [evalT_map, evalT_prefAnsF, PMF.pure_map]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAnsF G W F d B Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAnsF B P y input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The family test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRunF (y : Free Rev → Digest) {α : Type} (Gm : OracleComp RefWorld α) (obs : TObs d) :
    evalT y ((simulateQ (testImplF G W F a d B Rev aF P) Gm).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF d P (y aF))
        (simulateQ (Route.routeImpl a d B (withPublicF G W F B (fYF d Rev P y))) Gm) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridgeF B aF P y q
end Bridge

section Counts
variable {G W : Nat} {F : FamAddr} {a : ChainAddr} {d : Nat} (B : Answers) {Rev : Finset (GChainW G W)}
  (aF : Free Rev) (P : TParamsF G W d)

theorem tdepth_testImplF (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImplF G W F a d B Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
  rcases q with (n | input) | u
  · simp only [testImplF, StateT.run_lift]
    rw [if_neg (by simp [RefCharged])]
    refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
    rw [Nat.add_zero, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _) from
      (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.tdepth_coin]
    simp [ClaudeWCT.Arith.SideChannel.tdepth_pure]
  · rw [if_pos (by simp [RefCharged])]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [testImplF, hp, StateT.run_mk]
        refine (tdepth_map_le _ _).trans ?_
        unfold prefAnsF
        split_ifs with h0
        · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
        · exact Nat.zero_le _
    | none =>
        simp only [testImplF, hp, StateT.run_lift]
        refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
        rw [Nat.add_zero]
        unfold pubAnsF
        cases hz : zeroOfF G W F input with
        | none => exact Nat.zero_le _
        | some cv =>
            simp only
            split_ifs with hc
            · exact Nat.zero_le _
            · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
  · exact Nat.zero_le _

theorem enT_testImplF (y : Free Rev → Digest) (q : RefWorld.Domain) (s : TObs d) :
    enT y ((testImplF G W F a d B Rev aF P q).run s) = if isTestQF G W F a d Rev q then 1 else 0 := by
  rcases q with (n | input) | u
  · rw [if_neg (by simp [isTestQF])]
    simp only [testImplF, StateT.run_lift]
    rw [ClaudeWCT.Arith.SideChannel.enT_bind, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _)
      from (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.enT_coin]
    simp [ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_const]
  · cases hp : PrefixGame.rowOf a d input with
    | some p =>
        have hT : isTestQF G W F a d Rev (.inl (.inr input)) ↔ p.1.val = 0 := by simp only [isTestQF, hp]
        simp only [testImplF, hp, StateT.run_mk]
        rw [enT_map]
        unfold prefAnsF
        split_ifs with h0 h1 h1
        · rw [enT_map, enT_testQ]
        · exact absurd (hT.mpr h0) h1
        · exact absurd (hT.mp h1) h0
        · rfl
    | none =>
        simp only [testImplF, hp, StateT.run_lift]
        rw [ClaudeWCT.Arith.SideChannel.enT_bind,
          show (fun x => enT y (pure (x, s) : OracleComp (TSpec (Free Rev) Digest) _)) = fun _ => (0 : ℝ) from rfl,
          ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
        unfold pubAnsF
        cases hz : zeroOfF G W F input with
        | none =>
            rw [if_neg (by simp only [isTestQF, hp, hz]; exact id)]
            rfl
        | some cv =>
            have hT : isTestQF G W F a d Rev (.inl (.inr input)) ↔ cv.1 ∉ Rev := by simp only [isTestQF, hp, hz]
            simp only
            split_ifs with hc h1 h1
            · exact absurd hc (hT.mp h1)
            · rfl
            · rw [enT_map, enT_testQ]
            · exact absurd (hT.mpr hc) h1
  · rw [if_neg (by simp [isTestQF])]
    rfl
end Counts

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTest

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable raw_ov_const otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

/-- A row of chain `a` at a step `s < 256` that is a step-0 row of family chain `c` is step 0 of a chain with the
same layer and parity, hence read through the same half. -/
theorem chainHigh_of_zeroOfF {G W : Nat} {F : FamAddr} {a : ChainAddr} {s : Nat} {v : Digest} (hs : s < 256)
    (hac : a.chain < 2 ^ 24) (hW : W < 2 ^ 24)
    {cv : GChainW G W × Digest} (hz : zeroOfF G W F (chainRowW a s v) = some cv) :
    WCT9.chainHigh a.key.lay a.chain s = zhF G W F cv.1 := by
  have he := zeroOfF_some hz
  obtain ⟨hh, -⟩ := chainInputW_fields he
  obtain ⟨hl, -, -, hi, hst⟩ := chainHeader_fields hh
  have hs0 : s = 0 := by simp only [Nat.zero_mod] at hst; omega
  have hcc : (chainOfF G W F cv.1).chain = cv.1.2.val := rfl
  have hpar : a.chain % 2 = cv.1.2.val % 2 := by simp only [Nat.reducePow] at hi; omega
  have hl' : a.key.lay = F.lay := hl
  subst hs0
  -- img-v6 (r3-lean-nonsec): top G-ness depends on the chain index, so pin the index (both are < 2^24)
  have hcv := cv.1.2.isLt
  have heq : a.chain = cv.1.2.val := by
    rw [hcc] at hi
    simp only [Nat.reducePow] at hi
    omega
  rw [show zhF G W F cv.1 = WCT9.chainHigh F.lay cv.1.2.val 0 from rfl, hl', heq]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

/-- The real (in-tree) family chains revealed (depth `0`) in `R`; phantom chains are never revealed. -/
noncomputable def revSetF (S : FamScheme) (F : FamAddr) (R : Tables U) :
    Finset (GChainW (S.grp F.lay) (chainCount F.lay)) :=
  Finset.univ.filter fun c => S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay ∧
    CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0

/-- The family seed of chain `c = (l, i)` for coefficients `K` (point `l·stride + i + 1`). -/
noncomputable def seedOfF {m G W : Nat} (st : Nat) (K : Fin m → Digest) (c : GChainW G W) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn K) (c.1.val * st + c.2.val + 1)
/-- Step-0 rows of the family's chains programmed at the family seeds. -/
noncomputable def progFF {m G W : Nat} (st : Nat) (g : GChainW G W → Digest → Digest) (Lab : GChainW G W → Digest)
    (K : Fin m → Digest) : GChainW G W → Digest → Digest :=
  fun c => Function.update (g c) (seedOfF st K c) (Lab c)

section Pairing
variable {G W b n : Nat} {F : FamAddr}
include hU

/-- Pairing stage 1: the family override keeps the half of a step-0 row of the family that its chain does not
read. -/
theorem otherZ_ovF (hF : FamOk G W b n F) (R : Tables U) (X : FamData G W n) (input : HashInput)
    {cv : GChainW G W × Digest} (hz : zeroOfF G W F input = some cv) :
    WCT9.halfOf (!zhF G W F cv.1) (raw (ovF G W b n F R X) (.inl (.inr input))) =
      WCT9.halfOf (!zhF G W F cv.1) (raw R (.inl (.inr input))) := by
  rw [zeroOfF_some hz, raw_ovF_zero hU hF, halfOf_not_joinHalf]

/-- C3: the half of a chain-`a` row that the prefix game keeps from the rest table is unchanged by the family
override. -/
theorem otherHalf_ovF (hF : FamOk G W b n F) (R : Tables U) (X : FamData G W n) (a : ChainAddr) (s : Nat)
    (v : Digest) (hs : s < 256) (hac : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (ovF G W b n F R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOfF G W F (chainRowW a s v) with
  | none => rw [raw_ovF_pub R X _ hz]
  | some cv => rw [chainHigh_of_zeroOfF hs hac hF.width hz, otherZ_ovF hU hF R X _ hz]
end Pairing

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable raw_ov_const otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

section Program
variable (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hF haF hd1

theorem fill_pub_indepF (X X' : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest)
    (input : HashInput)
    (h : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), c ≠ ca → ∀ v,
      input ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inl (.inr input)) =
      fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X') e
        (.inl (.inr input)) := by
  rw [fill_pubF hU S hF ca haF R hd1 X e input h, fill_pubF hU S hF ca haF R hd1 X' e input h]

/-- The seed of a member chain after the fill: the family seed `seedOfF`. -/
theorem wotsSeed_fill_memF (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (e : Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) e)
        (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree (famLeaf (S.grp F.lay) F l).leaf c =
      seedOfF (S.stride F.lay) K ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) :=
  wotsSeed_fillF hU S hF ca haF R hd1 K f e l c hc

/-- **Programmed family congruence.** With the step-0 rows of the family's chains programmed at the family seeds
(`progFF`), the filled tables for two coefficient vectors agreeing on the seeds of the real revealed (depth-0)
chains are family congruent. -/
theorem famCongr_progF (g : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest)
    (Lab : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (K K' : Fin (S.size F.lay F.fam) → Digest)
    (hKK : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
        seedOfF (S.stride F.lay) K c = seedOfF (S.stride F.lay) K' c) (e : Digest) :
    FamCongr S zeroMessages F
      (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)) e)
      (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K', progFF (S.stride F.lay) g Lab K')) e) := by
  set T := fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
    (K, progFF (S.stride F.lay) g Lab K)) e with hT
  set T' := fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
    (K', progFF (S.stride F.lay) g Lab K')) e with hT'
  have hA := famAgree_fill hU S hF ca haF R hd1 (K, progFF (S.stride F.lay) g Lab K) e
  have hA' := famAgree_fill hU S hF ca haF R hd1 (K', progFF (S.stride F.lay) g Lab K') e
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hnz : ∀ (L : LeafAddr) (c s : Nat) (v : Digest), s ≠ 0 → s < 256 →
      ∀ c' : GChainW (S.grp F.lay) (chainCount F.lay), ∀ v',
        chainRowW ⟨L, c⟩ s v ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c') 0 v' := by
    intro L c s v hs hs256 c' v' he
    have := (chainHeader_fields (chainInputW_fields he).1).2.2.2.2
    omega
  refine ⟨⟨fun q hq => (hA'.out q hq).trans (hA.out q hq).symm, fun o ho hno =>
    (hA'.half o ho hno).trans (hA.half o ho hno).symm⟩, ?_, ?_⟩
  · intro l hl c hc s v hs hs256
    rw [depth_fillF hU S hF ca haF R hd1 _ e] at hs
    by_cases hs0 : s = 0
    · subst hs0
      have hca : ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) ≠ ca := by
        intro hca
        have : CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = RawPrefix.restDepth a R := by
          rw [← hda, haF, ← hca]; rfl
        omega
      have hrev := hKK (l, ⟨c, hc⟩) hl
        (by show CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = 0; omega)
      rw [show (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) =
        chainOfF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩) from rfl]
      rw [hT, hT', fill_zeroF hU S hF ca haF R hd1 _ e _ hca, fill_zeroF hU S hF ca haF R hd1 _ e _ hca]
      simp only [progFF]
      rw [hrev]
    · exact fill_pub_indepF hU S hF ca haF R hd1 _ _ e _ (fun c' _ v' => hnz _ c s v hs0 hs256 c' v')
  · intro l hl c hc
    by_cases hca : ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) = ca
    · have hb : (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) = a := by rw [haF, ← hca]; rfl
      rw [hb, fill_frontier_selfF hU S hF ca haF R hd1, fill_frontier_selfF hU S hF ca haF R hd1]
    · unfold CanonicalRef.frontierValue honestChainValueW
      simp only
      rw [depth_fillF hU S hF ca haF R hd1 _ e, depth_fillF hU S hF ca haF R hd1 _ e,
        wotsSeed_fill_memF hU S hF ca haF R hd1 _ _ e l c hc, wotsSeed_fill_memF hU S hF ca haF R hd1 _ _ e l c hc]
      rcases Nat.eq_zero_or_pos (CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩) with h0 | hpos
      · rw [h0, hKK (l, ⟨c, hc⟩) hl h0, chainW_zero']
        simp only [evalWithAnswerFn_pure]
      · obtain ⟨k, hk⟩ : ∃ k, CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = 1 + k :=
          ⟨CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ - 1, by omega⟩
        rw [hk, eval_chainW_add', eval_chainW_add' T]
        have hlab : ∀ X : Fin (S.size F.lay F.fam) → Digest,
            evalWithAnswerFn (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
              (X, progFF (S.stride F.lay) g Lab X)) e)
              (WCT9.chainW (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
                (famLeaf (S.grp F.lay) F l).leaf c 0 1
                (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)))) =
              Lab (l, ⟨c, hc⟩) := by
          intro X
          rw [eval_chainW_one', pad64_chainInputW]
          rw [show WCT9.chainInputW (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
              (famLeaf (S.grp F.lay) F l).leaf c 0
              (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay))) =
            chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩)) 0
              (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay))) from rfl,
            fill_zeroF hU S hF ca haF R hd1 _ e (l, ⟨c, hc⟩) hca]
          rw [show WCT9.chainHigh (famLeaf (S.grp F.lay) F l).lay c 0 =
            zhF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩) from rfl, halfOf_joinHalf]
          simp only [progFF, Function.update_self]
        rw [hlab K', hlab K]
        have hk256 : 0 + 1 + k ≤ 256 := by
          have := CanonicalRef.Mask.depth_le_seven (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩; omega
        refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
        refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
        rw [pad64_chainInputW]
        exact (fill_pub_indepF hU S hF ca haF R hd1 _ _ e _
          (fun c' _ v' => hnz _ c step value (by omega) (by omega) c' v')).symm
end Program

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

theorem famOut_encodingF (e : Wots.Enc.EncIndex) : FamOut S F (.inl (.inr (Wots.Enc.encInput e))) := by
  intro l c step value _ _ he
  have hn := nonEnc_chainRow ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
  apply hn
  rw [← he]
  exact Wots.Enc.encInput_encHeader e

/-- Family agreement survives the normalization of the encoding rows. -/
theorem famAgree_normalizeF {R R' : Tables U}
    (hC : FamAgree S F (raw R) (raw R')) (hm : sourceMessages (raw R') = sourceMessages (raw R)) :
    FamAgree S F (answers hU R) (answers hU R') := by
  refine ⟨?_, ?_⟩
  · intro query hq
    rcases query with (coin | input) | coordinate
    · exact hC.out _ hq
    · by_cases hu : input ∈ U
      · rw [show answers hU R' (.inl (.inr input)) = (normalize hU R').2 ⟨input, hu⟩ from RawPrefix.raw_mem _ _ hu,
          show answers hU R (.inl (.inr input)) = (normalize hU R).2 ⟨input, hu⟩ from RawPrefix.raw_mem _ _ hu]
        change MessageSwap.table zeroMessages (sourceMessages (raw R')) _ _ hU R'.2 ⟨input, hu⟩ =
          MessageSwap.table zeroMessages (sourceMessages (raw R)) _ _ hU R.2 ⟨input, hu⟩
        have ht : MessageSwap.table zeroMessages (sourceMessages (raw R')) zeroMessages_fit
            (sourceMessages_fit (raw R')) hU =
            MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit (sourceMessages_fit (raw R)) hU := by
          congr 1
        rw [ht]
        by_cases he : ∃ e, Wots.Enc.encInput e = input
        · obtain ⟨e, rfl⟩ := he
          rw [MessageSwap.table_at, MessageSwap.table_at]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ (famOut_encodingF S _)).trans (RawPrefix.raw_mem _ _ _))
        · push_neg at he
          rw [MessageSwap.table_other _ _ _ _ _ _ _ he, MessageSwap.table_other _ _ _ _ _ _ _ he]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ hq).trans (RawPrefix.raw_mem _ _ _))
      · rw [show answers hU R' (.inl (.inr input)) = (0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu,
          show answers hU R (.inl (.inr input)) = (0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu]
    · exact hC.out _ hq
  · intro o ho hno
    rw [Wots.Leaf.eval_lowerSeedPair, Wots.Leaf.eval_lowerSeedPair,
      nonEnc hU R' _ (by trivial), nonEnc hU R _ (by trivial)]
    simpa only [Wots.Leaf.eval_lowerSeedPair] using hC.half o ho hno

/-- Real members of a family whose tree is in range are source leaves. -/
theorem sourceLeaf_memF (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay) (l : Fin (S.grp F.lay))
    (hl : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay) :
    WotsExtract.SourceLeaf7 (famLeaf (S.grp F.lay) F l) :=
  ⟨htb, hl⟩

/-- Family congruence survives the normalization (messages switch from `zeroMessages` to the source messages). -/
theorem famCongr_normalizeF (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {R R' : Tables U}
    (hC : FamCongr S zeroMessages F (raw R) (raw R')) :
    FamCongr S (sourceMessages (answers hU R)) F (answers hU R) (answers hU R') := by
  have hm := sourceMessages_congrF hC hF
  have hmn : sourceMessages (answers hU R') = sourceMessages (answers hU R) := by
    rw [messages, messages, hm]
  refine ⟨famAgree_normalizeF hU S hC.toFamAgree hm, ?_, ?_⟩
  · intro l hl c hc step value hs hstep
    rw [depth_eq hU R ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl)] at hs
    rw [answers_chainRow, answers_chainRow]
    exact hC.rows l hl c hc step value hs hstep
  · intro l hl c hc
    rw [← hmn, frontier_eq hU R' ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl), hmn,
      frontier_eq hU R ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl)]
    exact hC.front l hl c hc

section Route
attribute [local irreducible] raw normalize answers RawPrefix.fill ovF

theorem normalized_public_congrF {R R' : Tables U}
    (hC : FamAgree S F (raw R) (raw R')) (hm : sourceMessages (raw R') = sourceMessages (raw R))
    (input : HashInput) (heq : raw R' (.inl (.inr input)) = raw R (.inl (.inr input))) :
    answers hU R' (.inl (.inr input)) = answers hU R (.inl (.inr input)) := by
  by_cases hn : Wots.Enc.NonEnc (.inl (.inr input))
  · rw [nonEnc hU R' _ hn, nonEnc hU R _ hn, heq]
  · apply (famAgree_normalizeF hU S hC hm).out
    intro l c step value hc hs he
    have hne := nonEnc_chainRow ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
    apply hn
    rw [he]
    exact hne

/-- **Programmed route.** The prefix-game routing of the family-programmed table at `K` equals the routing of the
table at `K'` with the family's step-0 rows publicly programmed at `K` (`FamTest.withPublicF`), when `K` and `K'`
give the same seeds on the real revealed chains. -/
theorem route_programmedF (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd : 1 ≤ RawPrefix.restDepth a R)
    (g : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest)
    (Lab : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (K K' : Fin (S.size F.lay F.fam) → Digest)
    (hKK : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
        seedOfF (S.stride F.lay) K c = seedOfF (S.stride F.lay) K' c) (e : Digest) :
    Route.routeImpl a (RawPrefix.restDepth a R)
      (answers hU (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)))
      (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)) e)) =
    Route.routeImpl a (RawPrefix.restDepth a R)
      (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K', progFF (S.stride F.lay) g Lab K')) e))
      (FamTest.withPublicF (S.grp F.lay) (chainCount F.lay) F
        (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K', progFF (S.stride F.lay) g Lab K')) e))
        (progFF (S.stride F.lay) g Lab K)) := by
  have hC := famCongr_progF hU S hF ca haF R hd g Lab K K' hKK e
  have hac : a.chain < 2 ^ 24 := by
    have h1 : a.chain = ca.2.val := by rw [haF]; rfl
    have h2 := ca.2.isLt
    have h3 := ClaudeWCT.W9.T3M.Extract.chainCount_le F.lay
    omega
  have hm := sourceMessages_congrF hC hF.leaf
  funext query
  rcases query with (coin | input) | coord
  · simp only [Route.routeImpl]
  · simp only [Route.routeImpl]
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | some p =>
      simp only
      congr 1
      funext v
      congr 1
      have hp7 : (p.1 : Nat) < 256 := by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega
      rw [PrefixGame.rowOf_some hp, answers_chainRow, answers_chainRow,
        otherHalf_fill hU a _ e _ _ hp7, otherHalf_ovF hU hF _ _ _ _ _ hp7 hac, otherHalf_ovF hU hF _ _ _ _ _ hp7 hac]
    | none =>
      simp only [FamTest.withPublicF, FamTest.publicAtF]
      congr 1
      cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
      | none =>
        simp only
        symm
        apply normalized_public_congrF hU S hC.toFamAgree hm
        exact (fill_pub_indepF hU S hF ca haF R hd _ _ e input (by
          intro c hca v he
          rw [he, zeroOfF_chainRow hF] at hz
          cases hz)).symm
      | some cv =>
        simp only
        have hca : cv.1 ≠ ca := by
          intro he
          apply PrefixGame.rowOf_none hp (⟨0, hd⟩, cv.2)
          rw [zeroOfF_some hz, he, ← haF]
        have hpX : PrefixGame.rowOf a (RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay)
            (S.size F.lay F.fam) F R (K', progFF (S.stride F.lay) g Lab K'))) input = none := by
          rw [restDepth_ovF S hF R _ a]; exact hp
        rw [zeroOfF_some hz] at hpX
        have hzX := hz
        rw [zeroOfF_some hz] at hzX
        rw [zeroOfF_some hz, answers_chainRow, answers_chainRow,
          high_fill_nonprefix hU a _ e _ hpX, otherZ_ovF hU hF _ _ _ hzX]
        exact fill_zeroF hU S hF ca haF R hd _ e cv.1 hca cv.2
  · simp only [Route.routeImpl]
end Route

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCaps ====
section

/-! # Family restart: the reveal caps (r3-lean-seedfam)

`FamCaps S`: the policy fact behind `revSet_card_le`, per leaf (every leaf's reference digits have at most `zcap lay`
zeros: lower 5, top 7 in T51 (9 in #938's v6); `famCount - 3` today) and the coefficient budget of every family
(`zcap · members + 3 ≤ size`, members = `min grp (2^height − grp·f)`, so the short last family is covered).
`leafCaps` instantiates it for today's scheme from `Core.revSet_card_le`. -/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
attribute [local instance] Classical.propDecidable

/-- Real members of family `f` of layer `lay`. -/
def famMembers (S : FamScheme) (lay : Layer) (f : Nat) : Nat := min (S.grp lay) (2 ^ height lay - S.grp lay * f)

/-- Reveal caps of a family scheme. -/
structure FamCaps (S : FamScheme) where
  zcap : Layer → Nat
  zeros_le : ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay
  size_ge : ∀ lay f, zcap lay * famMembers S lay f + 3 ≤ S.size lay f

/-- Caps of the `Correctness` layout with today's producer: top 7 (T51; #938: 9), lower 5 revealed seeds per leaf;
the family budgets `7 · 4 + 3 = 31` (top) and `5 r + 3 = famSize` (lower, `r` real members). -/
def layoutCaps : FamCaps layoutScheme where
  zcap lay := if lay = 0 then 7 else 5
  zeros_le R L := by
    have h := Core.revSet_card_le_cap L R
    unfold Core.revSet at h
    exact h
  size_ge lay f := by
    show (if lay = 0 then 7 else 5) * min (WCT9.famGrp lay) (2 ^ height lay - WCT9.famGrp lay * f) + 3 ≤
      WCT9.famSize lay f
    unfold WCT9.famGrp WCT9.famSize
    split_ifs with h
    · -- T51: 4-leaf top families, 7 · 4 + 3 = 31 = topCoefCount (img-v6: 9 · 4 + 3 = 39)
      have := min_le_left 4 (2 ^ height lay - 4 * f)
      simp only [SigGolfCandidate.T3.topCoefCount]; omega
    · exact le_rfl

end ClaudeWCT.W9.T3.Security.Wots.FamRestart
end
