import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafSum

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

/-- **Reference ≤ mixture + error** (lower chains). -/
theorem ref_le_mix :
    Pr[E | referenceExperiment adversary q] ≤
      ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | mixLaw a (restDepth a R) R GD] +
        errC adversary q a := by
  obtain ⟨hGq, hleaf⟩ := ref_hyps q ha GD out hout
  rw [ref_prob_eq_frozen q ha GD out hout E F hF hF0 hG hEF,
    ← errC_eq q ha GD out hout]
  exact frozen_le_mix ha.2 hleaf GD hG q hGq F hF hF0

/-- **Mixture ≤ reference + error** (lower chains). -/
theorem mix_le_ref :
    ∑' R, restLaw adversary R * Pr[F (restDepth a R) R | mixLaw a (restDepth a R) R GD] ≤
      Pr[E | referenceExperiment adversary q] + errC adversary q a := by
  obtain ⟨hGq, hleaf⟩ := ref_hyps q ha GD out hout
  rw [ref_prob_eq_frozen q ha GD out hout E F hF hF0 hG hEF,
    ← errC_eq q ha GD out hout]
  exact mix_le_frozen ha.2 hleaf GD hG q hGq F hF hF0
end Ref

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
