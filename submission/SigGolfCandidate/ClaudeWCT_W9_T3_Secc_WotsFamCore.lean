import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamTest
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCaps
import SigGolfCandidate.ClaudeWCT_Arith_GroupedFamilyS

/-! # Family restart, step P4b: frozen/mix law decomposition and per-table restart error (r3-lean-seedfam)

Family port of `WotsLeafCore` (namespace `CanonicalRef.Normalized.Core`, the normalized per-leaf part): the leaf `L`
becomes a family `F` of a scheme `S : FamScheme`, chain `a = chainOfF g w F ca`, the leaf data `LeafData L` becomes
`FamData g w (S.size F.lay F.fam)`, the leaf override `ovL` becomes `ovF`, the points `ptL` become `gptS stride`.
The laws `Core.gameD / frozenLaw / mixLaw` do not depend on the leaf and are reused.

* `KstF`, `seedsR_KstF`, `ePF`, `TstF`, `testRunF`;
* `GD_progF`, `frozen_pointF`, `route_withPublic_congrF`, `mix_pointF`, `ovSeed_ovF`;
* `revSetF_card_le` (from `FamCaps S`);
* `frozen_decompF`, `frozen_decompYF`, `mix_decompYF`;
* `tdepth_testRunF`, `errRF`, `frozen_le_mix_RF`, `mix_le_frozen_RF`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
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
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF

/-- Coefficients interpolating the revealed seeds `r` (a canonical choice). -/
noncomputable def KstF (S : FamScheme) (F : FamAddr) (R : Tables U) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) : Fin (S.size F.lay F.fam) → Digest :=
  if h : ∃ K, seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = r then h.choose else 0

theorem seedsR_KstF (S : FamScheme) (F : FamAddr) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest) :
    seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K := by
  unfold KstF
  rw [dif_pos ⟨K, rfl⟩]
  exact (⟨K, rfl⟩ : ∃ K', seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K).choose_spec

/-- The endpoint of the programmed prefix tables. -/
def ePF {G W d : Nat} (p : PDataF G W d) : Digest := evaluate (tYF d (mkPF p 0) 0) 0

/-- The canonical honest table: coefficients `KstF r`, the family's step-0 rows programmed at their seeds. -/
noncomputable def TstF (S : FamScheme) (F : FamAddr) (a : ChainAddr) (R : Tables U)
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) : Answers :=
  answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r))) (ePF p))

/-- The family test program. -/
noncomputable def testRunF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (GD : Answers → OracleComp RefWorld Res) (aF : Free (RawFam.revSetF S F R)) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) :
    OracleComp (TSpec (Free (RawFam.revSetF S F R)) Digest) (Res × TObs (RawPrefix.restDepth a R)) :=
  (simulateQ (FamTest.testImplF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (TstF hU S F a R p r) (RawFam.revSetF S F R) aF (mkPF p r))
    (GD (TstF hU S F a R p r))).run (fun _ _ => none)

/-- The seed of chain `a = chainOfF ca` after the family override is the family seed. -/
theorem ovSeed_ovF (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest) (f : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest)
    (s : Digest) : RawPrefix.ovSeed a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) s = RawFam.seedOfF (S.stride F.lay) K ca := by
  unfold RawPrefix.ovSeed
  subst haF
  exact RawFam.wotsSeed_ovF S hF R K f ca.1 ca.2.val ca.2.isLt

section Points
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG

theorem GD_progF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) :
    GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))) =
      GD (TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  unfold TstF
  apply Eq.symm
  apply hG
  apply RawFam.famCongr_normalizeF hU S htb hF.leaf
  apply RawFam.famCongr_progF hU S hF ca haF R hd1
  intro c hl hc
  have h := congrFun (seedsR_KstF S F R K) c
  have hc' : c ∈ (RawFam.revSetF S F R) := by
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
  simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm

include haca

theorem frozen_pointF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (tYF (RawPrefix.restDepth a R) (mkPF p 0) (RawFam.seedOfF (S.stride F.lay) K ca))
      (simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)))
        (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))
        (GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))) (fun _ _ => none) =
    evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  rw [GD_progF hU S hF htb ca haF R hd1 GD hG K p]
  unfold testRunF
  rw [FamTest.evalT_testRunF]
  have hfy : fYF (RawPrefix.restDepth a R) (RawFam.revSetF S F R) (mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) =
      RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K := by
    funext c
    unfold fYF RawFam.progFF mkPF
    simp only
    split_ifs with hc
    · unfold seedsR; rw [if_pos hc]; rfl
    · rfl
  have hya : seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K aF = RawFam.seedOfF (S.stride F.lay) K ca := by
    show RawFam.seedOfF (S.stride F.lay) K aF.1 = RawFam.seedOfF (S.stride F.lay) K ca
    rw [haca]
  rw [hfy, hya, tYF_mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) 0]
  have hKK : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
      RawFam.seedOfF (S.stride F.lay) K c = RawFam.seedOfF (S.stride F.lay) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) c := by
    intro c hl hc
    have h := congrFun (seedsR_KstF S F R K) c
    have hc' : c ∈ (RawFam.revSetF S F R) := by
      simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
    simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm
  rw [RawFam.route_programmedF hU S hF ca haF R hd1 p.1.1 p.1.2 K _ hKK (ePF p)]
  simp only [TstF]
end Points

/-- Routing only reads the public programming `f` off chain `ca` (chain `a`'s step-0 row is a prefix row). -/
theorem route_withPublic_congrF {G W : Nat} {F : FamAddr} {a : ChainAddr} {ca : GChainW G W}
    (haF : a = chainOfF G W F ca) {d : Nat} (hd : 1 ≤ d) (B : Answers) (f f' : GChainW G W → Digest → Digest)
    (hf : ∀ c : GChainW G W, c ≠ ca → f c = f' c) :
    Route.routeImpl a d B (FamTest.withPublicF G W F B f) = Route.routeImpl a d B (FamTest.withPublicF G W F B f') := by
  funext query
  rcases query with (coin | input) | coord
  · simp only [Route.routeImpl]
  · simp only [Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p => rfl
    | none =>
      simp only [FamTest.withPublicF, FamTest.publicAtF]
      congr 1
      cases hz : RawFam.zeroOfF G W F input with
      | none => rfl
      | some cv =>
        simp only
        rw [hf cv.1 (by
          intro he
          apply PrefixGame.rowOf_none hp (⟨0, hd⟩, cv.2)
          rw [RawFam.zeroOfF_some hz, he, ← haF])]
  · simp only [Route.routeImpl]

section Mix
attribute [local irreducible] TstF
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG haca

theorem mix_pointF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF (RawPrefix.restDepth a R) (mkPF p 0) s)
      (simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)))
        (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))
        (GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))) (fun _ _ => none) =
    evalT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  rw [GD_progF hU S hF htb ca haF R hd1 GD hG K p]
  unfold testRunF
  rw [FamTest.evalT_testRunF]
  have hya : seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s aF = s := by unfold seedsH; rw [if_pos rfl]
  rw [hya, tYF_mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) 0]
  have hKK : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
      RawFam.seedOfF (S.stride F.lay) K c = RawFam.seedOfF (S.stride F.lay) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) c := by
    intro c hl hc
    have h := congrFun (seedsR_KstF S F R K) c
    have hc' : c ∈ (RawFam.revSetF S F R) := by
      simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
    simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm
  rw [RawFam.route_programmedF hU S hF ca haF R hd1 p.1.1 p.1.2 K _ hKK (ePF p)]
  have hbase : answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K),
      RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) (ePF p)) =
      TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by unfold TstF; rfl
  rw [hbase]
  rw [route_withPublic_congrF haF hd1 (TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)
    (fYF (RawPrefix.restDepth a R) (RawFam.revSetF S F R) (mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s))]
  intro c hca
  funext v
  unfold fYF RawFam.progFF mkPF
  simp only
  split_ifs with hc
  · unfold seedsR; rw [if_pos hc]; rfl
  · have hne : (⟨c, hc⟩ : Free (RawFam.revSetF S F R)) ≠ aF := by
      intro he
      apply hca
      rw [← haca, ← he]
    unfold seedsH
    rw [if_neg hne]
    rfl
end Mix

/-- **Reveal cap of a family**: only the real members' depth-0 chains are revealed, each real member contributes at most
`zcap`, and the coefficient budget covers `zcap · members + 3`. -/
theorem revSetF_card_le {S : FamScheme} (C : FamCaps S) (F : FamAddr) (R : Tables U) :
    (RawFam.revSetF S F R).card + 3 ≤ S.size F.lay F.fam := by
  set realL : Finset (Fin (S.grp F.lay)) :=
    Finset.univ.filter fun l => S.grp F.lay * F.fam + l.val < 2 ^ height F.lay with hreal
  set Z : Fin (S.grp F.lay) → Finset (GChainW (S.grp F.lay) (chainCount F.lay)) := fun l =>
    (Finset.univ.filter fun i : Fin (chainCount F.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, i⟩ = 0).map
      ⟨fun i => (l, i), fun i j h => by simpa using h⟩ with hZ
  have hsub : RawFam.revSetF S F R ⊆ realL.biUnion Z := by
    intro c hc
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_biUnion]
    refine ⟨c.1, ?_, ?_⟩
    · rw [hreal, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc.1⟩
    · rw [hZ]
      exact Finset.mem_map.mpr ⟨c.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2⟩, rfl⟩
  have hZc : ∀ l, (Z l).card ≤ C.zcap F.lay := by
    intro l
    rw [hZ]
    simp only [Finset.card_map]
    convert C.zeros_le R (famLeaf (S.grp F.lay) F l) <;> rfl
  have hrc : realL.card ≤ famMembers S F.lay F.fam := by
    unfold famMembers
    refine le_min ?_ ?_
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · have hs : realL.map Fin.valEmbedding ⊆ Finset.range (2 ^ height F.lay - S.grp F.lay * F.fam) := by
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨l, hl, rfl⟩ := hx
        rw [hreal, Finset.mem_filter] at hl
        rw [Finset.mem_range, Fin.valEmbedding_apply]
        omega
      have := Finset.card_le_card hs
      rwa [Finset.card_map, Finset.card_range] at this
  calc (RawFam.revSetF S F R).card + 3 ≤ (realL.biUnion Z).card + 3 :=
        Nat.add_le_add_right (Finset.card_le_card hsub) 3
    _ ≤ (∑ l ∈ realL, (Z l).card) + 3 := Nat.add_le_add_right Finset.card_biUnion_le 3
    _ ≤ (∑ _l ∈ realL, C.zcap F.lay) + 3 := Nat.add_le_add_right (Finset.sum_le_sum fun l _ => hZc l) 3
    _ = C.zcap F.lay * realL.card + 3 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ C.zcap F.lay * famMembers S F.lay F.fam + 3 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hrc) 3
    _ ≤ S.size F.lay F.fam := C.size_ge F.lay F.fam

section Decomp
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG haca

/-- **Frozen law, decomposed** (family version). -/
theorem frozen_decompF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind (fun y => Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
          (fun res => (ePF p, res)))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hfr : ∀ f, Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca))) (fun _ _ => none)).map
          (fun res => (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca), res))) := by
    intro f
    unfold Core.frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R)) =
      PMF.uniformOfFintype ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovF S hF ca haF R K f]
    exact uniform_bind_const _
  simp only [hfr]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca) := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca)) (RawFam.seedOfF (S.stride F.lay) K ca) = ePF (gl, q) :=
    evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := frozen_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Frozen law with the family data, decomposed.** -/
theorem frozen_decompYF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
          (fun res => (((K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)), (ePF p, res))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hfr : ∀ f, Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca))) (fun _ _ => none)).map
          (fun res => (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca), res))) := by
    intro f
    unfold Core.frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R)) =
      PMF.uniformOfFintype ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovF S hF ca haF R K f]
    exact uniform_bind_const _
  simp only [hfr, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca) := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca)) (RawFam.seedOfF (S.stride F.lay) K ca) = ePF (gl, q) :=
    evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := frozen_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Mixture law with the family data, decomposed.** -/
theorem mix_decompYF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (PMF.uniformOfFintype Digest).bind (fun s =>
          (evalT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
            (fun res => (((K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)), (ePF p, res)))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hmx : ∀ f, Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype Digest).bind (fun s => (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind
        (fun t => (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t s)) (fun _ _ => none)).map
          (fun res => (evaluate t s, res)))) := by
    intro f
    unfold Core.mixLaw
    simp only [SphincsSecurity.Concrete.PartialChainEndpoint.realRun,
      SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
      SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.bind_bind, PMF.bind_map,
      PMF.map_comp, Function.comp_def]
    rw [PMF.bind_comm]
  simp only [hmx, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext s
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then s else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then s else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) s := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) s) s = ePF (gl, q) := evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := mix_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q) s
  exact congrArg (PMF.map _) hp
end Decomp

#print axioms revSetF_card_le
#print axioms frozen_decompYF
#print axioms mix_decompYF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
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
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF

open ClaudeWCT.Arith.SideChannel (tdepth prT amLen)
section PerR
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)

include hGq in
theorem tdepth_testRunF (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) :
    tdepth (testRunF hU GD aF p r) ≤ q :=
  ClaudeWCT.Arith.SideChannel.tdepth_simulate_le _ RefCharged
    (fun qu s => FamTest.tdepth_testImplF (F := F) (a := a) (TstF hU S F a R p r) aF _ qu s) _ q _ (hGq _)

/-- The per-rest-table error of the family restart: `2 δ K(q) E_{p,K}[amLen]`. -/
noncomputable def errRF : ℝ :=
  ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K : Fin (S.size F.lay F.fam) → Digest,
    (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ * ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
      (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))))

variable (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
include hF htb haF hd1 hG haca hGq C hws hb

theorem frozen_le_mix_RF (E : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam) → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hE : ∀ (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (K K' : Fin (S.size F.lay F.fam) → Digest),
      seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
        E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) = E (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errRF hU (a := a) R GD aF q) := by
  rw [frozen_decompYF hU S hF htb ca haF R hd1 GD hG aF haca, mix_decompYF hU S hF htb ca haF R hd1 GD hG aF haca]
  set A : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R) → ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) → (Res × TObs (RawPrefix.restDepth a R)) → Prop :=
    fun p r res => E (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r)) (ePF p, res) with hAdef
  have hA : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      (fun res => E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) (ePF p, res)) = A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_KstF S F R K).symm]
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : ((RawFam.revSetF S F R)).card + 3 ≤ S.size F.lay F.fam := revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), gptS (S.stride F.lay) c < 1024 := ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
          (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
            (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set Cc : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hx
  set z := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) =>
    prT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hz
  set m := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))
  have hZ : 0 ≤ errRF hU (a := a) R GD aF q := by
    unfold errRF
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K, x K p ≤
      ∑ K, (∑ s, z K p s) / Fintype.card Digest + Cc * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_le hpt hsmall hRev aF (A p)
      (fun r => testRunF hU GD aF p r) q (fun r => tdepth_testRunF hU R GD aF q hGq p r)
  have e1 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errRF hU (a := a) R GD aF q = ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * (Cc * ∑ K, m K p) := by
    unfold errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)

theorem mix_le_frozen_RF (E : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam) → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hE : ∀ (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (K K' : Fin (S.size F.lay F.fam) → Digest),
      seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
        E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) = E (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errRF hU (a := a) R GD aF q) := by
  rw [frozen_decompYF hU S hF htb ca haF R hd1 GD hG aF haca, mix_decompYF hU S hF htb ca haF R hd1 GD hG aF haca]
  set A : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R) → ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) → (Res × TObs (RawPrefix.restDepth a R)) → Prop :=
    fun p r res => E (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r)) (ePF p, res) with hAdef
  have hA : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      (fun res => E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) (ePF p, res)) = A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_KstF S F R K).symm]
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : ((RawFam.revSetF S F R)).card + 3 ≤ S.size F.lay F.fam := revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), gptS (S.stride F.lay) c < 1024 := ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
          (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
            (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set Cc : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hx
  set z := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) =>
    prT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hz
  set m := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))
  have hZ : 0 ≤ errRF hU (a := a) R GD aF q := by
    unfold errRF
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K, (∑ s, z K p s) / Fintype.card Digest ≤
      ∑ K, x K p + Cc * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_ge hpt hsmall hRev aF (A p)
      (fun r => testRunF hU GD aF p r) q (fun r => tdepth_testRunF hU R GD aF q hGq p r)
  have e1 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errRF hU (a := a) R GD aF q = ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * (Cc * ∑ K, m K p) := by
    unfold errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e2, e1, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)

end PerR

#print axioms frozen_le_mix_RF
#print axioms mix_le_frozen_RF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
