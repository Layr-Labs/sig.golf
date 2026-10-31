import Mathlib.Tactic
import SigGolfCandidate.Merge021
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge110
import SigGolfCandidate.Merge111

-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCore ====
section

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

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamSum1 ====
section

/-! # Family restart, step P5a: family test counts and their allocation (r3-lean-seedfam)

Family analogues of `Normalized.Core.{StepZeroUnrev, NL, isTestQ_iff, NL_mkSample, sum_NL_le}` (WotsLeafSum):
a test query of family `F` is a step-0 row of one of its unrevealed chains (phantom chains of a short last family are
always unrevealed); every trace entry is a test query of at most one family, and is charged to the source chains of
that family only, at most `grp · chainCount` of them (`sum_NL_leF`: today `54`, v6 `max(4·54, 7·43) = 301`).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized (depth_eq)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SphincsSecurity.QueryCap (recorded counted calls)
open SigGolfCandidate.T3.Security.Wots.Mask (chainCount_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (S : FamScheme)

/-- The family of a leaf. -/
def famOf (L : LeafAddr) : FamAddr := ⟨L.lay, L.tree, L.leaf / S.grp L.lay⟩

/-- Member `l` of `F` is a real (in-tree) leaf. -/
def RealM (F : FamAddr) (l : Nat) : Prop := S.grp F.lay * F.fam + l < 2 ^ height F.lay

/-- `input` is the step-0 row of an unrevealed chain of family `F` in `T` (phantom chains count as unrevealed). -/
def StepZeroUnrevF (F : FamAddr) (T : Answers) (input : HashInput) : Prop :=
  ∃ c : GChainW (S.grp F.lay) (chainCount F.lay),
    (¬RealM S F c.1.val ∨ CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) ≠ 0) ∧
      ∃ v, input = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v

/-- Number of test queries of family `F` in a reference sample. -/
noncomputable def NLF (F : FamAddr) (s : RefSample) : ℕ :=
  (s.trace.filter fun e => decide (StepZeroUnrevF S F s.answers e.1)).length

/-- Test count charged to chain `a`: its family's. -/
noncomputable def NLaF (a : ChainAddr) (s : RefSample) : ℕ := NLF S (famOf S a.key) s

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

theorem zeroOfF_none_ne {g w b n : Nat} {F : FamAddr} (hF : FamOk g w b n F) {input : HashInput}
    (h : zeroOfF g w F input = none) (c : GChainW g w) (v : Digest) : input ≠ chainRowW (chainOfF g w F c) 0 v := by
  rintro rfl
  rw [zeroOfF_chainRow hF] at h
  cases h

theorem isTestQF_iff {F : FamAddr} (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (T : Answers)
    (hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
        CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c))
    (hreal : RealM S F ca.1.val) (query : RefWorld.Domain) :
    isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R) query ↔
      ∃ x, query = .inl (.inr x) ∧ StepZeroUnrevF S F T x := by
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hw := hF.width
  rcases query with (k | input) | u
  · simp [isTestQF]
  · simp only [isTestQF, Sum.inl.injEq, Sum.inr.injEq, exists_eq_left']
    unfold StepZeroUnrevF
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | some p =>
        have hin := PrefixGame.rowOf_some hp
        simp only
        constructor
        · intro h0
          refine ⟨ca, Or.inr ?_, p.2, ?_⟩
          · rw [hT ca hreal, ← haF, hda]
            have := p.1.isLt
            omega
          · rw [hin, ← haF, show p.1.val = 0 from h0]
        · rintro ⟨c, -, v, he⟩
          rw [hin] at he
          have h1 : (p.1 : ℕ) < 256 := by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega
          have hc1 := c.2.isLt
          have hca1 := ca.2.isLt
          obtain ⟨-, -, hs, -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F c)
            (by subst haF; unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) h1 (by omega) he
          exact hs
    | none =>
        simp only
        cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
        | none =>
            simp only [false_iff, not_exists, not_and]
            intro c _ v he
            exact zeroOfF_none_ne hF hz c v he
        | some cv =>
            simp only
            have he := zeroOfF_some hz
            constructor
            · intro hc
              refine ⟨cv.1, ?_, cv.2, he⟩
              by_cases hr : RealM S F cv.1.1.val
              · right
                rw [hT cv.1 hr]
                intro h0
                apply hc
                unfold revSetF
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hr, h0⟩
              · exact Or.inl hr
            · rintro ⟨c, hc, v, he'⟩
              rw [he] at he'
              obtain ⟨h1, -⟩ := chainRowF_zero_inj hF he'
              subst h1
              unfold revSetF
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
              intro hr h0
              rcases hc with hc | hc
              · exact hc hr
              · exact hc (by rw [hT cv.1 hr]; exact h0)
  · simp [isTestQF]

include hU in
theorem NL_mkSampleF {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
    {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : RealM S F ca.1.val)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) (run : SeedResult) :
    NLF S F (mkSample (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) run) =
      calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R)) run.2 := by
  unfold NLF mkSample
  simp only
  rw [traceOf_filter_length]
  have hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
          (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) := by
    intro c hc
    rw [depth_eq hU _ _ (sourceLeaf_memF S htb c.1 hc), RawPrefix.depth_ov a (by have := RawPrefix.restDepth_le a R; omega)]
  congr 1
  funext query
  exact propext (isTestQF_iff S hF ca haF R _ hT hreal query).symm

/-- Step-0 rows determine their family (families of source leaves; trees below `2^40`, leaves below `2^32`). -/
theorem stepZero_fam_unique (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L L' : LeafAddr}
    (hL : WotsExtract.SourceLeaf L) (hL' : WotsExtract.SourceLeaf L') {T T' : Answers} {input : HashInput}
    (h : StepZeroUnrevF S (famOf S L) T input) (h' : StepZeroUnrevF S (famOf S L') T' input) :
    famOf S L = famOf S L' := by
  obtain ⟨c, -, v, rfl⟩ := h
  obtain ⟨c', -, v', he⟩ := h'
  have hb : ∀ K : LeafAddr, WotsExtract.SourceLeaf K → K.tree < 2 ^ 40 ∧ K.leaf < 2 ^ 12 := fun K hK => by
    refine ⟨by have := hK.1; omega, ?_⟩
    have h1 := hK.2
    have h2 : 2 ^ height K.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le K.lay)
    omega
  have hmem : ∀ (K : LeafAddr) (l : Fin (S.grp K.lay)), WotsExtract.SourceLeaf K →
      S.grp K.lay * (K.leaf / S.grp K.lay) + l.val < 2 ^ 32 := by
    intro K l hK
    have := (hb K hK).2; have := l.isLt; have := hgrp K.lay
    have : S.grp K.lay * (K.leaf / S.grp K.lay) ≤ K.leaf := Nat.mul_div_le _ _
    omega
  have hc1 := c.2.isLt; have hc2 := c'.2.isLt
  have hw1 := chainCount_le (famOf S L).lay; have hw2 := chainCount_le (famOf S L').lay
  obtain ⟨hal, -, -, -⟩ := chainInputW_eq_chainRowW (a := chainOfF _ _ (famOf S L') c')
    (by unfold chainOfF; simp only [Nat.reducePow]; omega) (by unfold chainOfF; simp only [Nat.reducePow]; omega)
    (by omega) (by omega) he
  have hE := hal.eq_of_lt (show L.tree < 2 ^ 40 from (hb L hL).1)
    (show S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val < 2 ^ 32 from hmem L c.1 hL)
    (show L'.tree < 2 ^ 40 from (hb L' hL').1)
    (show S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val < 2 ^ 32 from hmem L' c'.1 hL')
  have hlay : L.lay = L'.lay := by have h0 := congrArg LeafAddr.lay hE; exact h0
  have htree : L.tree = L'.tree := by have h0 := congrArg LeafAddr.tree hE; exact h0
  have hleaf : S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val =
      S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val := by have h0 := congrArg LeafAddr.leaf hE; exact h0
  rw [← hlay] at hleaf
  have hg := S.grp_pos L.lay
  have hc : c.1.val < S.grp L.lay := c.1.isLt
  have hc' : c'.1.val < S.grp L.lay := by
    have h := c'.1.isLt
    have hgg : S.grp (famOf S L').lay = S.grp L.lay := by show S.grp L'.lay = S.grp L.lay; rw [hlay]
    omega
  have e1 : (S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val) / S.grp L.lay = L.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (S.grp L.lay * (L'.leaf / S.grp L.lay) + c'.1.val) / S.grp L.lay = L'.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hfam : L.leaf / S.grp L.lay = L'.leaf / S.grp L'.lay := by
    rw [← hlay, ← e1, ← e2, hleaf]
  unfold famOf
  rw [hfam, hlay, htree]

/-- Source chains of one family: at most `grp · chainCount`. -/
theorem card_famChains_le (F : FamAddr) :
    (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card ≤
      S.grp F.lay * chainCount F.lay := by
  classical
  have hinj : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ∀ a' ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ((a.key.leaf % S.grp F.lay, a.chain) : Nat × Nat) = (a'.key.leaf % S.grp F.lay, a'.chain) → a = a' := by
    intro a ha a' ha' he
    simp only [Finset.mem_filter] at ha ha'
    have h1 := congrArg FamAddr.lay ha.2; have h2 := congrArg FamAddr.tree ha.2; have h3 := congrArg FamAddr.fam ha.2
    have h1' := congrArg FamAddr.lay ha'.2; have h2' := congrArg FamAddr.tree ha'.2
    have h3' := congrArg FamAddr.fam ha'.2
    unfold famOf at h1 h2 h3 h1' h2' h3'
    simp only at h1 h2 h3 h1' h2' h3'
    simp only [Prod.mk.injEq] at he
    have e1 : a.key.leaf = S.grp F.lay * F.fam + a.key.leaf % S.grp F.lay := by
      rw [← h1, ← h3]; exact (Nat.div_add_mod _ _).symm
    have e2 : a'.key.leaf = S.grp F.lay * F.fam + a'.key.leaf % S.grp F.lay := by
      rw [← h1', ← h3']; exact (Nat.div_add_mod _ _).symm
    have hl : a.key.leaf = a'.key.leaf := by rw [e1, e2, he.1]
    have hk : a.key = a'.key := by
      cases ha0 : a.key; cases ha0' : a'.key
      rw [ha0] at h1 h2 hl; rw [ha0'] at h1' h2' hl
      simp only at h1 h2 hl h1' h2'
      rw [h1, ← h1', h2, ← h2', hl]
    cases a; cases a'
    simp only at hk he
    rw [hk, he.2]
  calc (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card
      ≤ ((Finset.range (S.grp F.lay)) ×ˢ (Finset.range (chainCount F.lay))).card := by
        apply Finset.card_le_card_of_injOn (fun a => (a.key.leaf % S.grp F.lay, a.chain))
        · intro a ha
          simp only [Finset.mem_filter, Finset.coe_filter, Set.mem_setOf_eq] at ha
          have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha.1
          have h1 := congrArg FamAddr.lay ha.2
          unfold famOf at h1; simp only at h1
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact ⟨Nat.mod_lt _ (S.grp_pos _), h1 ▸ hs.2⟩
        · intro a ha a' ha' he
          exact hinj a (by simpa using ha) a' (by simpa using ha') he
    _ = S.grp F.lay * chainCount F.lay := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **Per-sample allocation:** every trace entry is a test of at most one family, charged to at most `Cmax` source
chains (`Cmax ≥ grp · chainCount` on every layer). -/
theorem sum_NL_leF (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : Nat) (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax)
    (s : RefSample) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s ≤ Cmax * s.trace.length := by
  classical
  let test : FamAddr → Entry → Prop := fun F e =>
    StepZeroUnrevF S F s.answers e.1 ∧ ∃ L, WotsExtract.SourceLeaf L ∧ famOf S L = F
  have hcongr : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s =
      (s.trace.filter fun e => decide (test (famOf S a.key) e)).length := by
    intro a ha
    have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha
    unfold NLaF NLF
    congr 1
    apply List.filter_congr
    intro e _
    simp only [test, decide_eq_decide]
    exact ⟨fun h => ⟨h, a.key, hs.1, rfl⟩, fun h => h.1⟩
  rw [Finset.sum_congr rfl hcongr]
  exact ClaudeWCT.Arith.SideChannel.GroupedFamily.sum_charge_le SigGolfCandidate.T3.Security.Wots.sourceChains
    (fun a => famOf S a.key) test Cmax
    (fun e F F' h h' => by
      obtain ⟨h1, L, hL, rfl⟩ := h
      obtain ⟨h1', L', hL', rfl⟩ := h'
      exact stepZero_fam_unique S hgrp hL hL' h1 h1')
    (fun F => (card_famChains_le S F).trans (hC F.lay)) s.trace

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamLift ====
section

/-! # Family restart, steps P4c/P5b: the lift over the rest tables and the seed-error charge (r3-lean-seedfam)

Family port of `WotsLeafLift` (normalized part: `selfF`, `errAR`, `restLaw_resampleL_tsum`, `resample_ind`,
`frozen_le_mix`, `mix_le_frozen`) and of the normalized charge of `WotsLeafSum` (`enT_testRun_rec`, `tcount`,
`errR_le_count`, `count_frozen`, `frozenCount`, `errAR_sum_le`, `reference_map_NL`, `frozenCount_eq`, `errC`,
`errC_le`, `errC_sum_le`). The leaf `L` becomes a family `F` of a scheme `S`, chain `a = chainOfF ca`, the leaf
resampling becomes `RawFam.restLaw_resampleF`, and the per-leaf allocation `54` becomes `Cmax ≥ grp · chainCount`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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

/-- The chain `a = chainOfF ca` as an unrevealed chain of its family (depth `≥ 1`). -/
def selfFF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U)
    (hd1 : 1 ≤ RawPrefix.restDepth a R) : Free (RawFam.revSetF S F R) :=
  ⟨ca, by
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _ h
    rw [RawPrefix.restDepth_eq, haF] at hd1
    omega⟩

/-- Per rest table error of the family restart (zero at depth `0`). -/
noncomputable def errARF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) {Res : Type}
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : Tables U) : ℝ≥0∞ :=
  if hd1 : 1 ≤ RawPrefix.restDepth a R then
    ENNReal.ofReal (FamCore.errRF hU (a := a) R GD (selfFF S ca haF R hd1) q) else 0

include hU in
theorem restLaw_resampleF_tsum {g w b n : Nat} {F : FamAddr} (hF : RawFam.FamOk g w b n F)
    (Φ : Tables U → ℝ≥0∞) :
    ∑' R, Core.restLaw U R * Φ R =
      ∑' R, Core.restLaw U R * ∑' y, PMF.uniformOfFintype (FamData g w n) y * Φ (RawFam.ovF g w b n F R y) := by
  unfold Core.restLaw
  have h := RawFam.restLaw_resampleF hU hF (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (FamData g w n)).bind (fun y => PMF.pure (RawFam.ovF g w b n F R y)) =
    (PMF.uniformOfFintype (FamData g w n)).map (RawFam.ovF g w b n F R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

theorem revSetF_ovF (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    RawFam.revSetF S F (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
      RawFam.revSetF S F R := by
  unfold RawFam.revSetF
  congr 1
  funext c
  rw [RawFam.depth_ovF S hF R y]

section Lift
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (E : (d : ℕ) → Tables U → Digest × (Res × TObs d) → Prop)
  (hE : ∀ (R : Tables U) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
      (K K' : Fin (S.size F.lay F.fam) → Digest),
    seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
      E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) =
        E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')))
  (hE0 : ∀ R z, ¬E 0 R z)

include hU hF in
/-- Resampling the family data, the event and the law at the resampled table. -/
theorem resample_indF (Law : (d : ℕ) → Tables U → PMF (Digest × (Res × TObs d))) :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R] =
      ∑' R, Core.restLaw U R * Pr[fun w => E (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R w.1) w.2 |
        (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
          (fun y => (Law (RawPrefix.restDepth a R)
            (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)).map
              (fun z => (y, z)))] := by
  rw [restLaw_resampleF_tsum hU hF (fun R => Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R])]
  refine tsum_congr fun R => ?_
  congr 1
  rw [prob_bind]
  refine tsum_congr fun y => ?_
  congr 1
  rw [prob_pmf_map, RawFam.restDepth_ovF S hF R y a]
  rfl

include hU hF htb haF hG hGq C hws hb hE hE0

/-- **Frozen ≤ mixture + error** (family version). -/
theorem frozen_le_mixF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.frozen_le_mix_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le

/-- **Mixture ≤ frozen + error** (family version). -/
theorem mix_le_frozenF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.mix_le_frozen_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le
end Lift

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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
open ClaudeWCT.Arith.SideChannel (exT enT amLen tdepth)
open SphincsSecurity.QueryCap (recorded counted calls)

/-- Expected number of tests = expected number of test queries in the recorded list (family version). -/
theorem enT_testRun_recF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (G0 : Answers → OracleComp RefWorld Res) (aF : Free (RawFam.revSetF S F R))
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
    (r : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (y : Free (RawFam.revSetF S F R) → Digest) :
    enT y (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) =
      exT y (fun out => (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
          (RawFam.revSetF S F R)) out.1.2 : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) := by
  unfold FamCore.testRunF
  rw [enT_simulate y _ (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R))
      (fun q s => FamTest.enT_testImplF (F := F) (a := a) (FamCore.TstF hU S F a R p r) aF _ y q s),
    counted_recorded, simulateQ_map, StateT.run_map, exT_map']
  rfl

section ErrR
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T))
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)

/-- The family test-query count of a run. -/
noncomputable def tcountF (out : (Res × List RefWorld.Domain) × TObs (RawPrefix.restDepth a R)) : ℕ :=
  calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) out.1.2

include hGq C hws hb in
/-- **The family error is charged to the expected test count.** -/
theorem errR_le_countF :
    FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q * (1 - (Fintype.card Digest : ℝ)⁻¹ * q) ≤
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
  have hRev : (RawFam.revSetF S F R).card + 3 ≤ S.size F.lay F.fam := FamCore.revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), gptS (S.stride F.lay) c < 1024 :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC'
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹
  have hC0 : 0 ≤ C' := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
    (Nat.cast_nonneg _)
  have hcK : 0 ≤ cK := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcp : 0 ≤ cp := inv_nonneg.mpr (Nat.cast_nonneg _)
  have e1 : FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (C' * cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest, amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
          (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    unfold FamCore.errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
      ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * (cp *
        exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
          (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
          (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => ?_
    rw [enT_testRun_recF]
    unfold tcountF
    ring
  rw [e1, e2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hf := ClaudeWCT.Arith.SideChannel.family_amLen_le hpt hsmall hRev
    (fun r => FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) q
    (fun r => FamCore.tdepth_testRunF hU R (fun T => recorded (G0 T)) aF q hGq p r)
  calc C' * cK * cp * (∑ K : Fin (S.size F.lay F.fam) → Digest,
        amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)
      = C' * cK * cp * ((∑ K : Fin (S.size F.lay F.fam) → Digest,
          amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
          (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) := by ring
    _ ≤ C' * cK * cp * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hC0 hcK) hcp)
    _ = C' * ((cK * cp) * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
        ring

include hF htb haF hd1 hG haca in
/-- The expected test count of the decomposed frozen law (family version). -/
theorem count_frozenF :
    ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ∑' z, ((PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)))) z *
          (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
  rw [FamCore.frozen_decompF hU S hF htb ca haF R hd1 (fun T => recorded (G0 T)) hG aF haca]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  have hx : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      ∑' out, evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) out *
          (tcountF (S := S) (F := F) (a := a) R out : ℝ≥0∞) =
      ENNReal.ofReal (exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
    intro K p
    rw [ClaudeWCT.Arith.SideChannel.ofReal_exT _ (fun _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  simp only [hx, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [Finset.sum_comm]
  have hnn : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      0 ≤ exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
    fun K p => ClaudeWCT.Arith.SideChannel.exT_nonneg _ (fun _ => Nat.cast_nonneg _) _
  rw [ENNReal.ofReal_sum_of_nonneg (fun K _ => Finset.sum_nonneg fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p)))]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)), ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    ← inv_card_eq_ofReal, ← inv_card_eq_ofReal]
end ErrR

section Charge
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T)) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1)

/-- The rest-table-averaged expected family test count of the frozen law. -/
noncomputable def frozenCountF (GD : Answers → OracleComp RefWorld (Res × List RefWorld.Domain)) : ℝ≥0∞ :=
  ∑' R, Core.restLaw U R * ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD z *
    (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) z.2.1.2 : ℝ≥0∞)

include hF htb haF hG hGq C hws hb hq in
theorem errAR_sum_leF :
    ∑' R, Core.restLaw U R * errARF hU S ca haF (fun T => recorded (G0 T)) q R ≤
      ENNReal.ofReal (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
        frozenCountF hU (S := S) (F := F) (a := a) (fun T => recorded (G0 T)) := by
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
    (1 - (Fintype.card Digest : ℝ)⁻¹ * q) with hC'
  have hpos : 0 < 1 - (Fintype.card Digest : ℝ)⁻¹ * q := by linarith
  let Ψd : ℕ → Tables U → ℝ≥0∞ := fun d R' =>
    ∑' z, Core.frozenLaw hU a d R' (fun T => recorded (G0 T)) z *
      (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a d (RawFam.revSetF S F R')) z.2.1.2 : ℝ≥0∞)
  have hres := restLaw_resampleF_tsum hU hF (fun R => Ψd (RawPrefix.restDepth a R) R)
  unfold frozenCountF
  change _ ≤ ENNReal.ofReal C' * ∑' R, Core.restLaw U R * Ψd (RawPrefix.restDepth a R) R
  rw [hres, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  unfold errARF
  split_ifs with hd1
  · have hy : ∀ y, Ψd (RawPrefix.restDepth a
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y))
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
        ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)) z * (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
      intro y
      rw [RawFam.restDepth_ovF S hF R y a]
      simp only [Ψd, revSetF_ovF S hF R y]
      rfl
    simp only [hy]
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
      ← count_frozenF hU hF htb ca haF R hd1 G0 hG (selfFF S ca haF R hd1) rfl]
    rw [← ENNReal.ofReal_mul (by
      rw [hC']; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr
        (Nat.cast_nonneg _)) 3)) (Nat.cast_nonneg _)) hpos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := errR_le_countF hU (a := a) R G0 (selfFF S ca haF R hd1) q hGq C hws hb
    rw [hC', div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact h
  · exact bot_le
end Charge

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : FamSum.RealM S F ca.1.val)

include hF htb haF hreal in
theorem reference_map_NLF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    (PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F) =
      (Core.restLaw (PairedReference.referenceInputs adversary)).bind (fun R =>
        (Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)).map
          (fun z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
            (RawFam.revSetF S F R)) z.2.1.2)) := by
  rw [reference_map_eq_frozen adversary q a ha (FamSum.NLF S F)
    (fun R z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
      (RawFam.revSetF S F R)) z.2.1.2)
    (fun R x res _ => FamSum.NL_mkSampleF S (referenceInputs_subset adversary) hF htb ca haF hreal R x res.1)]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  unfold Core.frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, Core.seedGame_eq_gameD]
  rfl

include hF htb haF hreal in
/-- **The frozen family count is the reference family count.** -/
theorem frozenCount_eqF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    frozenCountF (referenceInputs_subset adversary) (S := S) (F := F) (a := a) (Core.GDseed adversary q) =
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) := by
  have e1 : ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) =
      ∑' n, ((PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F)) n * (n : ℝ≥0∞) := by
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rw [e1, reference_map_NLF S hF htb ca haF hreal q ha,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rfl
end Ref

/-- Family chain coordinates of a chain `a` in its family `famOf S a.key`: member `leaf % grp`, chain `a.chain`. -/
def caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    GChainW (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) :=
  (⟨a.key.leaf % S.grp a.key.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨a.chain, hac⟩)

theorem chainOf_caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    a = chainOfF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (FamSum.famOf S a.key)
      (caOf S a hac) := by
  obtain ⟨⟨lay, tree, leaf⟩, c⟩ := a
  simp only [chainOfF, famLeaf, caOf, FamSum.famOf, Nat.div_add_mod]

theorem real_caOf (S : FamScheme) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    FamSum.RealM S (FamSum.famOf S a.key) (caOf S a ha.2).1.val := by
  unfold FamSum.RealM
  show S.grp a.key.lay * (a.key.leaf / S.grp a.key.lay) + a.key.leaf % S.grp a.key.lay < 2 ^ height a.key.lay
  rw [Nat.div_add_mod]
  exact ha.1.2

/-- **Admissibility of the family of a source leaf** (group size at most `2^20`). -/
theorem famOk_of_source (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L : LeafAddr}
    (hL : WotsExtract.SourceLeaf7 L) : FamOkS S (FamSum.famOf S L) := by
  have hleaf : L.leaf < 2 ^ 12 := by
    have h1 := hL.2
    have h2 : 2 ^ height L.lay ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le L.lay)
    omega
  have hdiv : L.leaf / S.grp L.lay ≤ L.leaf := Nat.div_le_self _ _
  have hmd : S.grp L.lay * (L.leaf / S.grp L.lay) ≤ L.leaf := Nat.mul_div_le _ _
  have hg := hgrp L.lay
  have hcnt : S.cnt L.lay * (L.leaf / S.grp L.lay) ≤ 512 * 4096 :=
    Nat.mul_le_mul (S.cnt_le L.lay) (by omega)
  have hc := S.cnt_le L.lay
  refine ⟨S.grp_pos _, ?_, ?_, ?_, ?_, S.size_le _ _⟩
  · have := chainCount_le L.lay
    show chainCount L.lay < 2 ^ 24
    omega
  · show S.grp L.lay * (L.leaf / S.grp L.lay) + S.grp L.lay ≤ 2 ^ 24
    omega
  · show L.tree < 2 ^ 40
    have := hL.tree_lt
    omega
  · show S.cnt L.lay * (L.leaf / S.grp L.lay) + S.cnt L.lay ≤ 2 ^ 33
    omega

/-- The seed-game body is invariant under family congruence. -/
theorem GDseed_fam (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (q : ℕ) (T T' : Answers)
    (h : FamGame.FamCongr S (sourceMessages T) F T T') : Core.GDseed adversary q T' = Core.GDseed adversary q T := by
  unfold Core.GDseed
  rw [FamGame.referenceGame_fam h hF.tree hF.leaf adversary q]

/-- **The per-chain seed-test error of the family restart** (every source chain, charged to its family). -/
noncomputable def errCF (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ)
    (a : ChainAddr) : ℝ≥0∞ :=
  if h : WotsExtract.SourceChain7 a then
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
      errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (caOf S a h.2) (chainOf_caOf S a h.2)
        (Core.GDseed adversary q) q R
  else 0

theorem errC_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) (a : ChainAddr) :
    errCF S adversary q a ≤ ENNReal.ofReal (Core.errConst q) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) := by
  unfold errCF
  split_ifs with h
  · have hF := famOk_of_source S hgrp h.1
    unfold FamSum.NLaF
    rw [← frozenCount_eqF S hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2) (real_caOf S h) q h]
    exact errAR_sum_leF (referenceInputs_subset adversary) hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2)
      (fun T => PairedReference.referenceGame T adversary q) (fun T T' h' => GDseed_fam S hF q T T' h') q
      (fun T => Core.GDseed_queryBound q T) C (hws _) (hb _) hq
  · exact bot_le

/-- **Total seed-test error of the family restart**: `Cmax ≥ grp · chainCount` on every layer. -/
theorem errC_sum_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : ℕ)
    (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a ≤
      ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  calc ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a
      ≤ ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, ENNReal.ofReal (Core.errConst q) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) :=
        Finset.sum_le_sum fun a _ => errC_leF S hgrp C hws hb q hq a
    _ = ENNReal.ofReal (Core.errConst q) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
        refine mul_le_mul' le_rfl ?_
        calc ∑' s, PairedReference.referenceExperiment adversary q s *
              ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞)
            ≤ ∑' s, PairedReference.referenceExperiment adversary q s * ((Cmax : ℝ≥0∞) * q) := by
              refine ENNReal.tsum_le_tsum fun s => ?_
              by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
              · refine mul_le_mul' le_rfl ?_
                have h1 := FamSum.sum_NL_leF S hgrp Cmax hC s
                have h2 := Core.ref_trace_length_le adversary q s hs
                have : ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s ≤ Cmax * q := by
                  calc _ ≤ Cmax * s.trace.length := h1
                    _ ≤ Cmax * q := Nat.mul_le_mul_left Cmax h2
                exact_mod_cast this
              · rw [(PMF.apply_eq_zero_iff _ s).mpr hs, zero_mul, zero_mul]
          _ = (Cmax : ℝ≥0∞) * q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRestart1 ====
section

/-! # Family restart, step P5c-1: contacts and markers under family congruence (r3-lean-seedfam)

Family analogues of `Normalized.Restart.{frontierValue_leafCongr, contactAt_leafCongr, markerAt_leafCongr, fill_congr,
GDr_leaf}` (WotsLeafRestart): the honest events of every SOURCE chain are invariant under `FamGame.FamCongr`; a source
chain in the family is a real member (its leaf is in the tree). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart (source_bounds)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {S : FamScheme} {F : FamAddr} {T T' : Answers}
  (hC : FamGame.FamCongr S (sourceMessages T) F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
  (hFtree : F.tree < 2 ^ 40)
include hC hF

include hFtree in
theorem frontierValue_famCongr {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.frontierValue T' (sourceMessages T') b = CanonicalRef.frontierValue T (sourceMessages T) b := by
  rw [FamGame.sourceMessages_congrF hC hF]
  obtain ⟨hbt, hbl⟩ := source_bounds hb
  by_cases hal : FamAlias S F b.key.lay b.key.tree b.key.leaf
  · obtain ⟨l, hla, hleq⟩ := famAlias_member S hal
    have hlt := famLeaf_lt S hF l
    have hk : b.key = famLeaf (S.grp F.lay) F l := by
      have := hla.eq_of_lt hbt (by omega) hFtree (by omega)
      cases hbk : b.key
      rw [hbk] at this
      exact this
    have hreal : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 := hb.1.2
      rw [hk] at h1
      exact h1
    have hbc : b.chain < chainCount F.lay := by have := hb.2; rwa [hal.1] at this
    cases b with
    | mk K c =>
      simp only at hk hbc
      subst hk
      exact hC.front l hreal c hbc
  · unfold CanonicalRef.frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
    rw [FamGame.depth_congrF hC.toFamAgree b, wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hbl hal]
    exact eval_chain_outF hC.toFamAgree hF hbl (by have := Mask.chainCount_le b.key.lay; have := hb.2; omega)
      (fun h => hal h.1) (by have := CanonicalRef.Mask.depth_le_seven T (sourceMessages T) b; omega) _

include hFtree in
theorem contactAt_famCongr (trace : List Entry) {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.ContactAt T' (sourceMessages T') trace b ↔ CanonicalRef.ContactAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.ContactAt
  rw [FamGame.sourceMessages_congrF hC hF]
  rw [FamGame.depth_congrF hC.toFamAgree b]
  have hf := frontierValue_famCongr hC hF hFtree hb
  rw [FamGame.sourceMessages_congrF hC hF] at hf
  rw [hf]

theorem markerAt_famCongr (trace : List Entry) (b : ChainAddr) :
    CanonicalRef.MarkerAt T' (sourceMessages T') trace b ↔ CanonicalRef.MarkerAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.MarkerAt CanonicalRef.referenceInput CanonicalRef.referenceDigits
  rw [FamGame.sourceMessages_congrF hC hF, FamGame.referenceSearch_congrF hC.toFamAgree]

end Congr

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRef ====
section

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
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRestart2 ====
section

/-! # Family restart, step P5c-4: the lower-chain restart, charged to families (r3-lean-seedfam)

Family port of the normalized lower-chain restart of `WotsLeafRestart` (`Normalized.Restart`, `fill_congr` ..
`source_contactAfterStop_charge`, `markerAt_stopL`, `source_markerFirst_at_le`). The restart of the leaf `a.key`
becomes the restart of the family `FamSum.famOf S a.key` (chain coordinates `FamLift.caOf S a`), the per-chain
error `Core.errC` becomes `FamLift.errCF S`, and the stop invariance under `Leaf.Congr` becomes invariance under
`FamGame.FamCongr`. Leaf-independent parts (`Restart.GDr`, `GDr_snd`, `mixLaw_restart`, `restart_real_cost`,
`casD`, `calls_pos_depth`, `count_coupled`, `lt_ite_iff`, `cas_coupled`, `stop_coupled`, `restart_le_R`,
`charge_le_R`, `markerAt_maskAt`, `markerAt_take_exists`) are reused. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestart2
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

/-! ### Lower chains, charged to their family -/

section Restart
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (Restart.maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    ∀ trace, Stop T' trace ↔ Stop T trace)

include ha hgrp in
/-- **Programmed family congruence after the fill** (the family `famOf S a.key`): coefficient vectors with equal
revealed seeds give family-congruent filled tables. -/
theorem fill_congrF (R : Tables (PairedReference.referenceInputs adversary)) (hd1 : 1 ≤ RawPrefix.restDepth a R)
    (p : PDataF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (RawPrefix.restDepth a R))
    (K K' : Fin (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) → Digest)
    (hK : seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K =
        seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K')
    (e : Digest) :
    FamGame.FamCongr S
      (sourceMessages (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) e))
      (FamSum.famOf S a.key)
      (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) e)
      (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K', RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K')) e) := by
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  apply RawFam.famCongr_normalizeF (referenceInputs_subset adversary) S ha.1.1 hFok.leaf
  refine RawFam.famCongr_progF (referenceInputs_subset adversary) S hFok (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) R hd1 p.1.1 p.1.2 K K' (fun c hc hd => ?_) e
  have h := congrFun hK c
  unfold seedsR at h
  have hc' : c ∈ RawFam.revSetF S (FamSum.famOf S a.key) R := by
    unfold RawFam.revSetF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hd⟩
  simp only [if_pos hc'] at h
  exact h

include ha hgrp hStopL in
theorem GDr_famF : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    Restart.GDr adversary q Stop T' = Restart.GDr adversary q Stop T := by
  intro T T' hC
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have hS : Stop T' = Stop T := funext fun trace => propext (hStopL T T' hC trace)
  unfold Restart.GDr
  rw [hS, FamGame.referenceGame_fam hC hFok.tree hFok.leaf adversary q]

include hgrp C hws hb ha hmask hStopL in
/-- **Contact after the stop: reference ≤ mixture + error** (lower chains, family charge). -/
theorem lower_cas_le_mixF :
    Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] + FamLift.errCF S adversary q a := by
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamRef.ref_le_mixF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => Restart.ContactAfterStop Stop s.answers s.trace a) (Restart.casD Stop a)
    (fun R p K K' hK => by
      funext z
      apply propext
      unfold Restart.casD
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨step, hstep, -⟩ := id h3
        have hC := fill_congrF S hgrp ha R (by omega) p K K' hK z.1
        exact ⟨(hStopL _ _ hC _).mpr h1,
          fun h => h2 ((FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree _ ha).mp h), h3⟩
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨step, hstep, -⟩ := id h3
        have hC := fill_congrF S hgrp ha R (by omega) p K K' hK z.1
        exact ⟨(hStopL _ _ hC _).mp h1,
          fun h => h2 ((FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree _ ha).mpr h), h3⟩)
    (fun R z h => by obtain ⟨-, -, step, -⟩ := h; exact step.elim0)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => Restart.cas_coupled q a ha Stop hmask R x res hres) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h

include hgrp C hws hb ha hmask hStopL in
/-- **The stop: mixture ≤ reference + error** (lower chains, family charge). -/
theorem lower_mix_le_stopF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => (∃ k, Stop s.answers (s.trace.take k)) ∧ 1 ≤ Restart.depth s.answers a)
    (fun d R z => 1 ≤ d ∧ Stop (Restart.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by omega)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => by
      have hdep : Restart.depth (answers (referenceInputs_subset adversary)
          (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a = RawPrefix.restDepth a R := by
        unfold Restart.depth
        rw [depth_eq (referenceInputs_subset adversary) _ a ha.1, ← RawPrefix.restDepth_eq, RawPrefix.restDepth_ov]
      have hs := Restart.stop_coupled q a ha Stop hmask R x res hres
      show ((∃ k, Stop _ _) ∧ 1 ≤ Restart.depth (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a) ↔ _
      rw [hdep]
      exact ⟨fun h => ⟨h.2, hs.mp h.1⟩, fun h => ⟨hs.mpr h.2, h.1⟩⟩) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h.trans (add_le_add (probEvent_mono'' fun s hs => hs.1) le_rfl)

include hgrp C hws hb ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the stop** (family charge). -/
theorem lower_contactAfterStop_leF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have hper : ∀ R : Tables (PairedReference.referenceInputs adversary),
      (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    by_cases hd : 1 ≤ RawPrefix.restDepth a R
    · have he : (fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r) = Restart.genStop Stop a R :=
        funext fun r => propext ⟨And.right, fun h => ⟨hd, h⟩⟩
      rw [he]
      exact Restart.restart_le_R q hq a ha.1 Stop R
    · have h0 : Pr[Restart.genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] = 0 := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_eq_zero.mpr fun r => if_neg fun h => hd ?_
        obtain ⟨step, hstep, -⟩ := h.2.2
        omega
      rw [h0, mul_zero, mul_zero]
      exact bot_le
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          (∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + FamLift.errCF S adversary q a)) := by
        gcongr
        exact lower_cas_le_mixF S hgrp C hws hb q ha Stop hmask hStopL
    _ = ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ((1 - (q : ENNReal) / 2 ^ 128) *
          ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)])) +
          (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * (((2 * q : ℕ) : ENNReal) *
          Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)]) + 1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (hper R)) (mul_le_mul' hx le_rfl)
    _ = ((2 * q : ℕ) : ENNReal) * ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + (2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a := by
        rw [one_mul, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ((2 * q : ℕ) : ENNReal) * (Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
          FamLift.errCF S adversary q a) + (2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a := by
        gcongr
        exact lower_mix_le_stopF S hgrp C hws hb q ha Stop hmask hStopL
    _ = _ := by ring

/-! ### The charge, by layers -/

include hgrp C hws hb ha hmask hStopL in
theorem lower_mix_layer_leF (k : ℕ) :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
          PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k'))
    (fun d R z => k < 2 * calls (PrefixGame.PrefixQuery a d) z.2.1.2.2 ∧
      Stop (Restart.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hk, h1⟩
        have hd := Restart.calls_pos_depth (a := a)
          (by omega : 0 < calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hk, h1⟩
        have hd := Restart.calls_pos_depth (a := a)
          (by omega : 0 < calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by
      have := h.1
      rw [calls_prefixQuery_zero] at this
      omega)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => by
      have hc := Restart.count_coupled q ha Stop R x res hres
      have hs := Restart.stop_coupled q a ha Stop hmask R x res hres
      show (k < 2 * prefixCount a (mkSample (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) ∧ _) ↔ _
      rw [hc]
      exact and_congr Iff.rfl hs) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h

include hgrp C hws hb ha hmask hStopL in
/-- **The charge: mixture ≤ reference + 2q · error** (lower chains, family charge). -/
theorem lower_mix_charge_leF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none) r * Restart.genCharge Stop a R r ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a := by
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
        (fun _ _ => none) r * Restart.genCharge Stop a R r =
      ∑ k ∈ Finset.range (2 * q), Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    have h := expectation_layers (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none))
      (fun r => if Restart.genStop Stop a R r then 2 * seedCost a R r.2.1.2 else 0) (2 * q) (fun r hr => by
        have := Restart.restart_real_cost q a Stop R r hr
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun r => ?_
    unfold Restart.genCharge
    congr 1
    show _ = (((if Restart.stopAt Stop a R r.1 r.2.1.1 then 2 * seedCost a R r.2.1.2 else 0 : ℕ)) : ENNReal)
    split_ifs <;> simp
  have href : ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * q), Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
        PairedReference.referenceExperiment adversary q] := by
    have h := expectation_layers (PairedReference.referenceExperiment adversary q)
      (fun s => if ∃ k, Stop s.answers (s.trace.take k) then 2 * prefixCount a s else 0) (2 * q) (fun s hs => by
        have := (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs)
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun s => ?_
    congr 1
    split_ifs <;> simp
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑ k ∈ Finset.range (2 * q),
        Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)]
      = ∑ k ∈ Finset.range (2 * q), ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range (2 * q),
          (Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
            PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun k _ => lower_mix_layer_leF S hgrp C hws hb q ha Stop hmask hStopL k
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

include hgrp C hws hb ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the prefix charge** (family charge). -/
theorem lower_contactAfterStop_chargeF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          (∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + FamLift.errCF S adversary q a)) := by
        gcongr
        exact lower_cas_le_mixF S hgrp C hws hb q ha Stop hmask hStopL
    _ = ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ((1 - (q : ENNReal) / 2 ^ 128) *
          ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)])) +
          (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none) r * Restart.genCharge Stop a R r +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (Restart.charge_le_R q hq a ha.1 Stop R))
          (mul_le_mul' hx le_rfl)
    _ ≤ (∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
          (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
          ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a) +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        gcongr
        exact lower_mix_charge_leF S hgrp C hws hb q ha Stop hmask hStopL
    _ = _ := by ring
end Restart

/-! ### All source chains -/

section Source
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (Restart.maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    ∀ trace, Stop T' trace ↔ Stop T trace)
include hgrp C hws hb ha hmask hStopL

/-- **Source chains: contact after the stop, against the stop** (family charge). -/
theorem source_contactAfterStop_leF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a :=
  lower_contactAfterStop_leF S hgrp C hws hb q ha Stop hmask hStopL hq

/-- **Source chains: contact after the stop, against the prefix charge** (family charge). -/
theorem source_contactAfterStop_chargeF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a :=
  lower_contactAfterStop_chargeF S hgrp C hws hb q ha Stop hmask hStopL hq
end Source

/-! ### Markers -/

/-- Markers are invariant under the family congruence of a source chain's family. -/
theorem markerAt_stopLF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {a : ChainAddr}
    (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → ∀ trace,
      Restart.MarkerAt T' trace a ↔ Restart.MarkerAt T trace a :=
  fun _ _ hC trace => FamRestartN.markerAt_famCongr hC (FamLift.famOk_of_source S hgrp ha.1).leaf trace a

/-- **Markers first, per source chain** (family charge). -/
theorem source_markerFirst_at_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => Restart.MarkerAt s.answers s.trace a |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have h := source_contactAfterStop_leF (adversary := adversary) S hgrp C hws hb q ha
    (fun T trace => Restart.MarkerAt T trace a)
    (fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2)
    (markerAt_stopLF S hgrp ha) hq
  simpa only [Restart.markerAt_take_exists] using h

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestart2
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamTot ====
section

/-! # Family restart, step P6a: the total family seed-test error (r3-lean-seedfam)

`errTotF S adversary q := ∑ over source chains of errCF` (family analogue of `Contacts.errTot`), bounded by the charge
`Cmax` (`errTotF_le`), in reals `errTotF ≤ 2·Cmax·y³/(1-y)` with the one-sided side-channel constant
(`errTotF_toReal`), hence the small-route seed-error hypothesis for `Cmax ≤ 305` (`seedErrorBoundF`; v6: `Cmax = 301`,
`errTotF ≤ 602 y³/(1-y)`). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Total family seed-test error over the source chains. -/
noncomputable def errTotF (S : FamScheme) (adversary : Final.Paired.AdversaryP) (q : Nat) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamLift.errCF S adversary q a

/-- Scheme-wide hypotheses of the family restart. -/
structure FamHyps (S : FamScheme) (Cmax : Nat) where
  caps : FamCaps S
  grp_le : ∀ lay, S.grp lay ≤ 2 ^ 20
  charge : ∀ lay, S.grp lay * chainCount lay ≤ Cmax
  width : ∀ lay, chainCount lay ≤ S.stride lay
  points : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024

theorem errTotF_le {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    errTotF S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) :=
  FamLift.errC_sum_leF S H.grp_le Cmax H.charge H.caps H.width H.points q
    (CanonicalWeighted.query_card_lt_one q hq)

theorem errTotF_toReal {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) :
    (errTotF S adversary q).toReal ≤ 2 * Cmax * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128) := by
  have h0 := CanonicalWeighted.errConst_nonneg q hq
  have hle := errTotF_le H adversary q hq
  have h := ENNReal.toReal_mono (by finiteness) hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_natCast] at h
  have hd : 0 < 1 - (q : ℝ) / 2 ^ 128 := by
    have hq' : (q : ℝ) < 2 ^ 128 := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one (by positivity)).2 hq')
  have hn : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hk := CanonicalWeighted.kconst_le_sq q
  have hm : 0 ≤ (Cmax : ℝ) * (q : ℝ) := mul_nonneg (Nat.cast_nonneg _) hn
  have hc : 0 ≤ 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) 128)) 3)
  unfold Core.errConst at h
  have hcard : (Fintype.card Digest : ℝ) = 2 ^ 128 := by rw [Fintype.card_bitVec]; norm_num
  rw [hcard] at h
  have hrat : ((2 : ℝ) ^ 128)⁻¹ * (q : ℝ) = (q : ℝ) / 2 ^ 128 := by ring
  rw [hrat] at h
  calc (errTotF S adversary q).toReal
      ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) / (1 - (q : ℝ) / 2 ^ 128)) *
          ((Cmax : ℝ) * q) := h
    _ ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ((q : ℝ) ^ 2) / (1 - (q : ℝ) / 2 ^ 128)) * ((Cmax : ℝ) * q) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hc) hd.le) hm
    _ = _ := by ring

/-- The family seed-error hypothesis of the small route (`errTotF ≤ (733/1000) y²` on `y ≤ 3/2500`) for `Cmax ≤ 305`. -/
theorem seedErrorBoundF {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF S adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  (errTotF_toReal H adversary q hq).trans
    (grouped_seed_error Cmax _ (Nat.cast_nonneg _) (by exact_mod_cast hC) (by positivity) hy)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamContacts ====
section

/-! # Family restart, step P6a: the normalized contacts layer charged to family errors (r3-lean-seedfam)

Family port of the normalized `Contacts` (`twoEdgeAt_cost_le`, `contactAt_cost_le`, `reference_twoEdge_le`,
`reference_contacts_cost_le`): the per-chain error `Core.errC` becomes `FamLift.errCF S`, the total `Contacts.errTot`
becomes `FamTot.errTotF S` (summed over `sourceChains`; it agrees with the sum over `Contacts.sourceChains7` since
`errCF` vanishes off `SourceChain7`, `errTot7F_eq`). The leaf-independent parts (`twoEdge_mix_R`, `contact_mix_R`,
`twoEdgeAt_iff_sample`, `contactAt_iff_sample`, `prefixCount_sum_le`, `expected_contactCount`) are reused.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun
  idealRun lazyRun TwoEdgeEvent Contact)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

/-- Family total over `sourceChains7` (the index set of the leaf consumers). -/
noncomputable def errTot7F (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ℝ≥0∞ :=
  ∑ a ∈ Normalized.Contacts.sourceChains7, FamLift.errCF S adversary q a

/-- `errCF` vanishes off `SourceChain7`, so the totals over `sourceChains7` and `sourceChains` agree. -/
theorem errTot7F_eq (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    errTot7F S adversary q = FamTot.errTotF S adversary q := by
  unfold errTot7F FamTot.errTotF Normalized.Contacts.sourceChains7
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : WotsExtract.SourceChain7 a
  · rw [if_pos h]
  · rw [if_neg h, FamLift.errCF, dif_neg h]

theorem errTot7F_le {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    errTot7F S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  rw [errTot7F_eq]
  exact FamTot.errTotF_le H adversary q hq

section PerChain
variable {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
include H

/-- Per chain, two-edge cost with the family seed-test error. -/
theorem twoEdgeAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.TwoEdge (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_twoEdge] at hv
  rw [Normalized.Contacts.twoEdgeAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ twoEdgeRate q * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.twoEdge_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ twoEdgeRate q * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- Per chain, contact cost with the family seed-test error. -/
theorem contactAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.Contact (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_contact] at hv
  rw [Normalized.Contacts.contactAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => Contact r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128) * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.contact_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128) * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- **Two-edge bound, family charge.** -/
theorem reference_twoEdge_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      (twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + twoEdgeRate q * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [← errTot7F_eq]
  have hunion : Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum Normalized.Contacts.sourceChains7
      (PairedReference.referenceExperiment adversary q)
      (fun a s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mp ha, h⟩
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
          CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] * (1 - (q : ENNReal) / 2 ^ 128)
      ≤ (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128) :=
        mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, (twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => twoEdgeAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s

/-- **Expected contact count bound, family charge.** -/
theorem reference_contacts_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) ≤
      ((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [Normalized.Contacts.expected_contactCount, ← errTot7F_eq]
  calc (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, ((2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s
end PerChain

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamV6 ====
section

/-! # The v6 seed families as an interface (r3-lean-seedfam; for the scheme / top-bytes porters)

The family restart (WotsFam*.lean) is proved for any `FamScheme S` with reveal caps `FamCaps S`. For the v6 images
(opus-crumbs img-v6, `scripts/check_seeds_v6.py`) the scheme side must discharge exactly two statements:

* `V6SeedSpec` — the WOTS seeds are family evaluations:
  - TOP (layer 0): 4-leaf families, 39 coefficients at ordinals `39·(leaf/4) + i` (carry-packed halves of
    `lowerSeedPair 0 tree`), points `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1 ≤ 256`;
  - LOWER: 7-leaf families, ordinals `38·(leaf/7) + i`, `5·r + 3` coefficients (`r = 7`, or the remainder `2` for L1 /
    `1` for L2, L3 in the last family), points `(leaf % 7)·43 + j + 1 ≤ 301`;
* `V6ZeroSpec` — every leaf's reference digits have at most 9 (top) / 5 (lower) zeros (`producerZeroCap`).

From them, `v6Scheme` / `v6Caps` are the `FamScheme` / `FamCaps` the port consumes. Facts used by the restart and the
closing are proved here: points distinct and `< 1024` (top `≤ 256`), per-test charge `4·54 = 216` (top) and
`7·43 = 301` (lower) `≤ 305` (the live closing bound, `FinalG`), degree `38` top (`39` coefficients), and the reveal budget
`9·4 + 3 = 39` (top), `5·r + 3` (lower).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.Arith.SideChannel.GroupedFamily (gptS gptS_injective gptS_lt)
attribute [local instance] Classical.propDecidable

/-- Leaves per family. -/
def grp (lay : Layer) : Nat := if lay = 0 then 4 else 7
/-- Ordinal base per family. -/
def cnt (lay : Layer) : Nat := if lay = 0 then 39 else 38
/-- Point stride. -/
def stride (lay : Layer) : Nat := if lay = 0 then 64 else 43
/-- Coefficients of family `f` (the last lower family is short). -/
def size (lay : Layer) (f : Nat) : Nat := if lay = 0 then 39 else 5 * min 7 (2 ^ height lay - 7 * f) + 3
/-- Evaluation point: chains below `chainCount` at `(leaf % grp)·stride + i + 1`; the unused address slots
`chainCount ≤ i < 58` in a separate junk region above `grp·stride` (lower `302 + l·15 + (i − 43)`), so all points of a
family are distinct and `< 1024`. The images never compute junk seeds. -/
def point (lay : Layer) (leaf i : Nat) : Nat :=
  if i < chainCount lay then (leaf % grp lay) * stride lay + i + 1
  else grp lay * stride lay + (leaf % grp lay) * (58 - chainCount lay) + (i - chainCount lay) + 1
/-- Zero-digit cap per leaf. -/
def zcap (lay : Layer) : Nat := if lay = 0 then 7 else 5

/-- **Scheme obligation 1**: WOTS seeds are v6 family evaluations. -/
def V6SeedSpec : Prop :=
  ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- **Scheme obligation 2**: per-leaf zero-digit caps of the reference digits. -/
def V6ZeroSpec : Prop :=
  ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay

theorem size_le (lay : Layer) (f : Nat) : size lay f ≤ cnt lay := by
  unfold size cnt
  split_ifs
  · exact le_rfl
  · have : min 7 (2 ^ height lay - 7 * f) ≤ 7 := min_le_left _ _
    omega

/-- The v6 family scheme (given the seed obligation). -/
def v6Scheme (h : V6SeedSpec) : FamScheme where
  grp := grp
  cnt := cnt
  size := size
  stride := stride
  point := point
  grp_pos lay := by unfold grp; split_ifs <;> decide
  cnt_le lay := by unfold cnt; split_ifs <;> decide
  size_le := size_le
  point_eq lay leaf i hi := by unfold point; rw [if_pos hi]
  seed := h

/-- The v6 reveal caps (given the zero obligation). -/
def v6Caps (hs : V6SeedSpec) (hz : V6ZeroSpec) : FamCaps (v6Scheme hs) where
  zcap := zcap
  zeros_le R L := hz R L
  size_ge lay f := by
    show zcap lay * min (grp lay) (2 ^ height lay - grp lay * f) + 3 ≤ size lay f
    unfold zcap grp size
    split_ifs
    · have : min 4 (2 ^ height lay - 4 * f) ≤ 4 := min_le_left _ _
      omega
    · exact le_rfl

/-! ### Facts used by the restart and the closing -/

/-- Points of the family chains `(l, c)` are `gptS (stride lay) (l, c)`; top points stay `≤ 256`. -/
theorem top_point_le (l : Fin 4) (c : Fin 54) : gptS 64 (l, c) ≤ 256 := by
  unfold gptS; have := l.isLt; have := c.isLt; omega

theorem top_points_injective : Function.Injective (gptS 64 (g := 4) (w := 54)) := gptS_injective (by decide)
theorem lower_points_injective : Function.Injective (gptS 43 (g := 7) (w := 43)) := gptS_injective le_rfl
theorem top_points_lt (c : Fin 4 × Fin 54) : gptS 64 c < 1024 := gptS_lt (by decide) c
theorem lower_points_lt (c : Fin 7 × Fin 43) : gptS 43 c < 1024 := gptS_lt (by decide) c

/-- `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1`. -/
theorem top_point_bits (leaf j : Nat) : ((leaf &&& 3) <<< 6) + j + 1 = (leaf % 4) * 64 + j + 1 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod leaf 2]

/-- Per-test charges (chains per family) against the live closing bound `305` (`FinalG.seedErrorBound_of_charge`). -/
theorem charges : 4 * 54 = 216 ∧ 216 ≤ 305 ∧ 7 * 43 = 301 ∧ 301 ≤ 305 := by decide

/-- Top: 39 coefficients (degree 38) and the reveal budget `9·4 + 3 = 39`. -/
theorem top_budget : cnt 0 = 39 ∧ size 0 0 = 39 ∧ 9 * 4 + 3 = 39 := by decide

/-- Reveal bound of a top family: at most 9 revealed seeds per leaf leave 3 free degrees. -/
theorem top_revealed_card_le (Rev : Finset (Fin 4 × Fin 54)) (h : ∀ l : Fin 4, (Rev.filter fun c => c.1 = l).card ≤ 9) :
    Rev.card + 3 ≤ 39 := by
  have := ClaudeWCT.Arith.SideChannel.GroupedFamily.revealed_card_leW (g := 4) (w := 54) (r := 9) Rev h
  omega

end ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamHyps ====
section

/-! # Family restart hypotheses for today's scheme and for v6 (r3-lean-seedfam)

`layoutHyps : FamHyps layoutScheme 301` (the scheme of the `Correctness` layout) and
`v6Hyps hs hz : FamHyps (v6Scheme hs) 301` (v6: lower 7-leaf, top 4-leaf families); with `seedErrorBoundF` the v6 seed
error is `≤ 602 y³/(1-y) ≤ (733/1000) y²` on the live small window. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3.Security.Wots.FamRestart

theorem chainCount_cases (lay : Layer) : chainCount lay = if lay = 0 then 51 else 43 := by
  fin_cases lay <;> rfl

/-- The scheme of the `Correctness` layout (v6 lower 7-leaf families, top per-leaf until the top port): charge
`max(1 · 51, 7 · 43) = 301`. -/
def layoutHyps : FamHyps layoutScheme 301 where
  caps := layoutCaps
  grp_le lay := by show WCT9.famGrp lay ≤ 2 ^ 20; unfold WCT9.famGrp; split_ifs <;> norm_num
  charge lay := by
    show WCT9.famGrp lay * chainCount lay ≤ 301
    unfold WCT9.famGrp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := WCT9.famStride_ge lay
  points lay := by
    show (WCT9.famGrp lay - 1) * WCT9.famStride lay + chainCount lay < 1024
    unfold WCT9.famGrp WCT9.famStride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6: lower 7-leaf (stride 43), top 4-leaf (stride 64) families, charge `max(4·51, 7·43) = 301`. -/
def v6Hyps (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) : FamHyps (V6.v6Scheme hs) 301 where
  caps := V6.v6Caps hs hz
  grp_le lay := by show V6.grp lay ≤ 2 ^ 20; unfold V6.grp; split_ifs <;> norm_num
  charge lay := by
    show V6.grp lay * chainCount lay ≤ 301
    unfold V6.grp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := by
    show chainCount lay ≤ V6.stride lay
    unfold V6.stride; rw [chainCount_cases]; split_ifs <;> decide
  points lay := by
    show (V6.grp lay - 1) * V6.stride lay + chainCount lay < 1024
    unfold V6.grp V6.stride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6 small-route seed error: `errTotF ≤ (733/1000) y²` on `y ≤ 3/2500` (via `602 y³/(1-y)`). -/
theorem v6_seedError (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF (V6.v6Scheme hs) adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  seedErrorBoundF (v6Hyps hs hz) (by norm_num) adversary q hq hy

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_FinalFam ====
section

/-! # The live security theorem through the family seed-error charge (r3-lean-seedfam, P6b)

Copies of the Final.lean blocks that charge the WOTS seed test per chain (`Core.errC`, `Contacts.errTot`, the
per-chain restart `Restart.source_contactAfterStop_charge` / `source_markerFirst_at_le`), suffixed `Fam`, with the
family charge `FamLift.errCF S` / `FamTot.errTotF S` for any `FamScheme S` with `H : FamTot.FamHyps S Cmax`
(`FamRestart2.*F`, `FamContacts.*F`). The closing is FinalG's (`799/1000`, `grouped_middle_closing`) with the seed
error `FamTot.seedErrorBoundF H hC` (`Cmax ≤ 305`); the large route is `LargeCoupling.Paired.large_bound`.
`t3_securityP_fam S Cmax H hC : SecurityP`; `t3_securityP_layout` instantiates the scheme's layout (v6). -/

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
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL

/-- Other contacts are invariant under the family congruence of a source chain's family. -/
theorem otherContact_stopLFam (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → ∀ trace,
      OtherContact a T' trace ↔ OtherContact a T trace := by
  intro T T' hC trace
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  unfold OtherContact
  exact exists_congr fun b => and_congr_right fun hb => and_congr_right fun _ =>
    FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree trace hb

theorem reference_twoContacts_le_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (((2 * q : ℕ) : ENNReal) *
          (((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) +
              (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
            (1 - (q : ENNReal) / 2 ^ 128)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum Contacts.sourceChains7 (PairedReference.referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · exact ⟨b, (Contacts.mem_sourceChains7 b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ Contacts.sourceChains7) =>
    FamRestart2.source_contactAfterStop_chargeF (adversary := adversary) S H.grp_le H.caps H.width H.points q
      ((Contacts.mem_sourceChains7 a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((Contacts.mem_sourceChains7 a).mp ha))
      (otherContact_stopLFam S H.grp_le a ((Contacts.mem_sourceChains7 a).mp ha)) hq
  have halloc : ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
        calc ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := Contacts.prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := Core.ref_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s ≤ 2 * q)
      calc PairedReference.referenceExperiment adversary q s * ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ PairedReference.referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | PairedReference.referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Contacts.sourceChains7, (∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ = ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← FamContacts.errTot7F_eq]
        rfl
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := add_le_add halloc le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq)) le_rfl

theorem reference_twoContacts_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * FamTot.errTotF S adversary q := by
  refine (reference_twoContacts_le_rawFam S H adversary q hq).trans (le_of_eq ?_)
  rw [ENNReal.add_div, big_div_mul]
  set E := ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)
  set T := FamTot.errTotF S adversary q
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring

set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_leFam (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) ≤ FamTot.errTotF S adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, FamLift.errCF S adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · rw [FamLift.errCF, dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [← FamContacts.errTot7F_eq, h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)

theorem reference_markerFirst_sum_le_ofFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((5022 / 2 ^ 128 : ENNReal) * (∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal))) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * FamTot.errTotF S adversary q := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
          FamLift.errCF S adversary q (Enc.chainAt p) := by
    intro p
    by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
    · simp only [hs, true_and]
      have hC := FamRestart2.source_markerFirst_at_leF (adversary := adversary) S H.grp_le H.caps H.width H.points
        q hq (Enc.chainAt p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (Enc.chainAt p)) s.answers s.trace
        (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set EC := FamLift.errCF S adversary q (Enc.chainAt p)
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs, ← big_div_mul, ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * EC := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainAt ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            FamLift.errCF S adversary q (Enc.chainAt p)) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
              PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hMS) (mul_le_mul' le_rfl (sum_errC_chainOf_leFam S adversary q))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_primitive_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
 (w v : ENNReal) (hwv : w+v=1) :
 Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
 Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] + (2^142:ENNReal)⁻¹ +
 prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
 encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
 (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
 errCoeff q w v*FamTot.errTotF S adversary q := by
 -- top-nonce layer (r3-lean-nonsec): the structural bound carries Pr[CapFail] ≤ (2^142)⁻¹; fold it into the
 -- other-mass argument of weighted_union_le as (2^128)⁻¹ * (EO + 2^128 * (2^142)⁻¹).
 have hcancel : ∀ x : ENNReal, (2^128:ENNReal)⁻¹ * (x + 2^128 * (2^142:ENNReal)⁻¹) =
     (2^128:ENNReal)⁻¹ * x + (2^142:ENNReal)⁻¹ := fun x => by
   rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
 have key : Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
     Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] +
     prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
     encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
     (2^128:ENNReal)⁻¹*((∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) + 2^128 * (2^142:ENNReal)⁻¹) +
     errCoeff q w v*FamTot.errTotF S adversary q := by
  refine weighted_union_le (PairedReference.referenceExperiment adversary q)
    Combined ReferenceFailed EncodingMatch Structural TwoEdge TwoContacts MarkerFirstEvent ContactFirstEvent
    q w v _ _ _ _ hwv combined_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact CanonicalRef.reference_encodingMatch_le adversary q
  · rw [hcancel]
    exact structural_reference_le adversary q (PairedReference.reference_structural_in_le adversary q)
  · exact FamContacts.reference_twoEdge_leF H adversary q hq
  · exact Restart.reference_twoContacts_leFam S H adversary q hq
  · exact Restart.reference_markerFirst_sum_le_ofFam S H adversary q hq (CanonicalRef.reference_marker_sum_le adversary q)
  · exact (CanonicalRef.Contact93.reference_contactFirst_le adversary q).trans
      (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq))
  · exact (nonstructural_reference_le adversary q).trans (FamContacts.reference_contacts_cost_leF H adversary q hq)
 refine key.trans (le_of_eq ?_)
 rw [hcancel]
 ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem errTotF_ne_topFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128) :
    FamTot.errTotF S adversary q≠⊤ :=
  ne_top_of_le_ne_top (by finiteness) (FamTot.errTotF_le H adversary q hq)

theorem primitive_real_of_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q<2^128)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤)
    (eventProbability otherMass : ENNReal) (ho:otherMass≠⊤)
    (hraw : eventProbability ≤ 1/(2:ENNReal)^139+(2^142:ENNReal)⁻¹+
      prefixCoeff q w v/2^128*prefixMass adversary q+
      encodingCoeff q w v/2^128*encodingMass adversary q+
      (2^128:ENNReal)⁻¹*otherMass+errCoeff q w v*FamTot.errTotF S adversary q)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    eventProbability.toReal ≤
      theta*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
      otherMass.toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc1:=prefixCoeff_ne_top q hq w v hw hv
  have hc2:=encodingCoeff_ne_top q hq w v hw
  have hc3:=errCoeff_ne_top q hq w v hw hv
  have hfin:=errTotF_ne_topFam S H adversary q hq
  have h:=ENNReal.toReal_mono (by finiteness) hraw
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_inv,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    prefixCoeff_toReal q hq w v hw hv hwv,encodingCoeff_toReal q hq w v hw,
    errCoeff_toReal q hq w v hw hv hwv] at h
  have he0 : 0≤canonicalError ((q:ℝ)/2^128) w.toReal := by
    rw [←errCoeff_toReal q hq w v hw hv hwv]
    exact ENNReal.toReal_nonneg
  have hseed := FamTot.seedErrorBoundF H hC adversary q hq hy
  have herr:=grouped_weighted_error ((q:ℝ)/2^128) (FamTot.errTotF S adversary q).toReal
    (canonicalError ((q:ℝ)/2^128) w.toReal) he0 herror hseed
  have hp' := mul_le_mul_of_nonneg_right hprefix (show 0≤(prefixMass adversary q).toReal/2^128 by positivity)
  have he' := mul_le_mul_of_nonneg_right hencoding (show 0≤(encodingMass adversary q).toReal/2^128 by positivity)
  simp only [div_eq_mul_inv] at h hp' he' herr ⊢
  nlinarith

theorem primitive_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      theta*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hqN : q<2^128 := by omega
  have hf := PairedSmallT.masses_finite adversary q hq
  have hraw := (reference_primitive_leFam S H adversary q hqN w v hwv).trans
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hfailed le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
  exact primitive_real_of_rawFam S H hC adversary q hqN hy w v hw hv hwv hf.1 hf.2.1
    _ (PairedSmallT.otherMass adversary q) hf.2.2.1 hraw theta hprefix hencoding herror

theorem primitive_middle_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤149/125000)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99843/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := middle_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq (hy.trans (by norm_num)) (10297/500000) (489703/500000)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

theorem primitive_tiny_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := tiny_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq (hy.trans (by norm_num)) (3/100) (97/100)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

theorem primitive_middle_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤149/125000) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99843/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_middle_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)

theorem primitive_tiny_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_tiny_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow:1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh:(q:ℝ)/2^128≤149/125000) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply middle_clean_closingG adversary q hq hlow hhigh (1174/1000000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_middle_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (99843/50000) (1174/1000000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤99843/50000))
    excess_middle_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem tiny_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤1/2^28) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply tiny_clean_closingG adversary q hq hpositive hhigh (18/5000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_tiny_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (249/125) (18/5000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤249/125))
    excess_tiny_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem small_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤149/125000) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  by_cases ht:(q:ℝ)/2^128≤1/2^28
  · exact tiny_boundFam S H hC adversary q hq hpositive ht
  · exact middle_boundFam S H hC adversary q hq (le_of_lt (lt_of_not_ge ht)) hhigh

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme layoutScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- **The live security theorem through the family seed-error charge**: any family scheme with the family-restart
hypotheses and per-test charge `Cmax ≤ 305`. -/
theorem t3_securityP_fam (S : FamScheme) (Cmax : Nat)
    (H : ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305) :
    ClaudeWCT.W9.T3M.Final.Paired.SecurityP := by
  apply PairedOuter.PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  by_cases hsmall : (q:ℝ)/2^128 ≤ 149/125000
  · exact Wots.PairedSmallT.small_boundFam S H hC adversary q hq hpositive hsmall
  · exact LargeCoupling.Paired.large_bound adversary q hq (le_of_not_ge hsmall)

/-- **The live security theorem of the v6 scheme** (the `Correctness` layout: lower 7-leaf families, charge 301). -/
theorem t3_securityP_layout : ClaudeWCT.W9.T3M.Final.Paired.SecurityP :=
  t3_securityP_fam layoutScheme 301 ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.layoutHyps
    (by norm_num)

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsLayout ====
section

section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
/-! ### T51 top layer (verify image T51_T152_g791_c0hi, generator t51/verify/py/gen_t51v.py --c0hi)
Groups `q` in dispatch (= chain) order:
* `q < 9`: the radix-6 triples g0..g8 (chains `3q .. 3q+2`, largest digit 5, 216 ranks); cells `cell6`, shared
  bodies `body6` (chain-A rung ladder, chain B, chain C, next dispatch);
* `9 ≤ q < 16`: #938's radix-5 groups q9..q15 (chains 27..47, largest digit 4, 125 ranks), #938's code with the
  leaf-slot immediates moved by `-16` (endpad leaf); q15's last dispatch is #938's dispatch into group 8;
* `q = 16`: the radix-7 pair (chains 48 = A, 49 = B, largest digit 6, 49 ranks `k = d48 + 7 d49`, no chain C);
  cells in #938's q8 column `1024 (125 - k) + 676`, bodies `body7Tab` (ladder, chain 49, checksum dispatch);
* `q = 17`: the radix-6 checksum chain 50 (largest digit 5), arms `ckArm d` (d = 0..5). -/
/-- Largest digit of the chains of top group `q` (T51): r6 groups 5, #938's r5 groups 4, the r7 pair 6, the
checksum chain (group 17) 5. -/
def mx (q : Nat) : Nat := if q<9 then 5 else if q<16 then 4 else if q=16 then 6 else 5
/-- Top chain `i`'s block in the top chain area (even pairing, charge 86: pair `p = (2p, 2p+1)` at `104 (26 - p)`,
G chain at `+16`, F chain at `+40`; `= W9.T3M.chainSlot 0 i`). -/
def topSlot (i : Nat) : Nat := 104*(26-i/2)+16+24*(i%2)
/-- Top chain format (T51): chain `i` is G (value first) iff it is even and `i ≤ 50` (`= T3.topIsG`). -/
def topG (i : Nat) : Bool := decide (i%2=0 ∧ i ≤ 50)
def off (i : Nat) : Word := BitVec.ofNat 64 (topSlot i)-BitVec.ofNat 64 1664
/-- T51 endpad top leaf: `end_0` at 25216 (tp + 512), the tweak at 25232, `end_i` at `25232 + 16 i` (i ≥ 1). -/
def slot (i : Nat) : Nat := if i=0 then 25216 else 25232+16*i
/-- Target of chain `i`'s terminal hash: chain 0 (c0hi) writes its last 32-byte answer at `slot 0 - 16 = 25200`
(the HIGH half lands on `end_0`); every other chain at its slot. -/
def termSlot (i : Nat) : Nat := if i=0 then 25200 else slot i
def slotOffset (a : Nat) : Nat := a-24704
def rungR (d : Nat) (sl : Option Nat) (p : Nat) : Result :=
  T3M.rungRB d (sl.map slotOffset) p
def copyN (rb : Reg) (o : Word) (sl tgt : Nat) (g : Bool := false) : Result :=
  T3M.copyNB rb o (slotOffset sl) tgt g
def copyFH (rb : Reg) (o : Word) (sl p : Nat) (g : Bool := false) : Result :=
  T3M.copyFHB rb o (slotOffset sl) p g
def headRH (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) (g : Bool := false) : Result :=
  T3M.headRHB rb o d (sl.map slotOffset) p i g
def emptyR (p : Nat) : Result := ⟨SymState.init,.c (pcOf p),.fuel,0,0⟩
/-- T51 top target (the checksum digit is `topT - sum`). -/
def topT : Nat := 152
/-- r6 group `g` dispatches through table B (`s2 - 256 raw`: g1, g2, g3, g8) or table A (`256 raw + s2`: g4..g7). -/
def r6B (g : Nat) : Bool := decide (g<4 ∨ g=8)
def r6Off (g : Nat) : Nat := 40+6*(g%4)
/-- The 8-bit field value of rank `k` in r6 group `g` (g0: raw = rank + 40). -/
def rawOf6 (g k : Nat) : Nat := if g=0 then k+40 else k
/-- Cell of r6 group `g` for field value `raw`: g0 base-free column `512 (raw - 3) + 326`, table B rows
`3327 - raw`, table A rows `3328 + raw` (offset `r6Off g` inside the 64-word rows). -/
def cell6 (g raw : Nat) : Nat :=
  if g=0 then 512*(raw-3)+326 else if r6B g then 64*(3327-raw)+r6Off g else 64*(3328+raw)+r6Off g
def body6Tab : List Nat := [185001,185713,129188,98758,127558,72868,190819,185085,101958,77988,51748,26182,185855,102854,118948,76964,26405,21062,102982,123044,122020,26277,21285,805,128454,51782,26917,21797,14918,10788,126243,26788,21157,933,10822,1105,186537,189172,187130,186439,130112,51877,190320,188404,188532,128582,27044,46628,189804,190279,185216,52388,21668,25381,191093,185673,52644,46662,967,16165,130212,27078,21924,1317,10917,11557,52678,46757,25893,16677,13860,5925,189353,187049,191988,191722,132863,72357,187305,189097,187634,187719,52005,47268,191846,188656,188926,72485,21958,41508,191785,127140,72997,47524,1351,20261,132902,52517,25124,15908,11428,13894,76453,47558,41542,20773,13989,6437,191913,187500,189038,184942,132941,76581,188270,185129,186986,184791,67108,50724,185289,186341,187206,77093,25158,41637,190945,188585,92965,50758,15942,24357,132980,67142,25253,16037,11684,14500,93477,50853,42148,24869,14756,11084,185769,189225,186727,186213,133019,97061,190633,188073,188005,189947,67237,51364,188841,185960,190577,97573,25764,42404,186086,117284,101157,51620,16548,40484,133058,67748,26020,16804,11718,14790,101669,51654,42438,40518,21324,11596,186481,191401,185577,190426,133097,113188,191587,189993,187877,118180,68004,67365,130300,72228,121380,113222,26054,45604,73124,122276,113828,67877,16838,40613,133136,68038,50981,20004,15141,21836,114084,71461,45638,41124,22052,12069,189865,187247,190889,76324,133175,114118,188773,190761,77220,184832,71204,71973,185449,92708,93348,117319,51493,45733,93604,93383,117541,72265,20038,41380,133214,71238,66084,20133,15653,22086,118053,73161,46244,41414,22181,22821,189545,189609,191529,96804,184867,118215,190121,186862,97700,97444,71333,75557,191453,100900,97479,121415,66118,46500,101796,101540,121637,76069,20644,44580,186584,71844,66213,20900,19237,22692,122149,76361,46534,44614,22948,23372,191017,187759,103588,123334,122311,72100,188457,124068,123462,188231,77257,66724,128164,124358,188329,72134,49700,20934,126534,188999,75300,66980,44709,15013,125476,87588,49734,45220,22982,9764,75334,67014,24100,15524,9798,4644]
def body7Tab : List Nat := [26148,21028,711,14884,11045,8740,268]
def body6 (g dB dC : Nat) : Nat := body6Tab.getD (36*g+6*dB+dC) 0
def baseTab : List Nat := [184791,130112,98124,184908,129996,130212,185013,185050,133292,186153,185147,122700,711,186183,77482,185310,133324,186281,102698,83032,133356,186311,77610,84056,268,93382,132863,185676,127564,133388,185779,185818,122828,133420,186409,98252,123212,805,186665,77738,127692,133452,186921,102826,103513,133484,187100,77910,104537,1105,97478,186442,98636,127820,186552,186584,98764,123340,186695,187433,101964,186794,186829,187689,78122,127948,186954,187817,102954,108633,187068,187847,78250,118314,1804,187206,132902,102092,187323,187357,132941,102220,187465,133516,187945,187562,187599,933,187975,97834,187725,133548,188128,103082,118442,133580,188201,97962,118570,2129,98504,132980,188091,128332,133612,133019,188233,123468,133644,188337,188367,123596,967,188472,98090,128460,133676,188596,103210,118698,133708,188502,98218,119082,2316,101574,188857,102348,128588,184873,188999,102732,123724,189110,189142,102860,123852,189244,189277,98602,128716,189369,189401,103338,119210,189483,189515,98730,122410,2572,189621,133058,102988,189738,189772,133097,103116,189880,189915,188626,103244,190014,1317,188713,101930,190140,190174,188743,103722,122538,190288,188896,102058,190378,190403,102600,133136,190506,190543,185184,133175,190648,190685,185257,188969,190782,124236,1351,189662,190917,128844,185385,190049,191041,191068,185417,190249,191155,191183,191208,117958,133214,191311,128972,185513,191414,103372,124364,185545,191557,103756,126540,191659,191692,102186,129356,185641,191816,103850,122666,185897,191930,191960,122794,2829,192036,192077,192116,192153,192187,192219,192258,192295,192330,192362,192392,192429,192464,192497,192527,192555,192589,192621,192651,192678,192703,192735,192765,192793,192818,192841,133253,103884,192958,192992,193024,193063,193100,193135,193167,193197,193234,193269,193302,193332,193360,193394,193426,193456,193483,193508,193540,193570,193598,193623,193646,193687,193726,193763,193797,193829,193868,193905,193940,193972,194002,194039,194074,194107,194137,194165,194199,194231,194261,194288,194313,194345,194375,194403,194428,194451,194492,194531,194568,194602,194634,194673,194710,194745,194777,194807,194844,194879,194912,194942,194970,195004,195036,195066,195093,195118,195150,195180,195208,195233,195256,195297,195336,195373,195407,195439,195478,195515,195550,195582,195612,195649,195684,195717,195747,195775,195809,195841,195871,195898,195923,195955,195985,196013,196038,196061,196102,196141,196178,196212,196244,196283,196320,196355,196387,196417,196454,196489,196522,196552,196580,196614,196646,196676,196703,196728,196760,196790,196818,196843,196866,196907,196946,196983,197017,197049,197088,197125,197160,197192,197222,197259,197294,197327,197357,197385,197419,197451,197481,197508,197533,197565,197595,197623,197648,197671,197712,197751,197788,197822,197854,197893,197930,197965,197997,198027,198064,198099,198132,198162,198190,198224,198256,198286,198313,198338,198370,198400,198428,198453,254621,254661,254699,254734,254768,254806,254842,254875,254907,254942,254975,255005,255034,255068,255100,255129]
def base (q dB dC : Nat) : Nat :=
  if q<9 then body6 q dB dC else if q<16 then baseTab.getD (25*q+5*dB+dC) 0
  else if q=16 then body7Tab.getD dB 0 else baseTab.getD (425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
/-- r6 bodies omit chain C's copy when chains B and C both have the largest digit (C is buffer-safe). -/
def skipBody (q dB dC : Nat) : Bool := decide (q<9 ∧ dB=mx q ∧ dC=mx q)
/-- End of the body (next dispatch). The r7 pair (q = 16) has no chain C: its checksum dispatch is at `pcC`. -/
def pcX (q dB dC : Nat) : Nat :=
  if q=16 then pcC q dB dC else pcC q dB dC+partLen q dC-(if skipBody q dB dC then 4 else 0)
def entOff (q : Nat) : Nat :=
  if q=0 then 1315 else if q=1 then 1350 else if q=2 then 548 else if q=3 then 582
  else if q=4 then 804 else if q=5 then 838 else if q=6 then 1444 else if q=7 then 1478
  else if q=8 then 676 else if q=9 then 64 else if q=10 then 710 else if q=11 then 932
  else if q=12 then 966 else if q=13 then 1276 else if q=14 then 1532 else if q=15 then 764 else 1188
/-- First cell word of rank `k` in group `q`: r6 cells, #938's r5 column `1024 (125 - k) + entOff q`, the r7 pair in
#938's q8 column (`entOff 8 = 676`). -/
def cellW (q k : Nat) : Nat :=
  if q<9 then cell6 q (rawOf6 q k) else if q<16 then 1024*(125-k)+entOff q
  else if q=16 then 1024*(125-k)+entOff 8 else 0
def entW (q k : Nat) : Nat := cellW q k + (if q=9 ∧ k%2=0 then 1 else 0)
def inl (q : Nat) : Bool := decide (q=9 ∨ (13 ≤ q ∧ q ≤ 15))
def leadOff (q : Nat) : Nat := 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
def rowInl (q k : Nat) : Bool := inl q || decide (9≤q ∧ q<16 ∧ 3≤kss q k)
def gbase (q k : Nat) : Nat :=
  if rowInl q k then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
/-- Shared-body groups: the r6 groups and the r7 pair. -/
def sharedG (q : Nat) : Bool := decide (q<9 ∨ q=16)
def skipA (q k : Nat) : Bool := decide (q=0 ∧ kdig q k 0=mx q)
def skipB (q k : Nat) : Bool := (rowInl q k || sharedG q) && decide (kdig q k 0=mx q ∧ kdig q k 1=mx q)
def skipC (q k : Nat) : Bool := (rowInl q k || decide (q<9)) && decide (kdig q k 1=mx q ∧ kdig q k 2=mx q)
/-- Start of chain B. Shared-body groups keep chain B's copy in the body; a buffer-safe chain B is jumped over (+4). -/
def gB (q k : Nat) : Nat :=
  if sharedG q then gbase q k+2*mx q+1+(if skipB q k then 4 else 0)
  else gbase q k+2*mx q+1-(if skipA q k then 4 else 0)
def gC (q k : Nat) : Nat := gB q k+partLen q (kdig q k 1)-(if skipB q k then 4 else 0)
/-- End of the group's code for rank `k` (the next dispatch); the r7 pair has no chain C. -/
def gX (q k : Nat) : Nat :=
  if q=16 then gC q k else gC q k+partLen q (kdig q k 2)-(if skipC q k then 4 else 0)
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,5,5⟩
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,4,4⟩
def headJDF (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  {headJD rb o tgt i d g with stop:=.fuel,steps:=4,cycles:=4}
def headJDTermF (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  {headJDTerm rb o tgt i d with stop:=.fuel,steps:=3,cycles:=3}
def s8R (n p : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (-BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf (p+1)),.fuel,1,1⟩
/-- T51 group 0's first cell word `addi s8,zero,T-kss`. -/
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (BitVec.ofNat 64 topT-BitVec.ofNat 64 (kss 0 k))),[],[]⟩,
    .c (pcOf (cellW 0 k+1)),.fuel,1,1⟩
def bge9R (p : Nat) : Result :=
  ⟨SymState.init,.ite .ge (.reg .x16) (.c 0) (.c (BitVec.ofNat 64 (0x1000+4*p-4096))) (.c (pcOf (p+1))),.branch,1,1⟩
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset a)))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+4)),steps:=4,cycles:=4}
def shift12 (w : Reg) (b : Nat) : E :=
  if b<12 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (12-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-12)))
def dispatchR (q : Nat) : Result :=
  let sh := shift12 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*q-64)
  let a := .bin .and sh (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (2^64+4*entOff q-4096)))) (.c (~~~1#64)),.jump,3,3⟩
def dispatch9R : Result :=
  let a := .bin .and (.bin .sll (.reg .x17) (.c (BitVec.ofNat 64 13))) (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c 256)) (.c (~~~1#64)),.jump,3,3⟩
/-- Field source of the dispatch into r6 group `h` (1..8): g1 = a6 bits 8..15 (no shift), g2..g6 = a6 >> 8(h-1),
g7 = a7 >> 40 (bits 112..119), g8 = a7 >> 48 (bits 120..127); masked with t4 = 0xFF00. -/
def r6Src (h : Nat) : E :=
  if h=1 then .reg .x16 else if h<7 then .bin .srl (.reg .x16) (.c (BitVec.ofNat 64 (8*h-8)))
  else if h=7 then .bin .srl (.reg .x17) (.c 40#64) else .bin .srl (.reg .x17) (.c 48#64)
/-- `a4 = s2 - 256 raw` (table B) or `256 raw + s2` (table A). -/
def r6A (h : Nat) : E :=
  if r6B h then .bin .sub (.reg .x18) (.bin .and (r6Src h) (.reg .x29))
  else .bin .add (.bin .and (r6Src h) (.reg .x29)) (.reg .x18)
/-- The jalr immediate of the dispatch into r6 group `h` (sign-extended): 4 (64 row0 + off - 212992). -/
def r6Imm (h : Nat) : Word :=
  if r6B h then BitVec.ofNat 64 (2^64+4*r6Off h-256) else BitVec.ofNat 64 (4*r6Off h)
def r6DispR (h : Nat) : Result :=
  ⟨⟨RegFile.init.set .x14 (r6A h),[],[]⟩,.bin .and (.bin .add (r6A h) (.c (r6Imm h))) (.c (~~~1#64)),.jump,
    (if h=1 then 3 else 4),(if h=1 then 3 else 4)⟩
/-- T51: the r6 mask word `0xFF00` is loaded by group 0's bodies (`ld t4,-288(s1)`: verify data word 16). -/
def maskE : E := .ld (.bin .add (.reg .x2) (.c (BitVec.ofNat 64 16)))
def g0A : E := .bin .sub (.c 856064#64) (.bin .and (.reg .x16) maskE)
/-- Group 0's next dispatch `ld t4,-288(s1); lui s2,209; and a4,a6,t4; sub a4,s2,a4; jalr -72(a4)` (into g1). -/
def g0DispR : Result :=
  ⟨⟨((RegFile.init.set .x29 maskE).set .x18 (.c 856064#64)).set .x14 g0A,[],
    [.valid ⟨some (.reg .x2),BitVec.ofNat 64 16⟩ 8]⟩,
    .bin .and (.bin .add g0A (.c (BitVec.ofNat 64 (2^64-72)))) (.c (~~~1#64)),.jump,5,5⟩
/-! ### T51 checksum chain 50
The r7 pair's bodies end with `addi a4,s8,89; slli a4,a4,11; jalr 1168(a4)`: with s8 = T - sum(d0..d49) it lands on
word `44836 + 512 s8`; `ckArm d` (d = s8 in 0..5) holds chain 50's code for digit d followed by the final tail at
`ckTail d` (#938's tail without its sum check); every other reachable s8 (sum <= 231) lands on a zero word. -/
def ckE : E := .bin .sll (.bin .add (.reg .x24) (.c 89#64)) (.c 11#64)
def ckDispR : Result :=
  ⟨⟨RegFile.init.set .x14 ckE,[],[]⟩,.bin .and (.bin .add ckE (.c 1168#64)) (.c (~~~1#64)),.jump,3,3⟩
def ckArm (d : Nat) : Nat := 44836+512*d
def ckTail (d : Nat) : Nat := ckArm d+partLen 17 d
/-- Landing word of the checksum dispatch for data digit sum `ds` (s8 = topT - ds). -/
def ckWord (ds : Nat) : Nat := 44836+512*topT-512*ds
/-- The dispatch at the end of top group `q`: q = 0 the 5-word g1 dispatch (mask/table setup), r6 groups into the
next r6 group, g8 into q9 (#938's dispatch9), q9..q14 into q+1, q15 into the r7 pair (#938's dispatch into group 8),
the r7 pair into the checksum arms. -/
def nextDispR (q : Nat) : Result :=
  if q=0 then g0DispR else if q<8 then r6DispR (q+1) else if q=8 then dispatch9R
  else if q<15 then dispatchR (q+1) else if q=15 then dispatchR 8 else ckDispR
def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))
def partOK (q i d p : Nat) (skip : Bool := false) : Bool :=
  if d=mx q then (if skip then rOK (vrun p 0) (emptyR p) else rOK (vrun p 4) (copyFH .x8 (off i) (slot i) p (topG i)))
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x8 (off i) d (slot i) p i
       else headRH .x8 (off i) d none p i (topG i)) &&
    rungsOK q (d+1) (slot i) (p+5)
def s8Check (q k : Nat) : Bool :=
  (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))) &&
  (if q=9 ∧ k%2=0 then rOK (vrun (cellW 9 k) 1) (bge9R (cellW 9 k)) else true)
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (nextDispR q) else true
/-- A shared body: chain A's rung ladder (tails and rungs; its terminal step targets `termSlot`), chain B, chain C
(absent for the r7 pair), the next dispatch. -/
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (termSlot (3*q)) (base q dB dC) &&
  rungsOK q 0 (termSlot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  (decide (q=16) || partOK q (3*q+2) dC (pcC q dB dC) (skipBody q dB dC)) && dispatchOK q dB dC
def inlineCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  s8Check q k &&
  (if dA=mx q then
    (if skipA q k then rOK (vrun (leadPc q k) 0) (emptyR (leadPc q k))
     else rOK (vrun (leadPc q k) 4) (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k) (topG (3*q))))
   else
    rOK (vrun (leadPc q k) (if dA+1=mx q then 3 else 4))
      (if dA+1=mx q then headJDTermF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
       else headJDF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q))) &&
    rOK (vrun (gbase q k+2*dA+1) 2)
      (tailR (if dA+1=mx q then some (termSlot (3*q)) else none) (gbase q k+2*dA+1)) &&
    rungsOK q (dA+1) (termSlot (3*q)) (gbase q k+2*(dA+1))) &&
  partOK q (3*q+1) (kdig q k 1) (gB q k) (skipB q k) && partOK q (3*q+2) (kdig q k 2) (gC q k) (skipC q k) &&
  rOK (vrun (gX q k) 5) (nextDispR q)
def entCheck (q k : Nat) : Bool :=
  if rowInl q k then inlineCheck q k else
  let dA := kdig q k 0
  if dA=mx q then
    (if q=0 then rOK (vrun (leadPc q k) 1) (T3M.skipJB (gB q k))
     else rOK (vrun (leadPc q k) 7) (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k) (topG (3*q))))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q)))
/-- Live shared blocks: every block of an r6 group; the r7 pair's 7 bodies (`x = dB`); for #938's non-inline r5
groups only the blocks with `dB + dC < 3` (a row with `kss ≥ 3` is inline; the dead blocks are not checked). -/
def liveBlock (q x : Nat) : Bool :=
  if q=16 then blockCheck 16 x 0
  else if q<9 ∨ x/(mx q+1)+x%(mx q+1) < 3 then blockCheck q (x/(mx q+1)) (x%(mx q+1)) else true
/-- Number of ranks of group `q` (`216` r6, `125` r5, `49` the r7 pair). -/
def nRank (q : Nat) : Nat := if q=16 then 49 else (mx q+1)^3
/-- Number of shared-body indices of group `q` (`(mx+1)^2`; the r7 pair: 7, indexed by `dB`). -/
def nBlock (q : Nat) : Nat := if q=16 then 7 else (mx q+1)^2
def tripleCheck (q : Nat) : Bool :=
  ((List.range (nRank q)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range (nBlock q)).all (liveBlock q))
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
/-! ### T51 guards -/
/-- The word at `p` is zero (an illegal instruction: fetch faults). -/
def zeroAt (p : Nat) : Bool := (lcode p).head? == some 0#32
def raw6Valid (g raw : Nat) : Bool := if g=0 then decide (40≤raw) else decide (raw<216)
/-- Invalid r6 fields (g = 0: raw 3..39; g >= 1: raw 216..255) land on zero words (g = 0, raw < 3: below the code). -/
def guard6Check (g raw : Nat) : Bool := raw6Valid g raw || (g=0 && decide (raw<3)) || zeroAt (cell6 g raw)
def guard6All (g : Nat) : Bool := (List.range 256).all (guard6Check g)
/-- Invalid r7 ranks 49..125 land on zero words (126, 127 land below the code). -/
def r7GuardCheck (k : Nat) : Bool := decide (k<49) || zeroAt (cellW 16 k)
def r7GuardAll : Bool := (List.range 126).all r7GuardCheck
/-- Reachable checksum landings (data sum <= 231) outside the 6 arms are zero words. -/
def ckGuardCheck (ds : Nat) : Bool := decide (topT-5≤ds ∧ ds≤topT) || zeroAt (ckWord ds)
def ckGuardAll : Bool := (List.range 232).all ckGuardCheck
def ckArmCheck (d : Nat) : Bool := partOK 17 50 d (ckArm d)
def ckArmAll : Bool := (List.range 6).all ckArmCheck
theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps Images.verifyImage s r.steps r.cycles (r.toState s) := by
  exact symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch Images.verifyImage (r.toState s)=some (.base .ECALL) := by
  exact symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
end SigGolfCandidate.T3M.Nonbinary
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsSem ====
section

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
structure NCtx where
  w : ClaudeWCT.W9.T3M.WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat
namespace NCtx
/-- Charge 86: chain `i`'s block (`= WIT + chainBlock 0 i` for `S3 = 14128`). -/
def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + topSlot i
/-- Address of the supplied value (G: block start, F: block + 48). -/
def vAt (c : NCtx) (i : Nat) : Nat := c.blk i + 48 * (i % 2)
/-- Hash destination of an interior step (G: block - 16, so the high half lands on the value; F: block + 48). -/
def oAt (c : NCtx) (i : Nat) : Nat := c.blk i + 64 * (i % 2) - 16
/-- The two pads (G: +32, +48; F: +0, +32). -/
def pad0At (c : NCtx) (i : Nat) : Nat := c.blk i + 32 - 32 * (i % 2)
def pad1At (c : NCtx) (i : Nat) : Nat := c.blk i + 48 - 16 * (i % 2)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
/-- Campaign T51: largest digit of top chain `i` (`= T3.maxDigit 0 i`): r6 groups q < 9 (chains 0..26) 5, r5 groups
9 <= q < 16 (chains 27..47) 4, the r7 pair (group 16, chains 48/49) 6, the checksum chain 50 (`mx 17`) 5. -/
def topMax (i : Nat) : Nat := if i < 50 then mx (i / 3) else mx 17
def last (i : Nat) : Nat := topMax i - 1
/-- The half of the step-`m` answer the image keeps (`= WCT9.chainHigh 0 i m`): G chains keep the high half on
interior steps; campaign T51 (PIN v1): chain 0 keeps it on its terminal step too (answer at `slot 0 - 16`). -/
def topHigh (i m : Nat) : Bool := topG i && (decide (m + 1 < topMax i) || decide (i = 0))
def «prefix» (c : NCtx) : Nat := 128 + 193 * 2 ^ 56 + ((c.tree * 2 ^ 12 + c.leaf) % 2 ^ 32) * 2 ^ 16
def w0 (c : NCtx) (i : Nat) : Nat := c.prefix + i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad0At i - Verify.WIT)
def pad1 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad1At i - Verify.WIT)
def padHeader (c : NCtx) (i : Nat) : Word := (ClaudeWCT.W9.T3M.wdig c.w (c.blk i - Verify.WIT + 16)).extractLsb' 64 64
def val (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.vAt i - Verify.WIT)
def ok (c : NCtx) : Prop :=
  c.tree = 0 ∧ c.leaf < 4096 ∧ c.S3 % 8 = 0 ∧ Verify.WIT + 8336 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x5000 ∧
    c.ret < 209920
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (.x28, BitVec.ofNat 64 (c.prefix + 385)), (.x8, BitVec.ofNat 64 c.S3), (.x2, BitVec.ofNat 64 0xffbde0), (.x4, 24704)]
/-- Rank of top group `q`: the digit triple in radix `mx q + 1`; group 16 (the r7 pair, chains 48 and 49) has only two
digits, `d48 + 7 d49`. -/
def kOf (c : NCtx) (q : Nat) : Nat :=
  if q = 16 then c.dig 48 + 7*c.dig 49 else
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := gbase (i/3) (c.kOf (i/3))
def qB (c : NCtx) (i : Nat) : Nat := gB (i/3) (c.kOf (i/3))
def qC (c : NCtx) (i : Nat) : Nat := gC (i/3) (c.kOf (i/3))
def qX (c : NCtx) (i : Nat) : Nat := gX (i/3) (c.kOf (i/3))
def entPc (c : NCtx) (q : Nat) : Nat := entW q (c.kOf q)
/-- Buffer-safe chain (`= WCT9.safeZeroCopy 0`): its value already sits in its leaf slot. The checksum chain 50 is
never buffer-safe (its arm always copies). -/
def bufferSafe (c : NCtx) (i : Nat) : Prop :=
  c.dig i = topMax i ∧
    (i = 0 ∨ (0 < i ∧ i % 3 ≠ 0 ∧ i ≠ 50 ∧ c.dig (i-1) = topMax (i-1)))
instance (c : NCtx) (i : Nat) : Decidable (c.bufferSafe i) := by
  unfold bufferSafe; infer_instance
/-- End of the leaf-buffer bytes written by chains `1 .. i-1` (endpad leaf: chain `j >= 1` writes `[slot j, slot j +
16)` (copy) or `[slot j, slot j + 32)` (terminal hash, junk high half on `slot (j+1)`)). -/
def bufferEnd (c : NCtx) (i : Nat) : Nat :=
  slot i + (if 1 < i ∧ c.dig (i-1) ≠ topMax (i-1) then 16 else 0)
def bufferOrig (c : NCtx) (s0 : MachineState) : Prop :=
  ∀ i, i < 51 → ∀ k < 2, OrigW c.w s0 (slot i + 8*k)
def bufferVal (c : NCtx) (i : Nat) : Digest :=
  if c.bufferSafe i then ClaudeWCT.W9.T3M.wdig c.w (slot i - Verify.WIT) else c.val i
/-- Start of chain `i`. Campaign T51: chains `i < 50` sit in group `i / 3` (lead chain in the cell, B/C in the body;
group 16 = the r7 pair, chain 48 lead, chain 49 = its chain B); the checksum chain 50 starts at its arm
`ckArm d50`. -/
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i < 50 then (if i%3=0 then leadPc (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i)
  else ckArm (c.dig 50)
def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 ∧ i < 50 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 2 else 3) + 2*(m-c.dig i)
/-- End of chain `i`. Chain 49 (the r7 pair's chain B) ends at `qC 49` (= the checksum dispatch); the checksum chain 50
(never buffer-safe) ends at the final tail `ckTail d50`. -/
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i < 50 then (if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i)
  else ckTail (c.dig 50)
/-- Bytes written before chain `i` (charge 86): the leaf buffer (chains `1 .. i-1` from `slot 1` on; chain 0 at most
`[slot 0 - 16, slot 0 + 16)`, never the tweak `[slot 0 + 16, slot 1)`), the pairs `p < i / 2` (the F chain of pair `p`
spills its junk 16 bytes into pair `p - 1`, chain 1 past the area), and the G half `[pair, pair + 40)` of pair `i / 2`
when `i` is odd. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (slot 1 ≤ A ∧ A < c.bufferEnd i) ∨ (0 < i ∧ slot 0 - 16 ≤ A ∧ A < slot 0 + 16) ∨
    (c.S3 + 104 * (27 - i / 2) ≤ A + 1664 ∧ A < c.S3 + 1160) ∨
    (i % 2 = 1 ∧ c.S3 + 104 * (26 - i / 2) ≤ A + 1664 ∧ A + 1664 < c.S3 + 104 * (26 - i / 2) + 40)
/-- Chain `i`'s own writes: its header word and the 32-byte destination of its interior steps. -/
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 24) ∨ (c.oAt i ≤ A ∧ A < c.oAt i + 32)
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  ((∀ i, i < 51 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ c.bufferOrig s0) ∧ Verify.DataOK s0
def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)
def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 8 = 128 + i ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i
def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.vAt i) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.oAt i)) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i ∧ DigAt t (c.vAt i) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then termSlot i else c.oAt i) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)
theorem topSlot_props (i : Nat) (hi : i < 51) : topSlot i % 8 = 0 ∧ 16 ≤ topSlot i ∧ topSlot i + 64 ≤ 2808 := by
  unfold topSlot; omega
theorem topG_eq (i : Nat) : topG i = T3.topIsG i := by simp [topG, T3.topIsG]
theorem topG_isG (i : Nat) : topG i = ClaudeWCT.WCT9.isG 0 i := by rw [ClaudeWCT.WCT9.isG_top_eq, topG_eq]
theorem topG_lt (i : Nat) (hi : i < 51) : topG i = decide (i % 2 = 0) := by
  unfold topG; by_cases h : i % 2 = 0 <;> simp [h] <;> omega
theorem topSlot_eq (i : Nat) : topSlot i = ClaudeWCT.W9.T3M.chainSlot 0 i := by
  unfold topSlot ClaudeWCT.W9.T3M.chainSlot; simp only [Fin.val_zero, if_true]; split <;> omega
theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.blk i % 8 = 0 ∧ Verify.WIT + 8352 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x5000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold blk Verify.WIT at *; refine ⟨?_, ?_, ?_⟩ <;> omega
/-- Chain `i`'s block lies in pair `i / 2` (`[pair, pair + 104)` with `pair = S3 - 1664 + 104 (26 - i / 2)`). -/
theorem blk_eq (c : NCtx) (i : Nat) (hi : i < 51) :
    c.blk i = c.S3 - 1664 + 104 * (26 - i / 2) + 16 + 24 * (i % 2) := by
  unfold blk topSlot; omega
theorem vAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.vAt i % 8 = 0 ∧ c.vAt i = c.blk i + 48 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold vAt; omega
theorem oAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.oAt i % 8 = 0 ∧ Verify.WIT + 8336 ≤ c.oAt i ∧ c.oAt i + 32 ≤ 0x5000 ∧
      c.oAt i + 16 = c.blk i + 64 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold oAt; omega
theorem oAt_G (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (hg : topG i = true) : c.oAt i + 16 = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
theorem oAt_F (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (hg : topG i = false) : c.oAt i = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
/-- `topMax` is the scheme's top `maxDigit` (T51: 5 / 4 / 6 / 5). -/
theorem topMax_eq (i : Nat) : topMax i = maxDigit 0 i := by
  unfold topMax mx maxDigit
  simp only [ite_true]
  split_ifs <;> omega
theorem topHigh_eq (i m : Nat) : topHigh i m = ClaudeWCT.WCT9.chainHigh 0 i m := by
  rw [ClaudeWCT.WCT9.chainHigh_top_eq]
  unfold topHigh T3.topChainHigh
  rw [topG_eq, topMax_eq]
/-- Campaign T51 (endpad leaf): `slot 0 = 25216` (end_0), the tweak at 25232, `slot i = 25232 + 16 i` for `i >= 1`
(the checksum chain's 32-byte terminal HASH output ends at 26064). -/
theorem slot_props (i : Nat) (hi : i < 51) : slot i % 16 = 0 ∧ 25216 ≤ slot i ∧ slot i + 32 ≤ 26064 := by
  unfold slot; split <;> omega
theorem slot0 : slot 0 = 25216 := rfl
theorem slot1 : slot 1 = 25248 := rfl
theorem slot_pos (i : Nat) (hi : 0 < i) : slot i = 25232 + 16 * i := by
  unfold slot; rw [if_neg (by omega)]
theorem slot_succ (i : Nat) (hi : 0 < i) : slot (i + 1) = slot i + 16 := by
  rw [slot_pos i hi, slot_pos (i + 1) (by omega)]; ring
/-- Destination of chain `i`'s terminal hash (`termSlot`, ChainsLayout): its leaf slot; chain 0 (high half kept)
writes at `slot 0 - 16`, so its junk low half lands on the dead L1 leaf-buffer tail and the leaf tweak
`[slot 0 + 16, slot 1)` is untouched. -/
theorem termSlot_props (i : Nat) (hi : i < 51) :
    termSlot i % 16 = 0 ∧ 25200 ≤ termSlot i ∧ termSlot i + 32 ≤ 26064 ∧ (i = 0 → termSlot i + 16 = slot 0) ∧
      (0 < i → termSlot i = slot i) := by
  unfold termSlot slot; split_ifs <;> omega
theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
/-- The hash destination register of an interior step (`gOut`). -/
theorem oAt_eval (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (x : Word) (hx : x = BitVec.ofNat 64 (c.blk i)) :
    x + gOut (topG i) = BitVec.ofNat 64 (c.oAt i) := by
  have hb := c.blk_props hc i hi
  subst hx
  rw [topG_lt i hi]
  unfold oAt
  by_cases h : i % 2 = 0
  · simp only [h, decide_true]
    rw [show gOut true = BitVec.ofNat 64 18446744073709551600 by unfold gOut; rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show c.blk i + 18446744073709551600 = (c.blk i + 64 * 0 - 16) + 2^64 by
      omega, Nat.add_mod_right]
  · simp only [h, decide_false]
    rw [show gOut false = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
    congr 1; omega
theorem prefix_props (c : NCtx) : c.prefix % 2 ^ 16 = 128 ∧ c.prefix < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold «prefix»
  constructor <;> omega
theorem w0_lt (c : NCtx) (i m : Nat) (hi : i < 51) (hm : m < 256) : c.w0 i + 2 ^ 8 * m < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold w0 «prefix»; omega
theorem w0_header (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 51) (hm : m < 8) :
    BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) = (chainHeader 0 c.tree c.leaf i m).extractLsb' 0 64 := by
  rw [chainHeader_low_bounded _ _ _ _ _ (by omega) hm
    (by rw [hc.1]; decide +kernel) hc.2.1]
  congr 1
  simp only [w0, «prefix», packedPrefix, packedHi, show height 0 = 12 from rfl, Fin.val_zero,
    Nat.zero_mul, Nat.add_zero]
  ring
set_option maxRecDepth 20000 in
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 51) (hm : m < 8) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.pad0At i) (c.pad0 i)) (hp1 : DigAt t (c.pad1At i) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i)
    (hv : DigAt t (c.vAt i) v) :
    hashInput t = toQ (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputL_length _ _ _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputL, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two]
  rw [topG_lt i hi]
  by_cases hg : i % 2 = 0
  · have ev : c.vAt i = c.blk i := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i + 32 := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 48 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_pos (by simpa using hg)]
    rw [hv.1, hv.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp0.1, hp0.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hp1.1, hp1.2, w0_header c hc i m hi hm]
    rfl
  · have h1 : i % 2 = 1 := by omega
    have ev : c.vAt i = c.blk i + 48 := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 32 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_neg (by simpa using hg)]
    rw [hp0.1, hp0.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_header c hc i m hi hm]
    rfl
/-- On the top layer the format of chain `i` is `topG i` (`= WCT9.isG 0 i`). -/
theorem chainInputL_top (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest) :
    chainInputL 0 tree leaf i step p0 p1 headerPad v (topG i) =
      ClaudeWCT.W9.T3M.chainInputPW 0 tree leaf i step p0 p1 headerPad v := by
  unfold chainInputL ClaudeWCT.W9.T3M.chainInputPW; rw [topG_isG]
theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 51) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1.1 i hi k hk
/-- No chain processed before chain `i` (nor a buffer write) touched chain `i`'s block. -/
theorem notWr_block (c : NCtx) (hc : c.ok) {i A : Nat} (hi : i < 51) (h1 : c.blk i ≤ A) (h2 : A < c.blk i + 64) :
    ¬ c.Wr i A := by
  have hb := c.blk_props hc i hi
  have he := c.blk_eq i hi
  have hlo := hc.2.2.2.1
  unfold Wr
  rw [slot0, slot1]
  omega
theorem dig_at {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : i < 51) (hA1 : c.blk i ≤ A) (hA2 : A + 16 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW0 : ¬ W A) (hW1 : ¬ W (A + 8)) :
    DigAt t A (ClaudeWCT.W9.T3M.wdig c.w (A - Verify.WIT)) := by
  have hb := c.blk_props hc i hi
  have e0 : c.blk i + 8 * ((A - c.blk i) / 8) = A := by omega
  have e1 : c.blk i + 8 * ((A - c.blk i) / 8 + 1) = A + 8 := by omega
  have o0 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8) (by omega) (by rw [e0]; exact hW0)
  have o1 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8 + 1) (by omega) (by rw [e1]; exact hW1)
  rw [e0] at o0; rw [e1] at o1
  exact DigAt_origW o0 o1 (by omega)
theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 51) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.pad0At i) (c.pad0 i) ∧ DigAt t (c.pad1At i) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ A, c.blk i ≤ A → A < c.blk i + 64 → (A < c.blk i + 16 ∨ c.blk i + 24 ≤ A) →
      (i % 2 = 0 → c.blk i + 16 ≤ A) → (i % 2 = 1 → A < c.blk i + 48) → ¬ c.WrIn i A := by
    intro A h1 h2 h3 h4 h5 hw
    rcases hw with hw | hw | hw
    · exact c.notWr_block hc hi h1 h2 hw
    · omega
    · unfold oAt at hw; omega
  unfold pad0 pad1
  have e0 : c.pad0At i = c.blk i + 32 - 32 * (i % 2) := rfl
  have e1 : c.pad1At i = c.blk i + 48 - 16 * (i % 2) := rfl
  rw [e0, e1]
  refine ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega)),
    dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))⟩
theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 51)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.vAt i) (c.val i) := by
  have hb := c.blk_props hc i hi
  unfold val
  have ev : c.vAt i = c.blk i + 48 * (i % 2) := rfl
  rw [ev]
  exact dig_at hF h0 hc hi (by omega) (by omega) (by omega) (c.notWr_block hc hi (by omega) (by omega))
    (c.notWr_block hc hi (by omega) (by omega))
theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 7 := by
  unfold topMax mx; split_ifs <;> omega
theorem topMax_mx (i : Nat) (hi : i < 50) : topMax i = mx (i / 3) := by
  unfold topMax; rw [if_pos hi]
theorem topMax_ck : topMax 50 = mx 17 := rfl
theorem topMax_r6 (i : Nat) (hi : i < 27) : topMax i = 5 := by
  unfold topMax mx; rw [if_pos (by omega), if_pos (by omega)]
theorem topMax_r5 (i : Nat) (h1 : 27 ≤ i) (hi : i < 48) : topMax i = 4 := by
  unfold topMax mx; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
theorem topMax_r7 (i : Nat) (h1 : 48 ≤ i) (hi : i < 50) : topMax i = 6 := by
  unfold topMax mx; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem topMax_50 : topMax 50 = 5 := rfl
theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 6 := by
  have := topMax_bounds i; unfold last; omega
theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega
def DigitsOk (c : NCtx) : Prop := ∀i,i<51 → c.dig i ≤ topMax i
/-- Digits of the triple groups `q < 16` (chains `3q .. 3q+2 < 48`). -/
theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<16) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  rwa [topMax_mx _ (by omega), show (3*q+k)/3=q by omega] at h
theorem kOf_triple (c : NCtx) (q : Nat) (hq : q<16) :
    c.kOf q = c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2) := by
  unfold kOf; rw [if_neg (by omega)]
theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  rw [c.kOf_triple q hq]
  unfold mx at *
  split_ifs at * <;> omega
theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  rw [c.kOf_triple q hq]
  unfold mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩
/-- The r7 pair (group 16): rank `d48 + 7 d49 < 49`. -/
theorem kOf16_lt (c : NCtx) (hd : c.DigitsOk) : c.kOf 16 < 49 := by
  have h0 := hd 48 (by omega); have h1 := hd 49 (by omega)
  rw [topMax_r7 48 (by omega) (by omega)] at h0; rw [topMax_r7 49 (by omega) (by omega)] at h1
  unfold kOf; rw [if_pos rfl]; omega
theorem kdig_kOf16 (c : NCtx) (hd : c.DigitsOk) :
    kdig 16 (c.kOf 16) 0=c.dig 48 ∧ kdig 16 (c.kOf 16) 1=c.dig 49 ∧ kdig 16 (c.kOf 16) 2=0 := by
  have h0 := hd 48 (by omega); have h1 := hd 49 (by omega)
  rw [topMax_r7 48 (by omega) (by omega)] at h0; rw [topMax_r7 49 (by omega) (by omega)] at h1
  have hm : mx 16 = 6 := rfl
  have hk : c.kOf 16 = c.dig 48 + 7*c.dig 49 := by unfold kOf; rw [if_pos rfl]
  unfold kdig; rw [hm, hk]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Nat.reduceAdd, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;> omega
theorem kdig_kOf (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    kdig q (c.kOf q) 0=c.dig (3*q) ∧ kdig q (c.kOf q) 1=c.dig (3*q+1) ∧ kdig q (c.kOf q) 2=c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hd q hq
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  unfold kdig
  simp only [pow_zero,Nat.div_one,pow_one]
  refine ⟨k1,k2,?_⟩
  rw [k3]; exact Nat.mod_eq_of_lt (by omega)
theorem bufferEnd_bounds (c : NCtx) (i : Nat) :
    slot i ≤ c.bufferEnd i ∧ c.bufferEnd i ≤ slot i + 16 := by
  unfold bufferEnd; split <;> omega

theorem bufferEnd_mono (c : NCtx) (i : Nat) : c.bufferEnd i ≤ c.bufferEnd (i+1) := by
  have h := c.bufferEnd_bounds i
  have h' := c.bufferEnd_bounds (i+1)
  by_cases h0 : i = 0
  · subst h0; rw [slot0] at h; rw [slot1] at h'; omega
  · have := slot_succ i (by omega); omega

theorem Wr_mono (c : NCtx) (i : Nat) :
    ∀ A, c.Wr i A → c.Wr (i+1) A := by
  intro A h
  have hm := c.bufferEnd_mono i
  unfold Wr at *
  rcases h with h | h | h | h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; left; omega

/-- Chain `i`'s own writes are among the writes before chain `i + 1`. -/
theorem WrIn_next (c : NCtx) (hc : c.ok) (i A : Nat) (hi : i < 51) (h : c.WrIn i A) : c.Wr (i+1) A := by
  have hlo := hc.2.2.2.1
  rcases h with h | h | h
  · exact c.Wr_mono i A h
  · have he := c.blk_eq i hi
    unfold Wr; right; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega
  · have he := c.blk_eq i hi
    unfold oAt at h
    unfold Wr; right; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega

theorem Wr_copy (c : NCtx) (i A : Nat)
    (hlo : slot i ≤ A) (hhi : A < slot i + 16) : c.Wr (i+1) A := by
  have h := c.bufferEnd_bounds (i+1)
  unfold Wr slot at *
  split_ifs at * <;> omega

/-- Chain `i`'s terminal hash (32 bytes at `termSlot i`) is among the writes before chain `i + 1`. -/
theorem Wr_hash (c : NCtx) (i A : Nat) (hn : c.dig i ≠ topMax i)
    (hlo : termSlot i ≤ A) (hhi : A < termSlot i + 32) : c.Wr (i+1) A := by
  by_cases h0 : i = 0
  · subst h0
    unfold Wr; right; left
    unfold termSlot at hlo hhi; rw [slot0] at *; simp at hlo hhi; omega
  · have he : c.bufferEnd (i+1) = slot (i+1)+16 := by
      simp [bufferEnd, hn, show 1 < i + 1 by omega]
    unfold termSlot at hlo hhi; rw [if_neg h0] at hlo hhi
    have hs := slot_succ i (by omega)
    have hs1 : slot 1 ≤ slot i := by unfold slot; split_ifs <;> omega
    unfold Wr; left; omega

theorem bufferSafe_end (c : NCtx) (i : Nat) (hs : c.bufferSafe i) :
    c.bufferEnd i = slot i := by
  rcases hs.2 with h | h
  · simp [bufferEnd, h]
  · simp [bufferEnd, h.2.2.2]

theorem bufferSafe_protected (c : NCtx) (i A : Nat) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (ha : slot i ≤ A) : ¬ c.Wr i A := by
  rw [Wr, c.bufferSafe_end i hs]
  by_cases hi : i = 0
  · subst hi; rw [slot0, slot1] at *; omega
  · have h1 := slot_pos i (by omega)
    rw [slot0, slot1] at *; omega

theorem bufferVal_at {c : NCtx} {s0 t : MachineState} (h0 : c.bufferOrig s0)
    {i : Nat} (hi : i < 51) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (hF : Frame s0 t (c.Wr i)) :
    DigAt t (slot i) (c.bufferVal i) := by
  have hp := slot_props i hi
  have o0 := h0 i hi 0 (by omega)
  have o1 := h0 i hi 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  have f0 := hF (slot i) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have f1 := hF (slot i+8) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have t0 : OrigW c.w t (slot i) := by unfold OrigW at *; rw [f0]; exact o0
  have t1 : OrigW c.w t (slot i+8) := by unfold OrigW at *; rw [f1]; exact o1
  rw [bufferVal, if_pos hs]
  exact DigAt_origW t0 t1 (by unfold Verify.WIT; omega)


theorem bufferSafe_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 51 → digits.getD j 0 = c.dig j)
    (i : Nat) (hi : i < 51) : c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy 0 digits i := by
  unfold bufferSafe ClaudeWCT.WCT9.safeZeroCopy
  rw [hd i hi, topMax_eq]
  by_cases hz : i = 0
  · simp [hz]
  · rw [hd (i-1) (by omega), topMax_eq]
    simp [hz]
theorem bufferSlot_source (i : Nat) :
    slot i - Verify.WIT = ClaudeWCT.W9.T3M.leafBufferSlot 0 i := by
  simp only [slot, ClaudeWCT.W9.T3M.leafBufferSlot, ClaudeWCT.W9.T3M.leafBufferBase, Verify.WIT, if_true]
  split_ifs <;> simp_all <;> omega
theorem bufferVal_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 51 → digits.getD j 0 = c.dig j)
    (hS : c.S3 = 14128) (i : Nat) (hi : i < 51) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w 0 digits i := by
  unfold bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [← c.bufferSafe_source digits hd i hi, bufferSlot_source]
  split
  · rfl
  · unfold val ClaudeWCT.W9.T3M.wvalue
    apply congrArg (ClaudeWCT.W9.T3M.wdig c.w)
    have hv : ClaudeWCT.W9.T3M.valueOff 0 i = 48 * (i % 2) := by
      unfold ClaudeWCT.W9.T3M.valueOff; rw [← topG_isG, topG_lt i hi]
      by_cases h : i % 2 = 0 <;> simp [h] <;> omega
    rw [hv]
    simp only [vAt, blk, hS, ClaudeWCT.W9.T3M.chainBlock, ClaudeWCT.W9.T3M.layerBase,
      ClaudeWCT.W9.T3M.pathSlots, Matrix.cons_val_zero, Verify.WIT, ← topSlot_eq]
    omega

theorem bufferVal_nonmax (c : NCtx) (i : Nat) (h : c.dig i ≠ topMax i) :
    c.bufferVal i = c.val i := by simp [bufferVal, bufferSafe, h]

/-- Digit `j` of group `i / 3`'s rank is chain `3 (i / 3) + j`'s digit (the r7 pair: two digits). -/
theorem kdig_chain (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 50) :
    kdig (i/3) (c.kOf (i/3)) (i%3) = c.dig i := by
  by_cases h16 : i/3 = 16
  · rw [h16]
    have : i = 48 ∨ i = 49 := by omega
    rcases this with h | h
    · rw [h]; exact (c.kdig_kOf16 hds).1
    · rw [h]; exact (c.kdig_kOf16 hds).2.1
  · obtain ⟨k0,k1,k2⟩ := c.kdig_kOf hds (i/3) (by omega)
    have : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
    rcases this with h | h | h
    · rw [h, k0, show 3*(i/3) = i by omega]
    · rw [h, k1, show 3*(i/3)+1 = i by omega]
    · rw [h, k2, show 3*(i/3)+2 = i by omega]
theorem rungPc_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 51) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last; omega
  by_cases h50 : i < 50
  · have hmq := topMax_mx i h50
    have hdq : c.dig i < mx (i/3) := hmq ▸ hd
    have hlq : last i + 1 = mx (i/3) := hmq ▸ hl
    have hk := c.kdig_chain hds i h50
    by_cases h0 : i%3=0
    · rw [h0] at hk
      have hskipA : skipA (i/3) (c.kOf (i/3))=false := by simp [skipA, hk, Nat.ne_of_lt hdq]
      have hskipB : skipB (i/3) (c.kOf (i/3))=false := by simp [skipB, hk, Nat.ne_of_lt hdq]
      simp only [rungPc,endPc,qb,qB,h0,h50,and_self,if_true,gB,hskipA,hskipB,Bool.false_eq_true,if_false,
        Nat.sub_zero,Nat.add_zero]
      split_ifs <;> omega
    · by_cases h1 : i%3=1
      · rw [h1] at hk
        have hskip : skipB (i/3) (c.kOf (i/3))=false := by simp [skipB, hk, Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h50,false_and,if_true,if_false,qC,gC,hskip,Bool.false_eq_true,
          Nat.sub_zero,hk]
        change c.qB i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qB i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
      · have h2 : i%3=2 := by omega
        rw [h2] at hk
        have h16 : i/3 ≠ 16 := by omega
        have hskip : skipC (i/3) (c.kOf (i/3))=false := by simp [skipC, hk, Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h50,false_and,if_true,if_false,qX,gX,h16,hskip,Bool.false_eq_true,
          Nat.sub_zero,hk]
        change c.qC i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qC i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
  · have hi50 : i = 50 := by omega
    subst hi50
    have h5 : topMax 50 = 5 := topMax_50
    simp only [rungPc,endPc,startPc,h50,and_false,if_false,if_true,Nat.sub_zero,ckTail]
    unfold partLen
    simp only [mx,show ¬ (17:Nat)<9 by decide,show ¬ (17:Nat)<16 by decide,show ¬ (17:Nat)=16 by decide,if_false]
    have hd5 : c.dig 50 < 5 := by omega
    simp only [if_neg (Nat.ne_of_lt hd5)]
    unfold last at *
    rw [h5] at *
    split_ifs <;> omega
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 6 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x7 1 (by simp [known]) (by decide +kernel)
  · exact kr .x13 2 (by simp [known]) (by decide +kernel)
  · exact kr .x19 3 (by simp [known]) (by decide +kernel)
  · exact kr .x20 4 (by simp [known]) (by decide +kernel)
  · exact kr .x21 5 (by simp [known]) (by decide +kernel)
  · exact kr .x26 6 (by simp [known]) (by decide +kernel)
theorem w0_low (c : NCtx) (i m : Nat) (hi : i < 51) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt c i m hi hm)]
  have hp := c.prefix_props
  unfold w0; constructor <;> omega
theorem w0_low0 (c : NCtx) (i : Nat) (hi : i < 51) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  have := w0_low c i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
/-- The `jal` from a cell into its shared body: lead chains of the non-inline rows (r6 groups, the r5 table rows, the
r7 pair's chain 48). -/
def tableJump (c : NCtx) (i : Nat) : Nat := if (i%3=0 ∧ i<50) ∧ rowInl (i/3) (c.kOf (i/3))=false then 1 else 0
/-- Cycles of chain `i` at digit `d`. As R6: a buffer-safe chain costs its table jump (chain 0's r6 cell `jal`, 1
cycle; every other buffer-safe chain is skipped in place). -/
def chainCost (c : NCtx) (i d : Nat) : Nat :=
  if d=topMax i then (if c.bufferSafe i then c.tableJump i else 4+c.tableJump i)
  else 4+c.tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)
def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => c.chainCost j (c.dig j)).sum
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_TopCost ====
section

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.WCT9
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

private theorem cost_kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 16) :
    kss q (c.kOf q) = c.dig (3*q) + c.dig (3*q+1) + c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]

private theorem sum_flags (P : Nat → Prop) [DecidablePred P] (L : List Nat) :
    (L.map fun i => if P i then 1 else 0).sum = (L.filter fun i => decide (P i)).length := by
  induction L with
  | nil => simp
  | cons i L ih => by_cases h : P i <;> simp [h, ih, Nat.add_comm]

def bufferCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.bufferSafe i then 1 else 0).sum

def exactCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum

def jumps (c : NCtx) : Nat := ((List.range 51).map c.tableJump).sum

theorem chainCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 51) :
    c.chainCost i (c.dig i) + 9*c.dig i +
      (if c.dig i + 1 = topMax i then 1 else 0) +
      4*(if c.bufferSafe i then 1 else 0) = 4 + 9*topMax i + c.tableJump i := by
  have hm := topMax_bounds i
  have hd := hds i (by omega)
  by_cases hs : c.bufferSafe i
  · have hd := hs.1
    simp [chainCost, hs, hd]
    omega
  · unfold chainCost
    split_ifs <;> omega

private theorem sum_map_add (L : List Nat) (f g : Nat → Nat) :
    (L.map fun i => f i + g i).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Campaign T51: the 51 chains' capacity is `4·51 + 9·236 = 2328` plus the table jumps. -/
theorem chainsCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) :
    c.chainsCost 0 51 + 9*((List.range 51).map c.dig).sum + c.exactCredit + 4*c.bufferCredit =
      2328 + c.jumps := by
  have H : ∀ L : List Nat, (∀ i ∈ L, i < 51) →
      (L.map fun j => c.chainCost j (c.dig j)).sum + 9*(L.map c.dig).sum +
        (L.map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum +
        4*(L.map fun i => if c.bufferSafe i then 1 else 0).sum =
      (L.map fun i => 4 + 9*topMax i).sum + (L.map c.tableJump).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := c.chainCost_buffer_balance hds i (hL i (by simp))
      have h2 := ih (fun j hj => hL j (by simp [hj]))
      omega
  have hcap : ((List.range 51).map fun i => 4 + 9*topMax i).sum = 2328 := by decide +kernel
  have := H (List.range 51) (fun i hi => List.mem_range.mp hi)
  rw [hcap] at this
  unfold chainsCost exactCredit bufferCredit jumps
  rw [List.range'_eq_map_range, List.map_map]
  simp only [Function.comp_def, Nat.zero_add]
  exact this

private theorem sum_range_three' (f : Nat → Nat) (n : Nat) :
    ((List.range (3*n)).map f).sum = ((List.range n).map fun q => f (3*q) + f (3*q+1) + f (3*q+2)).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1) = 3*n+1+1+1 by ring, List.range_succ, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih,
      Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Campaign T51: the r6 groups 0..8 and the r7 pair (group 16) always take their table jump; of the kept r5 groups
only the penalised rows 10, 11, 12 can (digit sum below 3); the checksum chain 50 never does. -/
theorem jumps_source (c : NCtx) (hds : c.DigitsOk) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.jumps = 10 + dispatchPenalty 0 digits := by
  have h51 : c.jumps = ((List.range (3*17)).map c.tableJump).sum := rfl
  have hq : ∀ q ∈ List.range 17, c.tableJump (3*q) + c.tableJump (3*q+1) + c.tableJump (3*q+2) =
      (if q < 9 ∨ q = 16 then 1 else 0) +
        (if (q = 10 ∨ q = 11 ∨ q = 12) ∧
          digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0) := by
    intro q hq
    have hq := List.mem_range.mp hq
    have h1 : c.tableJump (3*q+1) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    have h2 : c.tableJump (3*q+2) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    rw [h1, h2]
    by_cases h16 : q = 16
    · subst h16
      unfold tableJump
      simp [rowInl, inl]
    · rw [hd (3*q) (by omega), hd (3*q+1) (by omega), hd (3*q+2) (by omega),
        ← cost_kss_kOf c hds q (by omega)]
      unfold tableJump
      rw [show 3*q/3 = q by omega]
      simp only [show (3*q)%3 = 0 by omega, show 3*q < 50 by omega, and_self, true_and, rowInl, inl]
      generalize kss q (c.kOf q) = x
      interval_cases q <;> simp <;> omega
  rw [h51, sum_range_three', List.map_congr_left hq]
  have hsplit := sum_map_add (List.range 17) (fun q => if q < 9 ∨ q = 16 then 1 else 0)
    (fun q => if (q = 10 ∨ q = 11 ∨ q = 12) ∧
      digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0)
  have h10 : ((List.range 17).map fun q => if q < 9 ∨ q = 16 then 1 else 0).sum = 10 := by decide +kernel
  rw [hsplit, h10]
  unfold dispatchPenalty topDispatchPenalty
  rw [if_pos rfl, sum_flags]

theorem bufferCredit_source (c : NCtx) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.bufferCredit = savedCopies 0 digits := by
  unfold bufferCredit savedCopies
  rw [sum_flags, show chainCount 0 = 51 from rfl]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [decide_eq_decide]
  exact c.bufferSafe_source digits hd i hi'

theorem jumps_le_thirteen (c : NCtx) : c.jumps ≤ 13 := by
  have h : ∀ i, c.tableJump i ≤
      (if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0) := by
    intro i
    unfold tableJump
    by_cases hj : (i%3=0 ∧ i<50) ∧ rowInl (i/3) (c.kOf (i/3))=false
    · rw [if_pos hj]
      have hh : inl (i/3) = false := by
        have hh := hj.2
        simp only [rowInl, Bool.or_eq_false_iff] at hh
        exact hh.1
      simp [hj.1.1, hj.1.2, hh]
    · rw [if_neg hj]
      exact Nat.zero_le _
  have H : ∀ L : List Nat, (L.map c.tableJump).sum ≤
      (L.map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h i) ih
  have H0 := H (List.range 51)
  have he : ((List.range 51).map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum=13 := by
    decide +kernel
  simpa [jumps, he] using H0

theorem chainsCost_any (c : NCtx) (hds : c.DigitsOk) : c.chainsCost 0 51 ≤ 2341 := by
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_le_thirteen
  omega

/-- Campaign T51 cost law of the 51 chains at an accepted word (digit sum 152):
`2328 + 10 + penalty - 9·152 = 970 + penalty`. -/
theorem chainsCost_accepted (c : NCtx) (hds : c.DigitsOk) (v : Digest) (digits : List Nat)
    (hdec : decode 0 v = some digits)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.chainsCost 0 51 + topCredit v + 4*savedCopies 0 digits = 970 + dispatchPenalty 0 digits := by
  obtain ⟨-, -, ⟨hs1, -⟩, rfl⟩ := decode_top_some hdec
  have hlen : (dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum]).length = 51 := by
    simp [dataDigits_top_length]
  have hmap : (List.range 51).map c.dig = dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum] := by
    apply List.ext_getElem
    · simp [hlen]
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [← hd n (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
  have hsum : ((List.range 51).map c.dig).sum = 152 := by
    rw [hmap, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    have : target 0 = 152 := rfl
    omega
  have hex : c.exactCredit = topCredit v := by
    unfold exactCredit topCredit
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [hd i hi', topMax_eq]
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_source hds _ hd
  have hc := c.bufferCredit_source _ hd
  rw [hsum, hex, hc, hj] at hb
  omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsDispatchArith ====
section

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem land_mask12 (n k : Nat) (hk : k≤7) :
    n &&& (4096*(2^k-1))=4096*(n/4096%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (4096 : Nat)=2^12 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 12≤j
  · simp only [h,decide_true,Bool.true_and,show j-12+12=j by omega]
    by_cases hj : j-12<k <;> simp [hj]
  · simp [h]
theorem field_shl12 (W s k : Nat) (hs : s≤12) (hk : k≤7) :
    W*2^s%2^64/4096%2^k=W/2^(12-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (4096 : Nat)=2^12 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+12<64 by omega,show s≤j+12 by omega]
    rw [show j+12-s=j+(12-s) by omega]
  · simp [hj]
def shiftWord12 (W : Word) (b : Nat) : Word := if b<12 then W<<<(12-b) else W>>>(b-12)
theorem word_mask12 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord12 W b &&& 520192#64=BitVec.ofNat 64 (4096*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 4096*x)
  unfold shiftWord12
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl12 _ _ _ (by omega) (by decide +kernel),show 12-(12-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-12)*4096=2^b by rw [show (4096 : Nat)=2^12 by rfl,←pow_add];congr 1;omega]
    rfl
theorem shift12_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift12 w b).eval s=shiftWord12 W b := by
  unfold shift12 shiftWord12
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 12-b<2^64 by omega),Nat.mod_eq_of_lt (show 12-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-12<2^64 by omega),Nat.mod_eq_of_lt (show b-12<64 by omega)]
theorem sub127_xor : ∀ f, f<128 → 127-f=127 ^^^ f := by decide +kernel
theorem not_field (X : Word) (b : Nat) (hb : b+7 ≤ 64) :
    (~~~X).toNat/2^b%128=127-X.toNat/2^b%128 := by
  rw [sub127_xor _ (Nat.mod_lt _ (by decide +kernel))]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, show (128:Nat)=2^7 by norm_num, show (127:Nat)=2^7-1 by norm_num,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]
  by_cases hj : j<7
  · simp [hj, show j+b<64 by omega]
  · simp [hj]
theorem entOff_le (q : Nat) (hq : q<17) : entOff q ≤ 1532 := by interval_cases q <;> decide +kernel
theorem entOff_ge (q : Nat) : 64 ≤ entOff q := by
  by_cases h : q<17
  · interval_cases q <;> decide +kernel
  · simp only [entOff, if_neg (show q≠0 by omega), if_neg (show q≠1 by omega),
      if_neg (show q≠2 by omega), if_neg (show q≠3 by omega), if_neg (show q≠4 by omega),
      if_neg (show q≠5 by omega), if_neg (show q≠6 by omega), if_neg (show q≠7 by omega),
      if_neg (show q≠8 by omega), if_neg (show q≠9 by omega), if_neg (show q≠10 by omega),
      if_neg (show q≠11 by omega), if_neg (show q≠12 by omega), if_neg (show q≠13 by omega),
      if_neg (show q≠14 by omega), if_neg (show q≠15 by omega)]
    decide +kernel
theorem dispatch_value (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord12 W b &&& 520192#64)+BitVec.ofNat 64 (2^64+4*entOff q-4096)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat/2^b%128)+2^64+4*entOff q-4096) := by
  have he := entOff_le q hq
  rw [word_mask12 W b hb,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  apply congrArg (BitVec.ofNat 64); omega
/-- T51: #938's r5 groups 9..15 keep their cell column `1024 (125 - k) + entOff q`. -/
theorem cell_value (q k : Nat) (hq : q<16) (h9 : 9≤q) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)=pcOf (cellW q k) := by
  have he := entOff_le q (by omega)
  unfold pcOf cellW; rw [if_neg (by omega), if_pos hq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
/-- T51: the r7 pair (group 16) is reached by #938's dispatch into group 8 (`entOff 8 = 676`): rank `k < 49` lands
on its cell `cellW 16 k = 1024 (125 - k) + 676`. -/
theorem cell_value_pair (k : Nat) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff 8-4096)=pcOf (cellW 16 k) := by
  unfold pcOf cellW entOff
  simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault125_value (q : Nat) (hq : q<17) :
    BitVec.ofNat 64 (4096*(127-125)+2^64+4*entOff q-4096)=pcOf (entOff q) := by
  have he := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault_value (q k : Nat) (hq : q<17) (hk : 127 ≤ k) (hk' : k<128) :
    (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat<0x1000 ∨
      0x1000+4*257280 ≤ (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat := by
  have he := entOff_le q hq
  have hl := entOff_ge q
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_value (q : Nat) (hq : q<17) (he : 1024≤entOff q) :
    BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)=pcOf (entOff q-1024) := by
  have hu := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_low (q : Nat) (he : entOff q<1024) :
    (BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)).toNat<0x1000 := by
  simp only [BitVec.toNat_ofNat]
  omega
theorem g9_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64)+256#64) &&& ~~~1#64 =
      BitVec.ofNat 64 (8192*(W.toNat%64)+256) := by
  have hm : ((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64) = BitVec.ofNat 64 (8192*(W.toNat%64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hw := W.isLt
    rw [show (13 : Nat) % 2^64 = 13 by rfl]
    rw [Nat.mod_eq_of_lt (show 8192*(W.toNat%64) < 2^64 by omega)]
    have : W.toNat*2^13%2^64/4096%2^7 = 2*(W.toNat%64) := by
      rw [show (2:Nat)^64 = 2^13*2^51 by norm_num, Nat.mul_comm, Nat.mul_mod_mul_left,
        show (2:Nat)^13*(W.toNat%2^51) = 4096*(2*(W.toNat%2^51)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
    rw [this]; ring
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
theorem g9_cell (u : Nat) (hu : u ≤ 62) : BitVec.ofNat 64 (8192*(63-u)+256)=pcOf (cellW 9 (2*u)) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
theorem g9_fault : (BitVec.ofNat 64 (8192*(63-63)+256)).toNat<0x1000 := by decide +kernel
theorem prologue_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 12).toNat) &&& 520192#64)+BitVec.ofNat 64 (1168)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat%128)+1168) := by
  have hm := word_mask12 W 0 (by decide +kernel)
  simp only [shiftWord12, show (0 : Nat) < 12 from by omega, if_true,
    Nat.sub_zero, Nat.pow_zero, Nat.div_one] at hm
  change ((W <<< 12 &&& 520192#64) + BitVec.ofNat 64 (1168)) &&& ~~~1#64 = _
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
/-! ### T51 dispatch arithmetic (ported from R6)
g0 (prologue): `slli a4,a6,56; srli a4,a4,45; jalr -744(a4)` lands on `cell6 0 raw` (raw = a6 % 256 >= 3), below the
code start (raw = 1, 2) or far above it (raw = 0).  r6 groups 1..8: `a4 = field & 0xFF00 = 256 raw`, table B
(g1..g3, g8) `s2 - a4`, table A `a4 + s2`, `jalr` to `cell6 h raw`.  Checksum: `((s8 + 89) << 11) + 1168` with
`s8 = T - ds` (T = 152, ds <= 231) lands on `ckWord ds`. -/
/-- The g0 dispatch shift pair `slli a4,a6,56; srli a4,a4,45`: `2048 * (a6 % 256)`. -/
theorem g0_shift (W : Word) : (W <<< 56) >>> 45 = BitVec.ofNat 64 (2048 * (W.toNat % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have hW := W.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2048 * (W.toNat % 256) < 2^64 by omega)]
  rw [show (2:Nat)^64 = 2^56 * 2^8 by norm_num, Nat.mul_comm W.toNat, Nat.mul_mod_mul_left,
    show (2:Nat)^56 = 2^45 * 2048 by norm_num, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  norm_num
/-- The g0 dispatch target (jalr -744) for a field value `raw >= 1`. -/
theorem g0_target (W : Word) (raw : Nat) (hr : W.toNat % 256 = raw) (h1 : 1 ≤ raw) :
    (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64 = BitVec.ofNat 64 (2048 * raw - 744) := by
  have hr' : raw < 256 := by omega
  have e : BitVec.ofNat 64 (2048 * raw) + BitVec.ofNat 64 (2^64-744) = BitVec.ofNat 64 (2048 * raw - 744) := by
    rw [ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [g0_shift, hr, e, even_andNot1' _ (by omega)]
theorem g0_cell (raw : Nat) (h3 : 3 ≤ raw) : BitVec.ofNat 64 (2048 * raw - 744) = pcOf (cell6 0 raw) := by
  unfold pcOf cell6; simp only [if_true]; congr 1; omega
theorem g0_low (raw : Nat) (h3 : raw < 3) : (BitVec.ofNat 64 (2048 * raw - 744)).toNat < 0x1000 := by
  simp only [BitVec.toNat_ofNat]; omega
/-- Field value 0: the target `2^64 - 744` lies far above the code. -/
theorem g0_target0 (W : Word) (hr : W.toNat % 256 = 0) :
    0x1000 + 4 * 257280 ≤ ((((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64).toNat := by
  rw [g0_shift, hr, Nat.mul_zero, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  simp only [BitVec.toNat_ofNat]; omega
theorem land_mask8 (n : Nat) : n &&& (256*(2^8-1)) = 256*(n/256%2^8) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (256 : Nat)=2^8 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : 8 ≤ j
  · simp only [h, decide_true, Bool.true_and, show j-8+8=j by omega]
    by_cases hj : j-8<8 <;> simp [hj]
  · simp [h]
/-- `X &&& 0xFF00 = 256 * (X / 2^8 % 256)`. -/
theorem word_ff00 (X : Word) : X &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^8 % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : X.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [BitVec.toNat_and, show (65280#64).toNat = 256*(2^8-1) by rfl, land_mask8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 256 * (X.toNat / 2^8 % 256)) (by omega)]
  norm_num
/-- `(X >>> s) &&& 0xFF00 = 256 * (X / 2^(s+8) % 256)`. -/
theorem field_ff00 (X : Word) (s : Nat) :
    (X >>> s) &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^(s+8) % 256)) := by
  rw [word_ff00, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
theorem s2_sub (r : Nat) (hr : r < 256) :
    856064#64 - BitVec.ofNat 64 (256*r) = BitVec.ofNat 64 (856064-256*r) := by
  rw [BitVec.sub_eq_iff_eq_add, ofNat_add_ofNat]
  congr 1; omega
/-- Table B target (r6 groups 1..3): `s2 - 256 raw + (4 off - 256)`. -/
theorem tabB_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((856064#64 - BitVec.ofNat 64 (256*r)) + BitVec.ofNat 64 (2^64+4*o-256)) &&& ~~~1#64 =
      pcOf (64*(3327-r)+o) := by
  rw [s2_sub r hr, ofNat_add_ofNat]
  have e : BitVec.ofNat 64 (856064-256*r+(2^64+4*o-256)) = BitVec.ofNat 64 (856064-256*r+4*o-256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [e, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
/-- Table A target (r6 groups 4..7): `256 raw + s2 + 4 off`. -/
theorem tabA_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((BitVec.ofNat 64 (256*r) + 856064#64) + BitVec.ofNat 64 (4*o)) &&& ~~~1#64 =
      pcOf (64*(3328+r)+o) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
theorem ck_s8 (ds : Nat) (hd : ds ≤ 231) :
    (BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64 = BitVec.ofNat 64 (241-ds) := by
  rw [BitVec.ofNat_sub_ofNat, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [topT, BitVec.toNat_ofNat]
  omega
/-- The checksum dispatch target `(((s8 + 89) << 11) + 1168) & ~1` for s8 = T - ds, ds <= 231. -/
theorem ck_target (ds : Nat) (hd : ds ≤ 231) :
    ((((BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64) <<< 11) + 1168#64) &&& ~~~1#64 =
      pcOf (ckWord ds) := by
  have e2 : BitVec.ofNat 64 (241-ds) <<< 11 = BitVec.ofNat 64 (2048*(241-ds)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  rw [ck_s8 ds hd, e2, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf ckWord topT; congr 1; omega
/-- The r6 field read by the dispatch into group `h` (1..8): bits `8h..8h+7` (h < 7), `112..119` (g7),
`120..127` (g8) (`= T3.r6Shift h`). -/
def r6Pos (h : Nat) : Nat := if h=7 then 112 else if h=8 then 120 else 8*h
theorem cell6_tab (h r : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) :
    cell6 h r = if r6B h then 64*(3327-r)+r6Off h else 64*(3328+r)+r6Off h := by
  unfold cell6; rw [if_neg (by omega)]
theorem r6Off_lt (h : Nat) : r6Off h < 64 := by unfold r6Off; omega
end SigGolfCandidate.T3M.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsCheckParts ====
section

namespace SigGolfCandidate.T3M.Nonbinary
/-- Join bounded kernel computations without normalizing an entire closed code window. -/
theorem check_range_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem tripleCheck_join {q : Nat}
    (hent : (List.range' 0 (nRank q)).all (fun k => entCheck q k && s8Check q k) = true)
    (hblock : (List.range' 0 (nBlock q)).all (liveBlock q) = true) :
    tripleCheck q = true := by
  unfold tripleCheck
  rw [List.range_eq_range', List.range_eq_range', hent, hblock]
  rfl
end SigGolfCandidate.T3M.Nonbinary
end
