import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafTest
import SigGolfCandidate.ClaudeWCT.Arith.FamilyTest
import SigGolfCandidate.ClaudeWCT.WCT9.LowerReveal

/-! # The per-chain seed-test reduction (campaign X1 stage B, step B3)

For a lower source chain `a` of leaf `L` and fixed rest tables `R` (chain depth `d ≥ 1`), the prefix-game run in
the world where `L`'s step-0 rows and `a`'s prefix tables are programmed at the seeds is the test program
`testRun` run against the seeds:

* frozen world (the reference game, `a`'s seed is the family value): `frozen_point`, seeds `seedsY K`;
* mixture world (`a`'s seed independent): `mix_point`, seeds `seedsH aF K s`.

The honest part is the canonical table `Tst` (coefficients `Kst r` interpolating the revealed seeds), by
`leafCongr_prog`. -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafCore : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth prT amLen seedsY seedsR
  seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
variable {adversary : AdversaryP}

/-- Evaluation points of the chains of a leaf (`i + 1`). -/
def ptL (L : LeafAddr) : Fin (chainCount L.lay) → ℕ := fun c => c.val + 1

/-- The free parameters of the programmed world: `L`'s step-0 row functions and labels, `a`'s prefix tables and
labels. -/
abbrev PData (L : LeafAddr) (d : Nat) :=
  ((Fin (chainCount L.lay) → Digest → Digest) × (Fin (chainCount L.lay) → Digest)) ×
    ((Fin d → Digest → Digest) × (Fin d → Digest))
/-- Test-program parameters from the free parameters and the revealed seeds. -/
def mkP {L : LeafAddr} {d : Nat} (p : PData L d) (r : Fin (chainCount L.lay) → Digest) : TParams L d :=
  ⟨p.1.1, p.1.2, p.2.1, p.2.2, r⟩

theorem tY_mkP {L : LeafAddr} {d : Nat} (p : PData L d) (r r' : Fin (chainCount L.lay) → Digest) :
    tY L d (mkP p r) = tY L d (mkP p r') := rfl

/-- The endpoint of the programmed prefix tables: independent of the seed they are programmed at. -/
theorem evaluate_tY {L : LeafAddr} {d : Nat} (hd : 1 ≤ d) (P : TParams L d) (σ : Digest) :
    evaluate (tY L d P σ) σ = evaluate (tY L d P 0) 0 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [evaluate]
  have h1 : Fin.tail (tY L (d' + 1) P σ) = Fin.tail (tY L (d' + 1) P 0) := by
    funext i v
    simp only [Fin.tail, tY, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : tY L (d' + 1) P σ 0 σ = tY L (d' + 1) P 0 0 0 := by
    simp only [tY, Fin.val_zero, if_true, Function.update_self]
  rw [h1, h2]

section Point
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
include haL hac hd1

/-- The prefix game's oracle world reads `L`'s step-0 rows only off chain `a` (whose step-0 row is a prefix row). -/
theorem routeImpl_congr (K K' : Fin (WCT9.famCount L.lay) → Digest) (f f' : Fin (chainCount L.lay) → Digest → Digest)
    (hf : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → f c = f' c) :
    PrefixGame.routeImpl a (restDepth a R) (ovL L R (K, f)) =
      PrefixGame.routeImpl a (restDepth a R) (ovL L R (K', f')) := by
  funext q
  rcases q with (n | input) | u
  · simp only [PrefixGame.routeImpl]
  · simp only [PrefixGame.routeImpl]
    cases hp : PrefixGame.rowOf a (restDepth a R) input with
    | some p => simp only [high_ovL]
    | none =>
        simp only
        congr 1
        cases hz : zeroOf L input with
        | none => rw [restTable_ovL_pub L R _ input hz, restTable_ovL_pub L R _ input hz]
        | some cv =>
            have he := zeroOf_some hz
            have hca : cv.1.val ≠ a.chain := by
              intro hca
              apply PrefixGame.rowOf_none hp (⟨0, hd1⟩, cv.2)
              rw [he]
              subst haL
              simp only
              rw [hca]
            rw [he, restTable_ovL_zero, restTable_ovL_zero]
            simp only
            rw [hf cv.1 hca]
  · simp only [PrefixGame.routeImpl]

end Point

section Canon
variable (L : LeafAddr) (a : ChainAddr) (R : RefTables adversary)

/-- A family with the given revealed seeds (any one, if it exists). -/
noncomputable def Kst (r : Fin (chainCount L.lay) → Digest) : Fin (WCT9.famCount L.lay) → Digest :=
  if h : ∃ K, seedsR (ptL L) (revSet L R) K = r then h.choose else 0

theorem seedsR_Kst (K : Fin (WCT9.famCount L.lay) → Digest) :
    seedsR (ptL L) (revSet L R) (Kst L R (seedsR (ptL L) (revSet L R) K)) = seedsR (ptL L) (revSet L R) K := by
  unfold Kst
  rw [dif_pos ⟨K, rfl⟩]
  exact (⟨K, rfl⟩ : ∃ K', seedsR (ptL L) (revSet L R) K' = seedsR (ptL L) (revSet L R) K).choose_spec

/-- The endpoint of the programmed prefix tables. -/
def eP {d : Nat} (p : PData L d) : Digest := evaluate (tY L d (mkP p 0) 0) 0

/-- The canonical honest table: coefficients `Kst r`, step-0 rows programmed at their seeds. -/
noncomputable def Tst (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) : Answers :=
  PrefixGame.fillTable a (ovL L R (Kst L R r, progF p.1.1 p.1.2 (Kst L R r))) (eP L p)

variable {L a R}
/-- The seed-test program. -/
noncomputable def testRun {Res : Type} (GD : Answers → OracleComp RefWorld Res)
    (aF : Free (revSet L R)) (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) :
    OracleComp (TSpec (Free (revSet L R)) Digest) (Res × TObs (restDepth a R)) :=
  (simulateQ (testImpl L a (restDepth a R) R (revSet L R) aF (mkP p r)) (GD (Tst L a R p r))).run
    (fun _ _ => none)
end Canon

section Points
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', LeafCongr L T T' → GD T' = GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain)
include haL hac hLleaf hd1 hG haF

theorem seedOf_eq_seedsY (K : Fin (WCT9.famCount L.lay) → Digest) (i : Free (revSet L R)) :
    seedOf K i.1.val = seedsY (ptL L) (revSet L R) K i := rfl

/-- The honest game of the programmed world is the canonical one. -/
theorem GD_prog (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) :
    GD (PrefixGame.fillTable a (ovL L R (K, progF p.1.1 p.1.2 K)) (eP L p)) =
      GD (Tst L a R p (seedsR (ptL L) (revSet L R) K)) := by
  unfold Tst
  refine (hG _ _ (leafCongr_prog hLleaf haL hac R hd1 p.1.1 p.1.2 K _ (fun c hc => ?_) (eP L p))).symm
  have h := congrFun (seedsR_Kst L R K) c
  unfold seedsR at h
  have hc' : c ∈ revSet L R := by unfold revSet; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
  simp only [if_pos hc'] at h
  exact h.symm

/-- **Frozen world = test program against the family seeds.** -/
theorem frozen_point (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (tY L (restDepth a R) (mkP p 0) (seedOf K a.chain))
        (simulateQ (PrefixGame.routeImpl a (restDepth a R) (ovL L R (K, progF p.1.1 p.1.2 K)))
          (GD (PrefixGame.fillTable a (ovL L R (K, progF p.1.1 p.1.2 K)) (eP L p)))) (fun _ _ => none) =
      evalT (seedsY (ptL L) (revSet L R) K) (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) := by
  rw [GD_prog haL hac hLleaf R hd1 GD hG aF haF K p]
  unfold testRun
  rw [evalT_testRun R aF (mkP p (seedsR (ptL L) (revSet L R) K)) (seedsY (ptL L) (revSet L R) K) K]
  have hfy : fY L (restDepth a R) (revSet L R) (mkP p (seedsR (ptL L) (revSet L R) K))
      (seedsY (ptL L) (revSet L R) K) = progF p.1.1 p.1.2 K := by
    funext c
    unfold fY progF mkP
    simp only
    split_ifs with hc
    · unfold seedsR
      rw [if_pos hc]
      rfl
    · rfl
  have hya : seedsY (ptL L) (revSet L R) K aF = seedOf K a.chain := by
    rw [← seedOf_eq_seedsY haL hac hLleaf R hd1 GD hG aF haF, haF]
  rw [hfy, hya, tY_mkP p (seedsR (ptL L) (revSet L R) K) 0]

/-- **Mixture world = test program against the hybrid seeds.** -/
theorem mix_point (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) (s : Digest) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L (restDepth a R) (mkP p 0) s)
        (simulateQ (PrefixGame.routeImpl a (restDepth a R) (ovL L R (K, progF p.1.1 p.1.2 K)))
          (GD (PrefixGame.fillTable a (ovL L R (K, progF p.1.1 p.1.2 K)) (eP L p)))) (fun _ _ => none) =
      evalT (seedsH (ptL L) (revSet L R) aF K s) (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) := by
  rw [GD_prog haL hac hLleaf R hd1 GD hG aF haF K p]
  unfold testRun
  rw [evalT_testRun R aF (mkP p (seedsR (ptL L) (revSet L R) K)) (seedsH (ptL L) (revSet L R) aF K s) K]
  have hya : seedsH (ptL L) (revSet L R) aF K s aF = s := by unfold seedsH; rw [if_pos rfl]
  rw [hya, tY_mkP p (seedsR (ptL L) (revSet L R) K) 0,
    routeImpl_congr haL hac R hd1 K K _ (fY L (restDepth a R) (revSet L R) (mkP p (seedsR (ptL L) (revSet L R) K))
      (seedsH (ptL L) (revSet L R) aF K s))]
  intro c hca
  funext v
  unfold fY progF mkP
  simp only
  split_ifs with hc
  · unfold seedsR
    rw [if_pos hc]
    rfl
  · have hne : (⟨c, hc⟩ : Free (revSet L R)) ≠ aF := by
      intro h
      apply hca
      rw [← haF, ← h]
    unfold seedsH
    rw [if_neg hne]
    rfl
end Points

/-! ### The frozen and mixture laws of one rest table -/

/-- The prefix game of chain `a` at depth `d` with honest body `GD`. -/
noncomputable def gameD {Res : Type} (a : ChainAddr) (d : Nat) (R' : RefTables adversary)
    (GD : Answers → OracleComp RefWorld Res) (e : Digest) : OracleComp (PrefixGame.SeedSpec d) Res :=
  simulateQ (PrefixGame.routeImpl a d R') (GD (PrefixGame.fillTable a R' e))

/-- The reference game for chain `a` as a mixture over its prefix tables, seed frozen at `ovSeed`. -/
noncomputable def frozenLaw {Res : Type} (a : ChainAddr) (d : Nat) (R' : RefTables adversary)
    (GD : Answers → OracleComp RefWorld Res) : PMF (Digest × (Res × TObs d)) :=
  (PMF.uniformOfFintype (Hidden d)).bind (fun x =>
    (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (gameD a d R' GD (evaluate x.1 (PrefixGame.ovSeed a R' x.2))) (fun _ _ => none)).map
      (fun res => (evaluate x.1 (PrefixGame.ovSeed a R' x.2), res)))

/-- The `realRun` mixture (independent seed). -/
noncomputable def mixLaw {Res : Type} (a : ChainAddr) (d : Nat) (R' : RefTables adversary)
    (GD : Answers → OracleComp RefWorld Res) : PMF (Digest × (Res × TObs d)) :=
  SphincsSecurity.Concrete.PartialChainEndpoint.realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
    (gameD a d R' GD) (fun _ _ => none)

theorem ovSeed_ovL {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hLleaf : L.leaf < 2 ^ 24)
    (R : RefTables adversary) (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest)
    (s : Digest) : PrefixGame.ovSeed a (ovL L R (K, f)) s = seedOf K a.chain := by
  unfold PrefixGame.ovSeed
  subst haL
  rw [wotsSeed_ovL hLleaf]
  rfl

theorem uniform_bind_const {α β : Type} [Fintype α] [Nonempty α] (p : PMF β) :
    (PMF.uniformOfFintype α).bind (fun _ => p) = p := PMF.bind_const _ _

theorem uniform_prod_bind {α β γ : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (G : α × β → PMF γ) :
    (PMF.uniformOfFintype (α × β)).bind G =
      (PMF.uniformOfFintype α).bind (fun x => (PMF.uniformOfFintype β).bind (fun y => G (x, y))) := by
  rw [SigGolfCandidate.T3.Security.Wots.PrefixGame.uniform_prod, PMF.bind_bind]
  congr 1
  funext x
  rw [PMF.bind_map]
  rfl

section Decomp
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', LeafCongr L T T' → GD T' = GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain)
include haL hac hLleaf hd1 hG haF

/-- **Frozen law, decomposed.** -/
theorem frozen_decomp :
    (PMF.uniformOfFintype (LeafData L)).bind (fun y => frozenLaw a (restDepth a R) (ovL L R y) GD) =
      (PMF.uniformOfFintype (Fin (WCT9.famCount L.lay) → Digest)).bind (fun K => (PMF.uniformOfFintype (PData L (restDepth a R))).bind
        (fun p => (evalT (seedsY (ptL L) (revSet L R) K) (testRun GD aF p (seedsR (ptL L) (revSet L R) K))).map
          (fun res => (eP L p, res)))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  -- the frozen law of `ovL L R (K, f)`: the seed component is a dummy
  have hfr : ∀ f, frozenLaw a (restDepth a R) (ovL L R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (gameD a (restDepth a R) (ovL L R (K, f)) GD (evaluate t (seedOf K a.chain))) (fun _ _ => none)).map
          (fun res => (evaluate t (seedOf K a.chain), res))) := by
    intro f
    unfold frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (restDepth a R)) =
      PMF.uniformOfFintype ((Fin (restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovL haL hLleaf R K f]
    exact uniform_bind_const _
  simp only [hfr]
  rw [uniform_program (fun c : Fin (chainCount L.lay) => seedOf K c.val)]
  conv_rhs => rw [show PMF.uniformOfFintype (PData L (restDepth a R)) = PMF.uniformOfFintype
    (((Fin (chainCount L.lay) → Digest → Digest) × (Fin (chainCount L.lay) → Digest)) ×
      ((Fin (restDepth a R) → Digest → Digest) × (Fin (restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (restDepth a R) => if i.val = 0 then seedOf K a.chain else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (restDepth a R) => Function.update (q.1 i) (if i.val = 0 then seedOf K a.chain else 0) (q.2 i)) =
      tY L (restDepth a R) (mkP (gl, q) 0) (seedOf K a.chain) := rfl
  have he : evaluate (tY L (restDepth a R) (mkP (gl, q) 0) (seedOf K a.chain)) (seedOf K a.chain) = eP L (gl, q) :=
    evaluate_tY hd1 _ _
  rw [ht, he]
  unfold gameD
  have hp := frozen_point haL hac hLleaf R hd1 GD hG aF haF K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Frozen law with the leaf data, decomposed.** -/
theorem frozen_decompY :
    (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (frozenLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (WCT9.famCount L.lay) → Digest)).bind (fun K => (PMF.uniformOfFintype (PData L (restDepth a R))).bind
        (fun p => (evalT (seedsY (ptL L) (revSet L R) K) (testRun GD aF p (seedsR (ptL L) (revSet L R) K))).map
          (fun res => (((K, progF p.1.1 p.1.2 K) : LeafData L), (eP L p, res))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hfr : ∀ f, frozenLaw a (restDepth a R) (ovL L R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (gameD a (restDepth a R) (ovL L R (K, f)) GD (evaluate t (seedOf K a.chain))) (fun _ _ => none)).map
          (fun res => (evaluate t (seedOf K a.chain), res))) := by
    intro f
    unfold frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (restDepth a R)) =
      PMF.uniformOfFintype ((Fin (restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovL haL hLleaf R K f]
    exact uniform_bind_const _
  simp only [hfr, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : Fin (chainCount L.lay) => seedOf K c.val)]
  conv_rhs => rw [show PMF.uniformOfFintype (PData L (restDepth a R)) = PMF.uniformOfFintype
    (((Fin (chainCount L.lay) → Digest → Digest) × (Fin (chainCount L.lay) → Digest)) ×
      ((Fin (restDepth a R) → Digest → Digest) × (Fin (restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (restDepth a R) => if i.val = 0 then seedOf K a.chain else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (restDepth a R) => Function.update (q.1 i) (if i.val = 0 then seedOf K a.chain else 0) (q.2 i)) =
      tY L (restDepth a R) (mkP (gl, q) 0) (seedOf K a.chain) := rfl
  have he : evaluate (tY L (restDepth a R) (mkP (gl, q) 0) (seedOf K a.chain)) (seedOf K a.chain) = eP L (gl, q) :=
    evaluate_tY hd1 _ _
  rw [ht, he]
  unfold gameD
  have hp := frozen_point haL hac hLleaf R hd1 GD hG aF haF K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Mixture law with the leaf data, decomposed.** -/
theorem mix_decompY :
    (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (mixLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (WCT9.famCount L.lay) → Digest)).bind (fun K => (PMF.uniformOfFintype (PData L (restDepth a R))).bind
        (fun p => (PMF.uniformOfFintype Digest).bind (fun s =>
          (evalT (seedsH (ptL L) (revSet L R) aF K s) (testRun GD aF p (seedsR (ptL L) (revSet L R) K))).map
            (fun res => (((K, progF p.1.1 p.1.2 K) : LeafData L), (eP L p, res)))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hmx : ∀ f, mixLaw a (restDepth a R) (ovL L R (K, f)) GD =
      (PMF.uniformOfFintype Digest).bind (fun s => (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind
        (fun t => (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (gameD a (restDepth a R) (ovL L R (K, f)) GD (evaluate t s)) (fun _ _ => none)).map
          (fun res => (evaluate t s, res)))) := by
    intro f
    unfold mixLaw
    simp only [SphincsSecurity.Concrete.PartialChainEndpoint.realRun,
      SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
      SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
      PMF.map_comp, Function.comp_def]
    rw [PMF.bind_comm]
  simp only [hmx, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : Fin (chainCount L.lay) => seedOf K c.val)]
  conv_rhs => rw [show PMF.uniformOfFintype (PData L (restDepth a R)) = PMF.uniformOfFintype
    (((Fin (chainCount L.lay) → Digest → Digest) × (Fin (chainCount L.lay) → Digest)) ×
      ((Fin (restDepth a R) → Digest → Digest) × (Fin (restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext s
  rw [uniform_program (fun i : Fin (restDepth a R) => if i.val = 0 then s else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (restDepth a R) => Function.update (q.1 i) (if i.val = 0 then s else 0) (q.2 i)) =
      tY L (restDepth a R) (mkP (gl, q) 0) s := rfl
  have he : evaluate (tY L (restDepth a R) (mkP (gl, q) 0) s) s = eP L (gl, q) := evaluate_tY hd1 _ _
  rw [ht, he]
  unfold gameD
  have hp := mix_point haL hac hLleaf R hd1 GD hG aF haF K (gl, q) s
  exact congrArg (PMF.map _) hp
end Decomp

/-! ### Revealed chains -/

theorem card_filter_getD_zero : ∀ (l : List ℕ),
    (Finset.univ.filter (fun c : Fin l.length => l.getD c 0 = 0)).card = (l.filter (· = 0)).length
  | [] => rfl
  | x :: xs => by
      show (Finset.univ.filter (fun c : Fin (xs.length + 1) => (x :: xs).getD c 0 = 0)).card = _
      rw [Fin.card_filter_univ_succ']
      have ih := card_filter_getD_zero xs
      simp only [List.length_cons, Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ] at ih ⊢
      rw [ih, List.filter_cons]
      by_cases hx : x = 0
      · simp [hx, add_comm]
      · simp [hx]

theorem card_filter_getD_zero' (n : ℕ) (l : List ℕ) (hl : l.length = n) :
    (Finset.univ.filter (fun c : Fin n => l.getD c 0 = 0)).card = (l.filter (· = 0)).length := by
  subst hl
  exact card_filter_getD_zero l

theorem dummyDigits_zero (lay : Layer) : ((dummyDigits lay).filter (· = 0)).length = 0 := by
  fin_cases lay <;> decide

/-- **Revealed chains per leaf**: at most `famCount − 3` (campaign T8D: ≤ 20 of the 54 top chains with 24 top
coefficients, `top_zero_count_le`; ≤ 14 of the 43 lower chains with 17 coefficients, `lower_zero_count_le`), so every
unrevealed seed keeps 3 degrees of freedom. -/
theorem revSet_card_le {L : LeafAddr} (R : RefTables adversary) :
    (revSet L R).card + 3 ≤ WCT9.famCount L.lay := by
  unfold revSet
  have hspec := (Mask.referenceDigits_spec (restTable R) L).1
  have e : (Finset.univ.filter fun c : Fin (chainCount L.lay) => depth (restTable R) ⟨L, c⟩ = 0) =
      Finset.univ.filter fun c : Fin (chainCount L.lay) => (referenceDigits (restTable R) L).getD c 0 = 0 := rfl
  rw [e, card_filter_getD_zero' _ _ hspec]
  have hN := WCT9.famCount_ge L.lay
  unfold referenceDigits
  cases h : referenceSearch (restTable R) L with
  | none => simp only [Option.map_none, Option.getD_none]; rw [dummyDigits_zero]; omega
  | some found =>
      obtain ⟨counter, digits⟩ := found
      simp only [Option.map_some, Option.getD_some]
      have hd := (WCT9.layerCounterSearch_some (restTable R) L.lay L.tree L.leaf (leafMsg (restTable R) L)
        (WCT9.searchLimit L.lay) 0 counter digits (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) h).2.2
      by_cases h0 : L.lay = 0
      · rw [h0] at hd
        have := ClaudeWCT.WCT9.top_zero_count_le ClaudeWCT.WCT9.top_target_ge hd
        rw [show WCT9.famCount L.lay = 24 by rw [h0]; rfl]
        omega
      · have := ClaudeWCT.WCT9.lower_zero_count_le h0 (ClaudeWCT.WCT9.lower_target_ge _ h0) hd
        rw [show WCT9.famCount L.lay = 17 by unfold WCT9.famCount; rw [if_neg h0]; rfl]
        omega

/-! ### Probability bookkeeping -/

theorem prob_uniform_bind {α β : Type} [Fintype α] [Nonempty α] (g : α → PMF β) (E : β → Prop) :
    Pr[E | (PMF.uniformOfFintype α).bind g] = ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * Pr[E | g x] := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum, tsum_fintype]
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply]

theorem prob_pmf_map {α β : Type} (p : PMF α) (f : α → β) (E : β → Prop) : Pr[E | p.map f] = Pr[E ∘ f | p] := by
  rw [← PMF.monad_map_eq_map, probEvent_map]

theorem prob_evalT {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} (y : ι → Digest) (A : α → Prop)
    (oa : OracleComp (TSpec ι Digest) α) : Pr[A | evalT y oa] = ENNReal.ofReal (prT y A oa) := by
  classical
  rw [ClaudeWCT.Arith.SideChannel.ofReal_prT, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  rw [PMF.probOutput_eq_apply]
  split <;> simp

theorem inv_card_eq_ofReal (α : Type) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Fintype.card α : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]

theorem sum_inv_ofReal {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * ENNReal.ofReal (f x) =
      ENNReal.ofReal (∑ x, (Fintype.card α : ℝ)⁻¹ * f x) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (by positivity) (hf x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), inv_card_eq_ofReal]

/-! ### Real against mixture, one rest table -/

section PerR
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', LeafCongr L T T' → GD T' = GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)

include hGq in
theorem tdepth_testRun (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) :
    tdepth (testRun GD aF p r) ≤ q :=
  ClaudeWCT.Arith.SideChannel.tdepth_simulate_le _ RefCharged (fun qu s => tdepth_testImpl R aF _ qu s) _ q _
    (hGq _)

/-- The per-rest-table error: `2 δ K(q) E_{p,K}[amLen]`. -/
noncomputable def errR : ℝ :=
  ∑ p : PData L (restDepth a R), ∑ K : Fin (WCT9.famCount L.lay) → Digest,
    (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ * ((Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ *
      (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        amLen (testRun GD aF p (seedsR (ptL L) (revSet L R) K))))

include haL hac hLleaf hd1 hG haF hGq

theorem frozen_le_mix_R (E : LeafData L → Digest × (Res × TObs (restDepth a R)) → Prop)
    (hE : ∀ (p : PData L (restDepth a R)) (K K' : Fin (WCT9.famCount L.lay) → Digest),
      seedsR (ptL L) (revSet L R) K = seedsR (ptL L) (revSet L R) K' →
        E (K, progF p.1.1 p.1.2 K) = E (K', progF p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (frozenLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (mixLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errR (a := a) R GD aF q) := by
  rw [frozen_decompY haL hac hLleaf R hd1 GD hG aF haF, mix_decompY haL hac hLleaf R hd1 GD hG aF haF]
  set A : PData L (restDepth a R) → (Fin (chainCount L.lay) → Digest) → (Res × TObs (restDepth a R)) → Prop :=
    fun p r res => E (Kst L R r, progF p.1.1 p.1.2 (Kst L R r)) (eP L p, res) with hAdef
  have hA : ∀ (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)),
      (fun res => E (K, progF p.1.1 p.1.2 K) (eP L p, res)) = A p (seedsR (ptL L) (revSet L R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_Kst L R K).symm]
  set tr := fun (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) => testRun GD aF p r with htr
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : (revSet L R).card + 3 ≤ WCT9.famCount L.lay := revSet_card_le R
  have hpt : Function.Injective (ptL L) := fun c c' h => Fin.ext (by unfold ptL at h; omega)
  have hsmall : ∀ c, ptL L c < 1024 := fun c => by
    unfold ptL; have := c.isLt; have := chainCount_le L.lay; omega
  -- convert to real sums
  rw [show (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K))
          (testRun GD aF p (seedsR (ptL L) (revSet L R) K)))) =
      ENNReal.ofReal (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ *
        ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K))
            (testRun GD aF p (seedsR (ptL L) (revSet L R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set C : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) =>
    prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K)) (testRun GD aF p (seedsR (ptL L) (revSet L R) K))
    with hx
  set z := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) (s : Digest) =>
    prT (seedsH (ptL L) (revSet L R) aF K s) (A p (seedsR (ptL L) (revSet L R) K))
      (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) with hz
  set m := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) =>
    amLen (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))
  have hZ : 0 ≤ errR (a := a) R GD aF q := by
    unfold errR
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PData L (restDepth a R), ∑ K, x K p ≤
      ∑ K, (∑ s, z K p s) / Fintype.card Digest + C * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_le hpt hsmall hRev aF (A p)
      (fun r => testRun GD aF p r) q (fun r => tdepth_testRun R GD aF q hGq p r)
  have e1 : ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * x K p =
      ∑ p : PData L (restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PData L (restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errR (a := a) R GD aF q = ∑ p : PData L (restDepth a R), (cK * cp) * (C * ∑ K, m K p) := by
    unfold errR
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)
theorem mix_le_frozen_R (E : LeafData L → Digest × (Res × TObs (restDepth a R)) → Prop)
    (hE : ∀ (p : PData L (restDepth a R)) (K K' : Fin (WCT9.famCount L.lay) → Digest),
      seedsR (ptL L) (revSet L R) K = seedsR (ptL L) (revSet L R) K' →
        E (K, progF p.1.1 p.1.2 K) = E (K', progF p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (mixLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (LeafData L)).bind
        (fun y => (frozenLaw a (restDepth a R) (ovL L R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errR (a := a) R GD aF q) := by
  rw [frozen_decompY haL hac hLleaf R hd1 GD hG aF haF, mix_decompY haL hac hLleaf R hd1 GD hG aF haF]
  set A : PData L (restDepth a R) → (Fin (chainCount L.lay) → Digest) → (Res × TObs (restDepth a R)) → Prop :=
    fun p r res => E (Kst L R r, progF p.1.1 p.1.2 (Kst L R r)) (eP L p, res) with hAdef
  have hA : ∀ (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)),
      (fun res => E (K, progF p.1.1 p.1.2 K) (eP L p, res)) = A p (seedsR (ptL L) (revSet L R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_Kst L R K).symm]
  set tr := fun (p : PData L (restDepth a R)) (r : Fin (chainCount L.lay) → Digest) => testRun GD aF p r with htr
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : (revSet L R).card + 3 ≤ WCT9.famCount L.lay := revSet_card_le R
  have hpt : Function.Injective (ptL L) := fun c c' h => Fin.ext (by unfold ptL at h; omega)
  have hsmall : ∀ c, ptL L c < 1024 := fun c => by
    unfold ptL; have := c.isLt; have := chainCount_le L.lay; omega
  -- convert to real sums
  rw [show (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K))
          (testRun GD aF p (seedsR (ptL L) (revSet L R) K)))) =
      ENNReal.ofReal (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ *
        ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K))
            (testRun GD aF p (seedsR (ptL L) (revSet L R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set C : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) =>
    prT (seedsY (ptL L) (revSet L R) K) (A p (seedsR (ptL L) (revSet L R) K)) (testRun GD aF p (seedsR (ptL L) (revSet L R) K))
    with hx
  set z := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) (s : Digest) =>
    prT (seedsH (ptL L) (revSet L R) aF K s) (A p (seedsR (ptL L) (revSet L R) K))
      (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) with hz
  set m := fun (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)) =>
    amLen (testRun GD aF p (seedsR (ptL L) (revSet L R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (WCT9.famCount L.lay) → Digest, (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PData L (restDepth a R), (Fintype.card (PData L (restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * x K p :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))
  have hZ : 0 ≤ errR (a := a) R GD aF q := by
    unfold errR
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PData L (restDepth a R), ∑ K, (∑ s, z K p s) / Fintype.card Digest ≤
      ∑ K, x K p + C * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_ge hpt hsmall hRev aF (A p)
      (fun r => testRun GD aF p r) q (fun r => tdepth_testRun R GD aF q hGq p r)
  have e1 : ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * x K p =
      ∑ p : PData L (restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * ∑ p : PData L (restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PData L (restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errR (a := a) R GD aF q = ∑ p : PData L (restDepth a R), (cK * cp) * (C * ∑ K, m K p) := by
    unfold errR
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e2, e1, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)
end PerR

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
