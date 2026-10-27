import SigGolfCandidate.Merge019
import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge107

-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafCore ====
section

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
    | some p =>
        simp only
        have hp256 : (p.1 : Nat) < 256 := by have := p.1.isLt; have := PrefixGame.restDepth_le a R; omega
        have hc24 : a.chain < 2 ^ 24 :=
          lt_of_lt_of_le hac (le_trans (SigGolfCandidate.T3.chainCount_bound _) (by norm_num))
        rw [PrefixGame.rowOf_some hp, otherHalf_ovL L R _ _ _ _ hp256 hc24, otherHalf_ovL L R _ _ _ _ hp256 hc24]
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

/-- **Revealed chains per leaf**: at most `famCount − 3` (top, campaign T51: ≤ 21 of the 51 chains with 31
coefficients; B4 lower producer, including checksum and dummy fallback: ≤ 5 of the 43 chains with
8 coefficients), so every unrevealed seed keeps 3 degrees of freedom. The broad decoder is not narrowed. -/
theorem revSet_card_le {L : LeafAddr} (R : RefTables adversary) :
    (revSet L R).card + 3 ≤ WCT9.famCount L.lay := by
  unfold revSet
  have hspec := (Mask.referenceDigits_spec (restTable R) L).1
  have e : (Finset.univ.filter fun c : Fin (chainCount L.lay) => depth (restTable R) ⟨L, c⟩ = 0) =
      Finset.univ.filter fun c : Fin (chainCount L.lay) => (referenceDigits (restTable R) L).getD c 0 = 0 := rfl
  rw [e, card_filter_getD_zero' _ _ hspec]
  obtain ⟨value, hp⟩ := ClaudeWCT.W9.T3.Security.WotsExtract.referenceDigits_producerDecode (restTable R) L
  by_cases h0 : L.lay = 0
  · have hd := WCT9.producerDecode_decode hp
    rw [h0] at hd
    have := WCT9.top_zero_count_le WCT9.top_target_ge hd
    rw [h0, WCT9.famCount_top]
    omega
  · have := WCT9.lower_zero_count_le_producer h0 hp
    have := WCT9.famCount_ge L.lay
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

end PerR

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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL

noncomputable def revSet (L : LeafAddr) (R : Tables U) : Finset (Fin (chainCount L.lay)) :=
  Finset.univ.filter fun c => CanonicalRef.depth (raw R) zeroMessages ⟨L,c⟩=0
noncomputable def Kst (L : LeafAddr) (R : Tables U) (r : Fin (chainCount L.lay)→Digest) : Fin (WCT9.famCount L.lay)→Digest :=
  if h : ∃K,seedsR (ptL L) (revSet L R) K=r then h.choose else 0

theorem seedsR_Kst (L : LeafAddr) (R : Tables U) (K : Fin (WCT9.famCount L.lay)→Digest) :
    seedsR (ptL L) (revSet L R) (Kst L R (seedsR (ptL L) (revSet L R) K))=seedsR (ptL L) (revSet L R) K := by
  unfold Kst
  rw [dif_pos ⟨K,rfl⟩]
  exact (⟨K,rfl⟩ : ∃K',seedsR (ptL L) (revSet L R) K'=seedsR (ptL L) (revSet L R) K).choose_spec

noncomputable def Tst (L : LeafAddr) (a : ChainAddr) (R : Tables U)
    (p : PData L (RawPrefix.restDepth a R)) (r : Fin (chainCount L.lay)→Digest) : Answers :=
  answers hU (RawPrefix.fill a (RawLeaf.ovL L R (Kst L R r,progF p.1.1 p.1.2 (Kst L R r))) (eP L p))
noncomputable def testRun {L : LeafAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (GD : Answers→OracleComp RefWorld Res) (aF : Free (revSet L R))
    (p : PData L (RawPrefix.restDepth a R)) (r : Fin (chainCount L.lay)→Digest) :
    OracleComp (TSpec (Free (revSet L R)) Digest) (Res×TObs (RawPrefix.restDepth a R)) :=
  (simulateQ (Test.testImpl L a (RawPrefix.restDepth a R) (Tst hU L a R p r) (revSet L R) aF (mkP p r))
    (GD (Tst hU L a R p r))).run (fun _ _=>none)

section Points
variable {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L) {a : ChainAddr}
  (ha : a.key=L) (hac : a.chain<chainCount L.lay) (R : Tables U) (hd : 1≤RawPrefix.restDepth a R)
  {Res : Type} (GD : Answers→OracleComp RefWorld Res)
  (hG : ∀T T',CanonicalRef.Leaf.Congr (sourceMessages T) L T T'→GD T'=GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val=a.chain)
include hL ha hac hd hG

include haF

end Points

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput}

theorem revSet_card_le (L : LeafAddr) (R : Tables U) :
    (revSet L R).card+3≤WCT9.famCount L.lay := by
  unfold revSet
  change (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
    (CanonicalRef.referenceDigits (raw R) zeroMessages L).getD c 0=0).card+3≤_
  rw [card_filter_getD_zero' _ _ (CanonicalRef.referenceDigits_length (raw R) zeroMessages L)]
  cases hs : CanonicalRef.referenceSearch (raw R) zeroMessages L with
  | none =>
    simp only [CanonicalRef.referenceDigits,hs,Option.map_none,Option.getD_none,dummyDigits_zero,Nat.zero_add]
    have hc : ∀ lay : Layer,3≤WCT9.famCount lay := by intro lay;fin_cases lay <;> decide
    exact hc L.lay
  | some found =>
    obtain ⟨c,ds,lw⟩ := found
    have hd : ∃ floor lw' value,WCT9.CanonicalPolicy.producerDecodeAt L.lay floor lw' value=some ds := by
      obtain ⟨remaining, _, hs0⟩ := Option.bind_eq_some_iff.mp hs
      exact ⟨_,_,_,(WCT9.CanonicalPolicy.producerDecodeOut_spec (CanonicalRef.counterSearch_decode (raw R) L.lay _ L.tree L.leaf (zeroMessages L)
          (WCT9.searchLimit L.lay) 0 c (ds,lw) hs0)).2⟩
    simp only [CanonicalRef.referenceDigits,hs,Option.map_some,Option.getD_some]
    obtain ⟨floor,lw',value,hd⟩ := hd
    have hp := WCT9.CanonicalPolicy.producerDecodeAt_spec hd
    by_cases hz : L.lay=0
    · have hdec : decode 0 value=some ds := by
        simpa only [WCT9.CanonicalPolicy.decode,WCT9.CanonicalPolicy.normalLayer,hz,ite_true] using hp.1
      have hb := WCT9.top_zero_count_le WCT9.top_target_ge hdec
      rw [hz,WCT9.famCount_top]
      omega
    · have hb := hp.2.2.1
      simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_false] at hb
      have := WCT9.famCount_ge L.lay
      omega

/-- Today's producer zero caps per leaf: top 7 of 51 (T51), lower 5 of 43 (the family budgets `FamCaps.size_ge`). -/
theorem revSet_card_le_cap (L : LeafAddr) (R : Tables U) :
    (revSet L R).card ≤ if L.lay = 0 then 7 else 5 := by
  unfold revSet
  change (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
    (CanonicalRef.referenceDigits (raw R) zeroMessages L).getD c 0=0).card ≤ _
  rw [card_filter_getD_zero' _ _ (CanonicalRef.referenceDigits_length (raw R) zeroMessages L)]
  cases hs : CanonicalRef.referenceSearch (raw R) zeroMessages L with
  | none =>
    simp only [CanonicalRef.referenceDigits,hs,Option.map_none,Option.getD_none,dummyDigits_zero]
    exact Nat.zero_le _
  | some found =>
    obtain ⟨c,ds,low⟩ := found
    have hd : ∃ floor value,WCT9.CanonicalPolicy.producerDecodeAt L.lay floor low value=some ds := by
      obtain ⟨remaining, _, hs0⟩ := Option.bind_eq_some_iff.mp hs
      exact ⟨_,CanonicalRef.counterSearch_accepted (raw R) L.lay _ L.tree L.leaf (zeroMessages L)
          (WCT9.searchLimit L.lay) 0 c ds low hs0⟩
    simp only [CanonicalRef.referenceDigits,hs,Option.map_some,Option.getD_some]
    obtain ⟨floor,value,hd⟩ := hd
    have hp := WCT9.CanonicalPolicy.producerDecodeAt_spec hd
    -- T51: the producer's zero cap `producerZeroCap` is 7 on the top layer (4-leaf families of 31 coefficients)
    by_cases hz : L.lay=0
    · have hb := hp.2.2.1
      simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_true] at hb
      rw [if_pos hz]
      omega
    · have hb := hp.2.2.1
      simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_false] at hb
      rw [if_neg hz]
      omega

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL Tst
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem route_withPublic_congr {L : LeafAddr} {a : ChainAddr} (ha : a.key=L) {d : Nat} (hd : 1≤d)
    (B : Answers) (f f' : Fin (chainCount L.lay)→Digest→Digest)
    (hf : ∀c : Fin (chainCount L.lay),c.val≠a.chain→f c=f' c) :
    Route.routeImpl a d B (Test.withPublic L B f)=Route.routeImpl a d B (Test.withPublic L B f') := by
  funext query
  rcases query with (coin | input) | coord
  · simp only [Route.routeImpl]
  · simp only [Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p => rfl
    | none =>
      simp only [Test.withPublic,Test.publicAt]
      congr 1
      cases hz : zeroOf L input with
      | none => rfl
      | some cv =>
        simp only
        rw [hf cv.1 (by
          intro he
          apply PrefixGame.rowOf_none hp (⟨0,hd⟩,cv.2)
          rw [zeroOf_some hz]
          subst ha
          rw [he])]
  · simp only [Route.routeImpl]

section Points
variable {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L) {a : ChainAddr}
  (ha : a.key=L) (hac : a.chain<chainCount L.lay) (R : Tables U) (hd : 1≤RawPrefix.restDepth a R)
  {Res : Type} (GD : Answers→OracleComp RefWorld Res)
  (hG : ∀T T',CanonicalRef.Leaf.Congr (sourceMessages T) L T T'→GD T'=GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val=a.chain)
include hL ha hac hd hG haF

end Points
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

noncomputable def gameD {Res : Type} (a : ChainAddr) (d : Nat) (R' : Tables U)
    (GD : Answers→OracleComp RefWorld Res) (e : Digest) : OracleComp (PrefixGame.SeedSpec d) Res :=
  simulateQ (Route.routeImpl a d (answers hU R') (answers hU (RawPrefix.fill a R' e)))
    (GD (answers hU (RawPrefix.fill a R' e)))
noncomputable def frozenLaw {Res : Type} (a : ChainAddr) (d : Nat) (R' : Tables U)
    (GD : Answers→OracleComp RefWorld Res) : PMF (Digest×(Res×TObs d)) :=
  (PMF.uniformOfFintype (Hidden d)).bind fun x =>
    (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (gameD hU a d R' GD (evaluate x.1 (RawPrefix.ovSeed a R' x.2))) (fun _ _=>none)).map
      (fun res => (evaluate x.1 (RawPrefix.ovSeed a R' x.2),res))
noncomputable def mixLaw {Res : Type} (a : ChainAddr) (d : Nat) (R' : Tables U)
    (GD : Answers→OracleComp RefWorld Res) : PMF (Digest×(Res×TObs d)) :=
  SphincsSecurity.Concrete.PartialChainEndpoint.realRun (fun _=>SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
    (gameD hU a d R' GD) (fun _ _=>none)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

section Decomp
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hL : WotsExtract.SourceLeaf7 L) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) L T T' → GD T' = GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain)
include haL hac hL hd1 hG haF

end Decomp
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

open ClaudeWCT.Arith.SideChannel (tdepth prT amLen)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
section PerR
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hL : WotsExtract.SourceLeaf7 L) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (hG : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) L T T' → GD T' = GD T)
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)

include hGq in
theorem tdepth_testRun (p : PData L (RawPrefix.restDepth a R)) (r : Fin (chainCount L.lay) → Digest) :
    tdepth (testRun hU GD aF p r) ≤ q :=
  ClaudeWCT.Arith.SideChannel.tdepth_simulate_le _ RefCharged (fun qu s => Test.tdepth_testImpl (Tst hU L a R p r) aF _ qu s) _ q _
    (hGq _)

/-- The per-rest-table error: `2 δ K(q) E_{p,K}[amLen]`. -/
noncomputable def errR : ℝ :=
  ∑ p : PData L (RawPrefix.restDepth a R), ∑ K : Fin (WCT9.famCount L.lay) → Digest,
    (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ * ((Fintype.card (PData L (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
      (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        amLen (testRun hU GD aF p (seedsR (ptL L) (revSet L R) K))))

include haL hac hL hd1 hG haF hGq

end PerR
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Core
end
