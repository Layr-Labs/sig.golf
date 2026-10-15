import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafLift
import SigGolfCandidate.T3.Secc.WotsTwoEdge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraph

/-! # Summing the seed-test errors (campaign X1 stage B, step B3)

The error of chain `a` is charged to the expected number of test queries of its leaf (step-0 rows of unrevealed
chains): `errR · (1 - q/2^128) ≤ 2 δ K(q) · E[#tests]` (`family_amLen_le`), and the expected number of tests is
the expected number `N_L` of such queries in the reference experiment. -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafSum : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT exT enT amLen tdepth seedsY seedsR)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
open SphincsSecurity.QueryCap (recorded counted calls)
variable {adversary : AdversaryP}

theorem counted_recorded {ι α : Type} {spec : OracleSpec ι} (C : ι → Prop) [DecidablePred C]
    (G : OracleComp spec α) : counted C (recorded G) = (fun r => (r, calls C r.2)) <$> recorded G := by
  induction G using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.counted_bind,
        SphincsSecurity.QueryCap.counted_query]
      simp only [map_bind, bind_map_left, map_pure, bind_assoc]
      congr 1
      funext u
      rw [SphincsSecurity.QueryCap.counted_bind, ih u]
      simp only [bind_map_left, SphincsSecurity.QueryCap.counted_pure,
        SphincsSecurity.QueryCap.calls_cons, pure_bind, Nat.add_zero, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply]

theorem recorded_queryBound {ι α : Type} {spec : OracleSpec ι} (C : ι → Prop) [DecidablePred C]
    (G : OracleComp spec α) (n : ℕ) (h : OracleComp.IsQueryBoundP G C n) :
    OracleComp.IsQueryBoundP (recorded G) C n := by
  induction G using OracleComp.inductionOn generalizing n with
  | pure x => trivial
  | query_bind q k ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [SphincsSecurity.QueryCap.recorded_query_bind, OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun u => ?_⟩
      have := OracleComp.isQueryBoundP_bind (ob := fun r : α × List ι => (pure (r.1, q :: r.2) :
        OracleComp spec (α × List ι))) (m := 0) (ih u _ (h.2 u)) (fun _ _ => OracleComp.isQueryBoundP_pure C _ 0)
      rwa [Nat.add_zero] at this

theorem exT_map' {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (y : ι → Digest) (f : β → ℝ) (g : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : exT y f (g <$> oa) = exT y (f ∘ g) oa := by
  rw [map_eq_bind_pure_comp, ClaudeWCT.Arith.SideChannel.exT_bind]
  rfl

/-- Expected number of tests = expected number of test queries in the recorded list. -/
theorem enT_testRun_rec {L : LeafAddr} {a : ChainAddr} {R : RefTables adversary} {Res : Type}
    (G0 : Answers → OracleComp RefWorld Res) (aF : Free (revSet L R)) (p : PData L (restDepth a R))
    (r : Fin (chainCount L.lay) → Digest) (y : Free (revSet L R) → Digest) :
    enT y (testRun (fun T => recorded (G0 T)) aF p r) =
      exT y (fun out => (calls (isTestQ L a (restDepth a R) (revSet L R)) out.1.2 : ℝ))
        (testRun (fun T => recorded (G0 T)) aF p r) := by
  unfold testRun
  rw [enT_simulate y _ (isTestQ L a (restDepth a R) (revSet L R)) (fun q s => enT_testImpl R aF _ y q s),
    counted_recorded, simulateQ_map, StateT.run_map, exT_map']
  rfl

section ErrR
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', LeafCongr L T T' → recorded (G0 T') = recorded (G0 T))
  (aF : Free (revSet L R)) (haF : aF.1.val = a.chain) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)

/-- The test-query count of a run. -/
noncomputable def tcount (out : (Res × List RefWorld.Domain) × TObs (restDepth a R)) : ℕ :=
  calls (isTestQ L a (restDepth a R) (revSet L R)) out.1.2

include haL hac hLleaf hd1 hG haF hGq in
/-- **The error is charged to the expected test count.** -/
theorem errR_le_count :
    errR (a := a) R (fun T => recorded (G0 T)) aF q * (1 - (Fintype.card Digest : ℝ)⁻¹ * q) ≤
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        ∑ p : PData L (restDepth a R), ∑ K : Fin (WCT9.famCount L.lay) → Digest,
          (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ * ((Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ *
            exT (seedsY (ptL L) (revSet L R) K) (fun out => (tcount (L := L) (a := a) R out : ℝ))
              (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) := by
  have hRev : (revSet L R).card + 3 ≤ WCT9.famCount L.lay := revSet_card_le R
  have hpt : Function.Injective (ptL L) := fun c c' h => Fin.ext (by unfold ptL at h; omega)
  have hsmall : ∀ c, ptL L c < 1024 := fun c => by
    unfold ptL; have := c.isLt; have := chainCount_le L.lay; omega
  set C : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set cK : ℝ := (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹
  set cp : ℝ := (Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
    (Nat.cast_nonneg _)
  have hcK : 0 ≤ cK := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcp : 0 ≤ cp := inv_nonneg.mpr (Nat.cast_nonneg _)
  have e1 : errR (a := a) R (fun T => recorded (G0 T)) aF q =
      ∑ p : PData L (restDepth a R), (C * cK * cp) *
        ∑ K : Fin (WCT9.famCount L.lay) → Digest, amLen (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K)) := by
    unfold errR
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ p : PData L (restDepth a R), ∑ K : Fin (WCT9.famCount L.lay) → Digest, cK * (cp *
      exT (seedsY (ptL L) (revSet L R) K) (fun out => (tcount (L := L) (a := a) R out : ℝ))
        (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) =
      ∑ p : PData L (restDepth a R), (cK * cp) * ∑ K : Fin (WCT9.famCount L.lay) → Digest,
        enT (seedsY (ptL L) (revSet L R) K) (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => ?_
    rw [enT_testRun_rec]
    unfold tcount
    ring
  rw [e1, e2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hf := ClaudeWCT.Arith.SideChannel.family_amLen_le hpt hsmall hRev
    (fun r => testRun (fun T => recorded (G0 T)) aF p r) q
    (fun r => tdepth_testRun R (fun T => recorded (G0 T)) aF q hGq p r)
  calc C * cK * cp * (∑ K : Fin (WCT9.famCount L.lay) → Digest,
        amLen (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) *
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)
      = C * cK * cp * ((∑ K : Fin (WCT9.famCount L.lay) → Digest,
          amLen (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) *
          (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) := by ring
    _ ≤ C * cK * cp * ∑ K : Fin (WCT9.famCount L.lay) → Digest,
          enT (seedsY (ptL L) (revSet L R) K) (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K)) :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hC0 hcK) hcp)
    _ = C * ((cK * cp) * ∑ K : Fin (WCT9.famCount L.lay) → Digest,
          enT (seedsY (ptL L) (revSet L R) K) (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) := by
        ring

include haL hac hLleaf hd1 hG haF in
/-- The expected test count of the decomposed frozen law. -/
theorem count_frozen :
    ENNReal.ofReal (∑ p : PData L (restDepth a R), ∑ K : Fin (WCT9.famCount L.lay) → Digest,
          (Fintype.card (Fin (WCT9.famCount L.lay) → Digest) : ℝ)⁻¹ * ((Fintype.card (PData L (restDepth a R)) : ℝ)⁻¹ *
            exT (seedsY (ptL L) (revSet L R) K) (fun out => (tcount (L := L) (a := a) R out : ℝ))
              (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K)))) =
      ∑' z, ((PMF.uniformOfFintype (LeafData L)).bind
        (fun y => frozenLaw a (restDepth a R) (ovL L R y) (fun T => recorded (G0 T)))) z *
          (tcount (L := L) (a := a) R z.2 : ℝ≥0∞) := by
  rw [frozen_decomp haL hac hLleaf R hd1 (fun T => recorded (G0 T)) hG aF haF]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  have hx : ∀ (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)),
      ∑' out, evalT (seedsY (ptL L) (revSet L R) K)
        (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K)) out * (tcount (L := L) (a := a) R out : ℝ≥0∞) =
      ENNReal.ofReal (exT (seedsY (ptL L) (revSet L R) K) (fun out => (tcount (L := L) (a := a) R out : ℝ))
        (testRun (fun T => recorded (G0 T)) aF p (seedsR (ptL L) (revSet L R) K))) := by
    intro K p
    rw [ClaudeWCT.Arith.SideChannel.ofReal_exT _ (fun _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  simp only [hx, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [Finset.sum_comm]
  have hnn : ∀ (K : Fin (WCT9.famCount L.lay) → Digest) (p : PData L (restDepth a R)), 0 ≤ exT (seedsY (ptL L) (revSet L R) K)
      (fun out => (tcount (L := L) (a := a) R out : ℝ)) (testRun (fun T => recorded (G0 T)) aF p
        (seedsR (ptL L) (revSet L R) K)) := fun K p =>
    ClaudeWCT.Arith.SideChannel.exT_nonneg _ (fun _ => Nat.cast_nonneg _) _
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

/-! ### Test queries in the reference samples -/

/-- `input` is the step-0 row of an unrevealed chain of `L` (in the table `T`). -/
def StepZeroUnrev (L : LeafAddr) (T : Answers) (input : HashInput) : Prop :=
  ∃ c : Fin (chainCount L.lay), depth T ⟨L, c⟩ ≠ 0 ∧ ∃ v, input = chainRow ⟨L, c⟩ 0 v

/-- Number of test queries of leaf `L` in a reference sample. -/
noncomputable def NL (L : LeafAddr) (s : RefSample) : ℕ :=
  (s.trace.filter fun e => decide (StepZeroUnrev L s.answers e.1)).length

theorem isTestQ_iff {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
    (R : RefTables adversary) (T : Answers)
    (hT : ∀ c : Fin (chainCount L.lay), depth T ⟨L, c⟩ = depth (restTable R) ⟨L, c⟩) (query : RefWorld.Domain) :
    isTestQ L a (restDepth a R) (revSet L R) query ↔ ∃ x, query = .inl (.inr x) ∧ StepZeroUnrev L T x := by
  have hda : depth (restTable R) a = restDepth a R := (restDepth_eq a R).symm
  rcases query with (n | input) | u
  · simp [isTestQ]
  · simp only [isTestQ, Sum.inl.injEq, Sum.inr.injEq, exists_eq_left']
    unfold StepZeroUnrev
    cases hp : PrefixGame.rowOf a (restDepth a R) input with
    | some p =>
        have hin := PrefixGame.rowOf_some hp
        simp only
        constructor
        · intro h0
          refine ⟨⟨a.chain, hac⟩, ?_, p.2, ?_⟩
          · rw [hT]
            show depth (restTable R) ⟨L, a.chain⟩ ≠ 0
            rw [show (⟨L, a.chain⟩ : ChainAddr) = a by subst haL; rfl, hda]
            have := p.1.isLt
            omega
          · rw [hin]
            subst haL
            rw [show p.1.val = 0 from h0]
        · rintro ⟨c, -, v, he⟩
          rw [hin] at he
          have h1 : (p.1 : ℕ) < 256 := by have := p.1.isLt; have := PrefixGame.restDepth_le a R; omega
          obtain ⟨-, -, hs, -⟩ := chainInput_eq_chainRow (a := ⟨L, c⟩)
            (by have := chainCount_le L.lay; subst haL; simp only [Nat.reducePow]; omega)
            (by have := chainCount_le L.lay; have := c.isLt; simp only [Nat.reducePow]; omega) h1 (by omega) he
          exact hs
    | none =>
        simp only
        cases hz : zeroOf L input with
        | none =>
            simp only [false_iff, not_exists, not_and]
            intro c _ v he
            exact zeroOf_none hz c v he
        | some cv =>
            simp only
            have he := zeroOf_some hz
            constructor
            · intro hc
              refine ⟨cv.1, ?_, cv.2, he⟩
              rw [hT]
              unfold revSet at hc
              simpa using hc
            · rintro ⟨c, hc, v, he'⟩
              rw [he] at he'
              obtain ⟨h1, -⟩ := chainRow_zero_inj cv.1.isLt he' c.isLt
              have hcv : cv.1 = c := Fin.ext h1
              unfold revSet
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [hcv, ← hT]
              exact hc
  · simp [isTestQ]

theorem leafAgree_ov {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    LeafAgree L (restTable R) (restTable (PrefixGame.ov a (restDepth a R) R x)) := by
  have hpriv : ∀ coord, restTable (PrefixGame.ov a (restDepth a R) R x) (.inr coord) = restTable R (.inr coord) :=
    fun coord => PrefixGame.restTable_ov_private a R x coord
  refine ⟨fun q hq => ?_, fun o _ _ => ?_⟩
  · rcases q with (n | input) | coord
    · rfl
    · apply PrefixGame.restTable_ov_nonprefix
      rw [PrefixGame.rowOf_none_iff]
      rintro ⟨step, value, hs, rfl⟩
      exact hq a.chain step value hac (by have := PrefixGame.restDepth_le a R; omega) (by subst haL; rfl)
    · exact hpriv coord
  · rw [eval_lowerSeedPair, eval_lowerSeedPair, hpriv]

theorem NL_mkSample {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
    (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (run : SeedResult) :
    NL L (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) run) =
      calls (isTestQ L a (restDepth a R) (revSet L R)) run.2 := by
  unfold NL mkSample
  simp only
  rw [traceOf_filter_length]
  have hT : ∀ c : Fin (chainCount L.lay), depth (restTable (PrefixGame.ov a (restDepth a R) R x)) ⟨L, c⟩ =
      depth (restTable R) ⟨L, c⟩ := fun c => depth_lay (leafAgree_ov haL hac R x) hLleaf rfl
  congr 1
  funext query
  exact propext (isTestQ_iff haL hac R _ hT query).symm

theorem revSet_ovL {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) (R : RefTables adversary)
    (y : LeafData L) : revSet L (ovL L R y) = revSet L R := by
  unfold revSet
  congr 1
  funext c
  rw [depth_lay (leafAgree_ovL hLleaf R y) hLleaf rfl]

section Charge
variable {L : LeafAddr} {a : ChainAddr} (haL : a.key = L) (hac : a.chain < chainCount L.lay)
  (hLleaf : L.leaf < 2 ^ 24) {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', LeafCongr L T T' → recorded (G0 T') = recorded (G0 T)) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1)

/-- The rest-table-averaged expected test count of the frozen law. -/
noncomputable def frozenCount (GD : Answers → OracleComp RefWorld (Res × List RefWorld.Domain)) : ℝ≥0∞ :=
  ∑' R, restLaw adversary R * ∑' z, frozenLaw a (restDepth a R) R GD z *
    (calls (isTestQ L a (restDepth a R) (revSet L R)) z.2.1.2 : ℝ≥0∞)

include haL hac hLleaf hG hGq hq in
theorem errAR_sum_le :
    ∑' R, restLaw adversary R * errAR a (haL ▸ hac) (fun T => recorded (G0 T)) q R ≤
      ENNReal.ofReal (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
        frozenCount (adversary := adversary) (L := L) (a := a) (fun T => recorded (G0 T)) := by
  subst haL
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
    (1 - (Fintype.card Digest : ℝ)⁻¹ * q) with hC'
  have hpos : 0 < 1 - (Fintype.card Digest : ℝ)⁻¹ * q := by linarith
  -- the d-uniform count
  let Ψd : ℕ → RefTables adversary → ℝ≥0∞ := fun d R' =>
    ∑' z, frozenLaw a d R' (fun T => recorded (G0 T)) z *
      (calls (isTestQ a.key a d (revSet a.key R')) z.2.1.2 : ℝ≥0∞)
  have hres := restLaw_resampleL_tsum (adversary := adversary) hLleaf (fun R => Ψd (restDepth a R) R)
  unfold frozenCount
  change _ ≤ ENNReal.ofReal C' * ∑' R, restLaw adversary R * Ψd (restDepth a R) R
  rw [hres, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  unfold errAR
  split_ifs with hd1
  · have hy : ∀ y, Ψd (restDepth a (ovL a.key R y)) (ovL a.key R y) = ∑' z, frozenLaw a (restDepth a R)
        (ovL a.key R y) (fun T => recorded (G0 T)) z *
          (tcount (L := a.key) (a := a) R z.2 : ℝ≥0∞) := by
      intro y
      show Ψd (restDepth a (ovL a.key R y)) (ovL a.key R y) = _
      rw [restDepth_ovL hLleaf a rfl R y]
      simp only [Ψd, revSet_ovL hLleaf R y]
      rfl
    simp only [hy]
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
      ← count_frozen rfl hac hLleaf R hd1 G0 hG (selfF hac R hd1) rfl]
    rw [← ENNReal.ofReal_mul (by
      rw [hC']; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr
        (Nat.cast_nonneg _)) 3)) (Nat.cast_nonneg _)) hpos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := errR_le_count rfl hac hLleaf R hd1 G0 hG (selfF hac R hd1) rfl q hGq
    rw [hC', div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact h
  · exact bot_le
end Charge

/-- The seed-game honest body. -/
noncomputable def GDseed (adversary : AdversaryP) (q : ℕ) (T : Answers) :
    OracleComp RefWorld (Option (Bool × ℕ) × List RefWorld.Domain) := recorded (referenceGame T adversary q)

theorem seedGame_eq_gameD (q : ℕ) (a : ChainAddr) (R : RefTables adversary) (e : Digest) :
    seedGame adversary q a R e = gameD a (restDepth a R) R (GDseed adversary q) e := by
  rw [seedGame, gameD, GDseed]

theorem reference_map_NL {L : LeafAddr} {a : ChainAddr} (q : ℕ) (ha : WotsExtract.SourceChain a)
    (haL : a.key = L) (hac : a.chain < chainCount L.lay) (hLleaf : L.leaf < 2 ^ 24) :
    (referenceExperiment adversary q).map (NL L) = (restLaw adversary).bind (fun R =>
      (frozenLaw a (restDepth a R) R (GDseed adversary q)).map
        (fun z => calls (isTestQ L a (restDepth a R) (revSet L R)) z.2.1.2)) := by
  rw [reference_map_eq_frozen adversary q a ha (NL L)
    (fun R z => calls (isTestQ L a (restDepth a R) (revSet L R)) z.2.1.2)
    (fun R x res _ => NL_mkSample haL hac hLleaf R x res.1)]
  congr 1
  funext R
  unfold frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, seedGame_eq_gameD]
  rfl

/-- **The frozen count is the reference count.** -/
theorem frozenCount_eq {L : LeafAddr} {a : ChainAddr} (q : ℕ) (ha : WotsExtract.SourceChain a) (haL : a.key = L)
    (hac : a.chain < chainCount L.lay) (hLleaf : L.leaf < 2 ^ 24) :
    frozenCount (adversary := adversary) (L := L) (a := a) (GDseed adversary q) =
      ∑' s, referenceExperiment adversary q s * (NL L s : ℝ≥0∞) := by
  have e1 : ∑' s, referenceExperiment adversary q s * (NL L s : ℝ≥0∞) =
      ∑' n, ((referenceExperiment adversary q).map (NL L)) n * (n : ℝ≥0∞) := by
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rw [e1, reference_map_NL q ha haL hac hLleaf, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rfl

/-- Source leaves are determined by the step-0 rows of their chains. -/
theorem stepZero_key_unique {L L' : LeafAddr} (hL : WotsExtract.SourceLeaf L) (hL' : WotsExtract.SourceLeaf L')
    {T T' : Answers} {input : HashInput} (h : StepZeroUnrev L T input) (h' : StepZeroUnrev L' T' input) :
    L = L' := by
  obtain ⟨c, -, v, rfl⟩ := h
  obtain ⟨c', -, v', he⟩ := h'
  have hb : ∀ K : LeafAddr, WotsExtract.SourceLeaf K → K.tree < 2 ^ 40 ∧ K.leaf < 2 ^ 32 := fun K hK => by
    refine ⟨by have := hK.1; omega, ?_⟩
    have h1 := hK.2
    have h2 : 2 ^ height K.lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by
      have := SigGolfCandidate.T3.Security.Wots.height_le K.lay; omega)
    omega
  obtain ⟨hal, -, -, -⟩ := chainInput_eq_chainRow (a := ⟨L', c'⟩)
    (by have := chainCount_le L.lay; have := c.isLt; simp only [Nat.reducePow]; omega)
    (by have := chainCount_le L'.lay; have := c'.isLt; simp only [Nat.reducePow]; omega) (by omega) (by omega) he
  have := hal.eq_of_lt (hb L hL).1 (hb L hL).2 (hb L' hL').1 (hb L' hL').2
  exact this

/-- Test count of chain `a` (its leaf's). -/
noncomputable def NLa (a : ChainAddr) (s : RefSample) : ℕ := NL a.key s

/-- **Per-sample allocation:** every trace entry is a test query of at most one source leaf, whose (at most `54`)
chains each count it. -/
theorem sum_NL_le (s : RefSample) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLa a s ≤ 54 * s.trace.length := by
  unfold NLa NL
  have hcount : ∀ e : Entry, ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains,
      (if StepZeroUnrev a.key s.answers e.1 then 1 else 0) ≤ 54 := by
    intro e
    by_cases hex : ∃ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, StepZeroUnrev a.key s.answers e.1
    · obtain ⟨a0, ha0, h0⟩ := hex
      have hle : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains,
          (if StepZeroUnrev a.key s.answers e.1 then 1 else 0) =
            if a ∈ (Finset.range (chainCount a0.key.lay)).image (fun c => (⟨a0.key, c⟩ : ChainAddr)) ∧
              StepZeroUnrev a.key s.answers e.1 then 1 else 0 := by
        intro a ha
        by_cases h2 : StepZeroUnrev a.key s.answers e.1
        · have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha
          have hs0 := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a0).mp ha0
          have hk := stepZero_key_unique hs.1 hs0.1 h2 h0
          rw [if_pos h2, if_pos]
          refine ⟨Finset.mem_image.mpr ⟨a.chain, Finset.mem_range.mpr (hk ▸ hs.2), ?_⟩, h2⟩
          rw [← hk]
        · rw [if_neg h2, if_neg (fun h => h2 h.2)]
      rw [Finset.sum_congr rfl hle, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have h54 : chainCount a0.key.lay ≤ 54 := by generalize a0.key.lay = l; fin_cases l <;> decide
      calc (Finset.filter _ _).card
          ≤ ((Finset.range (chainCount a0.key.lay)).image (fun c => (⟨a0.key, c⟩ : ChainAddr))).card :=
            Finset.card_le_card (fun a ha => (Finset.mem_filter.mp ha).2.1)
        _ ≤ (Finset.range (chainCount a0.key.lay)).card := Finset.card_image_le
        _ ≤ 54 := by rw [Finset.card_range]; exact h54
    · push Not at hex
      rw [Finset.sum_eq_zero (fun a ha => by rw [if_neg (hex a ha)])]
      omega
  have key : ∀ (tr : List Entry), ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains,
      (tr.filter fun e => decide (StepZeroUnrev a.key s.answers e.1)).length ≤ 54 * tr.length := by
    intro tr
    induction tr with
    | nil => simp
    | cons e tr ih =>
        have hs : ∀ a : ChainAddr,
            (List.filter (fun e => decide (StepZeroUnrev a.key s.answers e.1)) (e :: tr)).length =
              (if StepZeroUnrev a.key s.answers e.1 then 1 else 0) +
                (List.filter (fun e => decide (StepZeroUnrev a.key s.answers e.1)) tr).length := by
          intro a
          split_ifs with h1
          · rw [List.filter_cons_of_pos (by simpa using h1), List.length_cons]
            omega
          · rw [List.filter_cons_of_neg (by simpa using h1), Nat.zero_add]
        simp only [hs, Finset.sum_add_distrib, List.length_cons]
        have := hcount e
        omega
  exact key s.trace

theorem ref_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
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

/-- **The per-chain seed-test error** (every source chain; top leaves are families since campaign T8D). -/
noncomputable def errC (adversary : AdversaryP) (q : ℕ) (a : ChainAddr) : ℝ≥0∞ :=
  if h : WotsExtract.SourceChain a then
    ∑' R, restLaw adversary R * errAR a h.2 (GDseed adversary q) q R
  else 0

theorem GDseed_leaf {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) (hLtree : L.tree < 2 ^ 40)
    (q : ℕ) (T T' : Answers) (h : LeafCongr L T T') : GDseed adversary q T' = GDseed adversary q T := by
  unfold GDseed
  rw [referenceGame_leaf h hLleaf hLtree]

theorem GDseed_queryBound (q : ℕ) (T : Answers) :
    OracleComp.IsQueryBoundP (GDseed adversary q T) RefCharged q :=
  recorded_queryBound RefCharged _ q (referenceGame_queryBound T adversary q)

/-- The per-chain constant `2 δ K(q) / (1 - q/2^128)`. -/
noncomputable def errConst (q : ℕ) : ℝ :=
  2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
    (1 - (Fintype.card Digest : ℝ)⁻¹ * q)

theorem errC_le (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) (a : ChainAddr) :
    errC adversary q a ≤ ENNReal.ofReal (errConst q) *
      ∑' s, referenceExperiment adversary q s * (NLa a s : ℝ≥0∞) := by
  unfold errC
  split_ifs with h
  · have ha := h
    have hleaf : a.key.leaf < 2 ^ 24 := by
      have h1 := ha.1.2
      have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
        have := SigGolfCandidate.T3.Security.Wots.height_le a.key.lay; omega)
      omega
    have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
    unfold NLa
    rw [← frozenCount_eq q ha rfl ha.2 hleaf]
    exact errAR_sum_le rfl ha.2 hleaf (fun T => referenceGame T adversary q)
      (fun T T' h => GDseed_leaf hleaf htree q T T' h) q (fun T => GDseed_queryBound q T) hq
  · exact bot_le

/-- **Total seed-test error.** -/
theorem errC_sum_le (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errC adversary q a ≤
      ENNReal.ofReal (errConst q) * (54 * q) := by
  calc ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errC adversary q a
      ≤ ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, ENNReal.ofReal (errConst q) *
          ∑' s, referenceExperiment adversary q s * (NLa a s : ℝ≥0∞) :=
        Finset.sum_le_sum fun a _ => errC_le q hq a
    _ = ENNReal.ofReal (errConst q) * ∑' s, referenceExperiment adversary q s *
          ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLa a s : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (errConst q) * (54 * q) := by
        refine mul_le_mul' le_rfl ?_
        calc ∑' s, referenceExperiment adversary q s *
              ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLa a s : ℕ) : ℝ≥0∞)
            ≤ ∑' s, referenceExperiment adversary q s * (54 * q) := by
              refine ENNReal.tsum_le_tsum fun s => ?_
              by_cases hs : s ∈ (referenceExperiment adversary q).support
              · refine mul_le_mul' le_rfl ?_
                have h1 := sum_NL_le s
                have h2 := ref_trace_length_le adversary q s hs
                have : ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLa a s ≤ 54 * q := by
                  calc _ ≤ 54 * s.trace.length := h1
                    _ ≤ 54 * q := Nat.mul_le_mul_left 54 h2
                exact_mod_cast this
              · rw [(PMF.apply_eq_zero_iff _ s).mpr hs, zero_mul, zero_mul]
          _ = 54 * q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
