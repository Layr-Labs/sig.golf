import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafProg
import SigGolfCandidate.ClaudeWCT.Arith.SideChannelSem
import SigGolfCandidate.ClaudeWCT.Arith.FamilySideChannel

/-! # The seed-test program of a lower leaf (campaign X1 stage B, step B3)

Fix a lower source chain `a` of leaf `L`, the rest tables `R` and the depth `d` of `a`. With the step-0 rows of
`L`'s chains programmed at the family seeds (`fY`) and chain `a`'s prefix tables programmed at its seed (`tY`),
the adversary's oracle world of the prefix game is a test program (`testImpl`) over the unrevealed seeds: a query
of a programmed row at `v` is the equality test `seed = v`. `evalT_testRun` identifies the run of the test program
against `y` with the prefix-game run in the world programmed at `y`. -/

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
noncomputable local instance instFintypeCoordinate_wotsLeafTest : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
variable {adversary : AdversaryP}

/-- Chains of `L` revealed (depth `0`) in `R`. -/
noncomputable def revSet (L : LeafAddr) (R : RefTables adversary) : Finset (Fin (chainCount L.lay)) :=
  Finset.univ.filter fun c => depth (restTable R) ⟨L, c⟩ = 0

/-- Parameters of the test program: row functions and labels of `L`'s step-0 rows (`g`, `lab`), of chain `a`'s
prefix tables (`gt`, `labt`), and the revealed seeds `r`. -/
structure TParams (L : LeafAddr) (d : Nat) where
  g : Fin (chainCount L.lay) → Digest → Digest
  lab : Fin (chainCount L.lay) → Digest
  gt : Fin d → Digest → Digest
  labt : Fin d → Digest
  r : Fin (chainCount L.lay) → Digest

section Defs
variable (L : LeafAddr) (a : ChainAddr) (d : Nat) (R : RefTables adversary)
  (Rev : Finset (Fin (chainCount L.lay))) (aF : Free Rev) (P : TParams L d)

/-- Chain `a`'s prefix tables, row `0` programmed at the seed `s` (the other rows at `0`). -/
def tY (s : Digest) : Fin d → Digest → Digest :=
  fun i => Function.update (P.gt i) (if i.val = 0 then s else 0) (P.labt i)

/-- Step-0 rows of `L`'s chains: revealed chains programmed at `r`, unrevealed ones at `y`. -/
noncomputable def fY (y : Free Rev → Digest) : Fin (chainCount L.lay) → Digest → Digest :=
  fun c => Function.update (P.g c) (if hc : c ∈ Rev then P.r c else y ⟨c, hc⟩) (P.lab c)

/-- Observed prefix rows. -/
abbrev TObs := Fin d → Digest → Option Digest

/-- Answer to a prefix query of chain `a`: row `0` is a test on `a`'s seed. -/
noncomputable def prefAns (p : Fin d × Digest) : OracleComp (TSpec (Free Rev) Digest) Digest :=
  if p.1.val = 0 then (fun b => if b then P.labt p.1 else P.gt p.1 p.2) <$> testQ (aF, p.2)
  else pure (Function.update (P.gt p.1) 0 (P.labt p.1) p.2)

/-- Answer to any other public query: step-0 rows of unrevealed chains of `L` are tests. -/
noncomputable def pubAns (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOf L input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (ChainGraph.joinOutput (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (high (restTable R (.inl (.inr input)))))
      else (fun b => ChainGraph.joinOutput (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (high (restTable R (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (restTable R (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world. -/
noncomputable def testImpl : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (ChainGraph.joinOutput w (high (restTable R (.inl (.inr input)))), record obs p w)) <$>
            prefAns L d Rev aF P p
      | none => StateT.lift (pubAns L d R Rev P input)
  | .inr _ => pure ()
end Defs

theorem high_ovL (L : LeafAddr) (R : RefTables adversary) (X : LeafData L) (input : HashInput) :
    high (restTable (ovL L R X) (.inl (.inr input))) = high (restTable R (.inl (.inr input))) := by
  cases hz : zeroOf L input with
  | none => rw [restTable_ovL_pub L R X input hz]
  | some cv =>
      rw [zeroOf_some hz, restTable_ovL_zero, high, ChainGraph.joinOutput_high]

theorem ite_decide_update (g : Digest → Digest) (y lab v : Digest) :
    (if decide (y = v) then lab else g v) = Function.update g y lab v := by
  rw [Function.update_apply]
  by_cases h : v = y
  · subst h; simp
  · rw [if_neg h, if_neg (by simpa [eq_comm] using h)]

section Bridge
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (R : RefTables adversary) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem evalT_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (y : ι → Digest) (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : evalT y (f <$> oa) = (evalT y oa).map f := by
  unfold evalT
  rw [simulateQ_map]
  rfl

theorem evalT_prefAns (y : Free Rev → Digest) (p : Fin d × Digest) :
    evalT y (prefAns L d Rev aF P p) = PMF.pure (tY L d P (y aF) p.1 p.2) := by
  unfold prefAns tY
  split_ifs with h0
  · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]
  · rfl

theorem evalT_pubAns (y : Free Rev → Digest) (K : Fin 17 → Digest) (input : HashInput) :
    evalT y (pubAns L d R Rev P input) = PMF.pure (restTable (ovL L R (K, fY L d Rev P y)) (.inl (.inr input))) := by
  unfold pubAns
  cases hz : zeroOf L input with
  | none =>
      simp only
      rw [restTable_ovL_pub L R _ input hz]
      rfl
  | some cv =>
      simp only
      rw [zeroOf_some hz, restTable_ovL_zero, ← zeroOf_some hz]
      unfold fY
      simp only
      split_ifs with hc
      · rfl
      · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]

/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridge (y : Free Rev → Digest) (K : Fin 17 → Digest) (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImpl L a d R Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF)))
        (PrefixGame.routeImpl a d (ovL L R (K, fY L d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImpl, PrefixGame.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImpl, PrefixGame.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (ChainGraph.joinOutput w (high (restTable R (.inl (.inr input)))), record s p w)) <$>
          prefAns L d Rev aF P p) = _
        rw [evalT_map, evalT_prefAns, PMF.pure_map, high_ovL L R]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAns L d R Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAns R P y K input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRun (y : Free Rev → Digest) (K : Fin 17 → Digest) {α : Type} (G : OracleComp RefWorld α)
    (obs : TObs d) :
    evalT y ((simulateQ (testImpl L a d R Rev aF P) G).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF))
        (simulateQ (PrefixGame.routeImpl a d (ovL L R (K, fY L d Rev P y))) G) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridge R aF P y K q
end Bridge

/-! ### Test counts and depth -/

/-- Queries answered by a test: chain `a`'s prefix row `0`, and step-0 rows of unrevealed chains of `L`. -/
noncomputable def isTestQ (L : LeafAddr) (a : ChainAddr) (d : Nat) (Rev : Finset (Fin (chainCount L.lay))) :
    RefWorld.Domain → Prop
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => p.1.val = 0
      | none =>
          match zeroOf L input with
          | some cv => cv.1 ∉ Rev
          | none => False
  | _ => False

theorem tdepth_map_le {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : tdepth (f <$> oa) ≤ tdepth oa := by
  rw [map_eq_bind_pure_comp]
  exact (ClaudeWCT.Arith.SideChannel.tdepth_bind_le oa _ 0 fun _ => le_rfl).trans (by omega)
theorem enT_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} (y : ι → Digest) (f : α → β)
    (oa : OracleComp (TSpec ι Digest) α) : enT y (f <$> oa) = enT y oa := by
  rw [map_eq_bind_pure_comp, ClaudeWCT.Arith.SideChannel.enT_bind]
  simp only [Function.comp_apply]
  rw [show (fun x => enT y (pure (f x) : OracleComp (TSpec ι Digest) β)) = fun _ => (0 : ℝ) from rfl,
    ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
theorem tdepth_testQ {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι × Digest) :
    tdepth (testQ p : OracleComp (TSpec ι Digest) Bool) = 1 := by
  have h := ClaudeWCT.Arith.SideChannel.tdepth_test (V := Digest) p (fun b => pure b)
  rw [bind_pure] at h
  rw [h]
  rfl
theorem enT_testQ {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → Digest) (p : ι × Digest) :
    enT y (testQ p : OracleComp (TSpec ι Digest) Bool) = 1 := by
  have h := ClaudeWCT.Arith.SideChannel.enT_test y p (fun b => pure b)
  rw [bind_pure] at h
  rw [h]
  simp [ClaudeWCT.Arith.SideChannel.enT_pure]

section Counts
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (R : RefTables adversary) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem tdepth_testImpl (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImpl L a d R Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
  rcases q with (n | input) | u
  · simp only [testImpl, StateT.run_lift]
    rw [if_neg (by simp [RefCharged])]
    refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
    rw [Nat.add_zero, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _) from
      (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.tdepth_coin]
    simp [ClaudeWCT.Arith.SideChannel.tdepth_pure]
  · rw [if_pos (by simp [RefCharged])]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [testImpl, hp, StateT.run_mk]
        refine (tdepth_map_le _ _).trans ?_
        unfold prefAns
        split_ifs with h0
        · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
        · exact Nat.zero_le _
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
        rw [Nat.add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none => exact Nat.zero_le _
        | some cv =>
            simp only
            split_ifs with hc
            · exact Nat.zero_le _
            · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
  · exact Nat.zero_le _

theorem enT_testImpl (y : Free Rev → Digest) (q : RefWorld.Domain) (s : TObs d) :
    enT y ((testImpl L a d R Rev aF P q).run s) = if isTestQ L a d Rev q then 1 else 0 := by
  rcases q with (n | input) | u
  · rw [if_neg (by simp [isTestQ])]
    simp only [testImpl, StateT.run_lift]
    rw [ClaudeWCT.Arith.SideChannel.enT_bind, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _)
      from (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.enT_coin]
    simp [ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_const]
  · cases hp : PrefixGame.rowOf a d input with
    | some p =>
        have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ p.1.val = 0 := by simp only [isTestQ, hp]
        simp only [testImpl, hp, StateT.run_mk]
        rw [enT_map]
        unfold prefAns
        split_ifs with h0 h1 h1
        · rw [enT_map, enT_testQ]
        · exact absurd (hT.mpr h0) h1
        · exact absurd (hT.mp h1) h0
        · rfl
    | none =>
        simp only [testImpl, hp, StateT.run_lift]
        rw [ClaudeWCT.Arith.SideChannel.enT_bind,
          show (fun x => enT y (pure (x, s) : OracleComp (TSpec (Free Rev) Digest) _)) = fun _ => (0 : ℝ) from rfl,
          ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
        unfold pubAns
        cases hz : zeroOf L input with
        | none =>
            rw [if_neg (by simp only [isTestQ, hp, hz]; exact id)]
            rfl
        | some cv =>
            have hT : isTestQ L a d Rev (.inl (.inr input)) ↔ cv.1 ∉ Rev := by simp only [isTestQ, hp, hz]
            simp only
            split_ifs with hc h1 h1
            · exact absurd hc (hT.mp h1)
            · rfl
            · rw [enT_map, enT_testQ]
            · exact absurd (hT.mpr hc) h1
  · rw [if_neg (by simp [isTestQ])]
    rfl
end Counts

/-- Expected number of tests of a state-passing simulation that tests exactly on the `C`-queries. -/
theorem enT_simulate {ι ιs σ : Type} [Fintype ι] [DecidableEq ι] {spec : OracleSpec ιs} (y : ι → Digest)
    (impl : QueryImpl spec (StateT σ (OracleComp (TSpec ι Digest)))) (C : ιs → Prop) [DecidablePred C]
    (himpl : ∀ q s, enT y ((impl q).run s) = if C q then 1 else 0) {α : Type} (G : OracleComp spec α) (s : σ) :
    enT y ((simulateQ impl G).run s) =
      exT y (fun out => (out.1.2 : ℝ)) ((simulateQ impl (SphincsSecurity.QueryCap.counted C G)).run s) := by
  induction G using OracleComp.inductionOn generalizing s with
  | pure x =>
      rw [SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
        ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_pure]
      simp
  | query_bind q k ih =>
      rw [SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure]
      rw [ClaudeWCT.Arith.SideChannel.enT_bind, ClaudeWCT.Arith.SideChannel.exT_bind, himpl]
      simp only [ih]
      rw [← ClaudeWCT.Arith.SideChannel.exT_add_const]
      congr 1
      funext p
      rw [ClaudeWCT.Arith.SideChannel.exT_bind, ← ClaudeWCT.Arith.SideChannel.exT_add_const]
      congr 1
      funext r
      simp only [StateT.run_pure]
      rw [ClaudeWCT.Arith.SideChannel.exT_pure]
      push_cast
      split_ifs <;> simp

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
