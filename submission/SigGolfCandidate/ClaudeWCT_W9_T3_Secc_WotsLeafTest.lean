import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafProg
import SigGolfCandidate.ClaudeWCT_Arith_SideChannelSem
import SigGolfCandidate.ClaudeWCT_Arith_FamilySideChannel
set_option Elab.async false

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
        pure (joinHalf (zh L cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input)))))
      else (fun b => joinHalf (zh L cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (restTable R (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world. -/
noncomputable def testImpl : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input)))),
              record obs p w)) <$> prefAns L d Rev aF P p
      | none => StateT.lift (pubAns L d R Rev P input)
  | .inr _ => pure ()
end Defs

/-- Pairing stage 1: the leaf override keeps the half of a step-0 row of `L` that its chain does not read. -/
theorem otherZ_ovL (L : LeafAddr) (R : RefTables adversary) (X : LeafData L) (input : HashInput)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L input = some cv) :
    WCT9.halfOf (!zh L cv.1) (restTable (ovL L R X) (.inl (.inr input))) =
      WCT9.halfOf (!zh L cv.1) (restTable R (.inl (.inr input))) := by
  rw [zeroOf_some hz, restTable_ovL_zero, halfOf_not_joinHalf]
/-- A row of chain `a` at a step `s < 256` that is a step-0 row of chain `c` of `L` is step 0 of a chain with the
same layer and parity, hence read through the same half. -/
theorem chainHigh_of_zeroOf {L : LeafAddr} {a : ChainAddr} {s : Nat} {v : Digest} (hs : s < 256)
    (hc : a.chain < 2 ^ 24)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L (chainRowW a s v) = some cv) :
    WCT9.chainHigh a.key.lay a.chain s = zh L cv.1 := by
  -- Witness stack: the top G rule (`i ≤ 52`) is not a function of `i % 2^24`, so the chain index is pinned by
  -- the bound `a.chain < 2^24` (the header carries `i % 2^24`).
  have he := zeroOf_some hz
  obtain ⟨hh, -⟩ := chainInputW_fields he
  obtain ⟨hl, -, -, hi, hst⟩ := chainHeader_fields hh
  have hs0 : s = 0 := by simp only [Nat.zero_mod] at hst; omega
  have hcv : cv.1.val < 2 ^ 24 :=
    lt_of_lt_of_le cv.1.isLt (le_trans (SigGolfCandidate.T3.chainCount_bound L.lay) (by norm_num))
  have hac : a.chain = cv.1.val := by
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hcv] at hi; exact hi
  subst hs0
  unfold zh
  simp only at hl
  rw [hl, hac]

/-- C3: the half of a chain-`a` row that the prefix game keeps from the rest table is unchanged by the leaf
override: a step-0 row keeps its high half, and the only row whose used half is high (step 6 of a lower chain 0)
is no step-0 row. -/
theorem otherHalf_ovL (L : LeafAddr) (R : RefTables adversary) (X : LeafData L) (a : ChainAddr) (s : Nat)
    (v : Digest)
    (hs : s < 256) (hc : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (restTable (ovL L R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (restTable R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOf L (chainRowW a s v) with
  | none => rw [restTable_ovL_pub L R X _ hz]
  | some cv => rw [chainHigh_of_zeroOf hs hc hz, otherZ_ovL L R X _ hz]
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

theorem evalT_pubAns (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest) (input : HashInput) :
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
theorem testImpl_bridge (hd : d ≤ 256) (hc : a.chain < 2 ^ 24) (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest)
    (q : RefWorld.Domain) :
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
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input)))),
            record s p w)) <$> prefAns L d Rev aF P p) = _
        rw [evalT_map, evalT_prefAns, PMF.pure_map, PrefixGame.rowOf_some hp,
          otherHalf_ovL L R _ _ _ _ (by have := p.1.isLt; omega) hc]
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
theorem evalT_testRun (hd : d ≤ 256) (hc : a.chain < 2 ^ 24) (y : Free Rev → Digest) (K : Fin (WCT9.famCount L.lay) → Digest) {α : Type}
    (G : OracleComp RefWorld α)
    (obs : TObs d) :
    evalT y ((simulateQ (testImpl L a d R Rev aF P) G).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF))
        (simulateQ (PrefixGame.routeImpl a d (ovL L R (K, fY L d Rev P y))) G) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridge R aF P hd hc y K q
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

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Test
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def publicAt (L : LeafAddr) (B : Answers) (f : Fin (chainCount L.lay) → Digest → Digest) (input : HashInput) : HashOutput :=
  match zeroOf L input with
  | some cv => joinHalf (zh L cv.1) (f cv.1 cv.2) (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input))))
  | none => B (.inl (.inr input))
noncomputable def withPublic (L : LeafAddr) (B : Answers) (f : Fin (chainCount L.lay) → Digest → Digest) : Answers
  | .inl (.inr input) => publicAt L B f input
  | .inl (.inl coin) => B (.inl (.inl coin))
  | .inr coordinate => B (.inr coordinate)

section Defs
variable (L : LeafAddr) (a : ChainAddr) (d : Nat) (B : Answers)
  (Rev : Finset (Fin (chainCount L.lay))) (aF : Free Rev) (P : TParams L d)
/-- Answer to any other public query: step-0 rows of unrevealed chains of `L` are tests. -/
noncomputable def pubAns (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOf L input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (joinHalf (zh L cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input)))))
      else (fun b => joinHalf (zh L cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zh L cv.1) (B (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (B (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world. -/
noncomputable def testImpl : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
              record obs p w)) <$> prefAns L d Rev aF P p
      | none => StateT.lift (pubAns L d B Rev P input)
  | .inr _ => pure ()
end Defs


section Bridge
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (B : Answers)
  {Rev : Finset (Fin (chainCount L.lay))} (aF : Free Rev) (P : TParams L d)

theorem evalT_pubAns (y : Free Rev → Digest) (input : HashInput) :
    evalT y (pubAns L d B Rev P input)=PMF.pure (publicAt L B (fY L d Rev P y) input) := by
  unfold pubAns publicAt
  cases hz : zeroOf L input with
  | none => rfl
  | some cv =>
    simp only
    unfold fY
    split_ifs with hc
    · rfl
    · rw [evalT_map,ClaudeWCT.Arith.SideChannel.evalT_testQ,PMF.pure_map,ite_decide_update]
/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridge (y : Free Rev → Digest) (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImpl L a d B Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF)))
        (Route.routeImpl a d B (withPublic L B (fY L d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImpl, Route.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImpl, Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
            record s p w)) <$> prefAns L d Rev aF P p) = _
        rw [evalT_map, evalT_prefAns, PMF.pure_map]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAns L d B Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAns B P y input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRun (y : Free Rev → Digest) {α : Type} (G : OracleComp RefWorld α)
    (obs : TObs d) :
    evalT y ((simulateQ (testImpl L a d B Rev aF P) G).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tY L d P (y aF))
        (simulateQ (Route.routeImpl a d B (withPublic L B (fY L d Rev P y))) G) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridge B aF P y q
end Bridge

section Counts
variable {L : LeafAddr} {a : ChainAddr} {d : Nat} (B : Answers) {Rev : Finset (Fin (chainCount L.lay))}
  (aF : Free Rev) (P : TParams L d)

theorem tdepth_testImpl (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImpl L a d B Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
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
    enT y ((testImpl L a d B Rev aF P q).run s) = if isTestQ L a d Rev q then 1 else 0 := by
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


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Test

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
include hU
attribute [local irreducible] raw normalize answers RawPrefix.fill ovL

theorem otherZ_ovL (L : LeafAddr) (R : Tables U) (X : LeafData L) (input : HashInput)
    {cv : Fin (chainCount L.lay) × Digest} (hz : zeroOf L input = some cv) :
    WCT9.halfOf (!zh L cv.1) (raw (ovL L R X) (.inl (.inr input))) =
      WCT9.halfOf (!zh L cv.1) (raw R (.inl (.inr input))) := by
  rw [zeroOf_some hz, raw_ovL_zero hU, halfOf_not_joinHalf]

/-- Stage 2 (C3, #866 `otherHalf_ovL`): the half of a chain-`a` row that the prefix game keeps from the rest
table (the half its step does not read) is unchanged by the leaf override: a step-0 row keeps its high half,
and the only row whose used half is high (step 6 of a lower chain 0) is no step-0 row. -/
theorem otherHalf_ovL (L : LeafAddr) (R : Tables U) (X : LeafData L) (a : ChainAddr) (s : Nat) (v : Digest)
    (hs : s < 256) (hc : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (ovL L R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOf L (chainRowW a s v) with
  | none => rw [raw_ovL_pub _ _ _ _ hz]
  | some cv => rw [chainHigh_of_zeroOf hs hc hz, otherZ_ovL hU L R X _ hz]

/-- Stage 2 (C3): the filled table keeps `R`'s other half (the one the step does not read) of a chain-`a` row. -/
theorem otherHalf_fill (a : ChainAddr) (R : Tables U) (e : Digest) (s : Nat) (v : Digest) (hs : s < 256) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (RawPrefix.fill a R e) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  unfold RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a R;omega)]
  cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) (chainRowW a s v) with
  | none => rfl
  | some p =>
      simp only
      have hin := PrefixGame.rowOf_some hp
      have hps : p.1.val = s :=
        (ClaudeWCT.W9.T3.Security.Wots.chainRowW_inj
          (by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega) hs hin.symm).1
      rw [hps, halfOf_not_joinHalf]

/-- The filled table agrees with `R` on the high half of every non-prefix query. -/
theorem high_fill_nonprefix (a : ChainAddr) (R : Tables U) (e : Digest) (input : HashInput)
    (hn : PrefixGame.rowOf a (RawPrefix.restDepth a R) input = none) (b : Bool) :
    WCT9.halfOf b (raw (RawPrefix.fill a R e) (.inl (.inr input))) = WCT9.halfOf b (raw R (.inl (.inr input))) := by
  unfold RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix a R _ input hn]

theorem normalized_public_congr {L : LeafAddr} {R R' : Tables U}
    (hC : LeafAgree L (raw R) (raw R')) (hm : sourceMessages (raw R')=sourceMessages (raw R))
    (input : HashInput) (heq : raw R' (.inl (.inr input))=raw R (.inl (.inr input))) :
    answers hU R' (.inl (.inr input))=answers hU R (.inl (.inr input)) := by
  by_cases hn : Wots.Enc.NonEnc (.inl (.inr input))
  · rw [nonEnc hU R' _ hn,nonEnc hU R _ hn,heq]
  · apply (leafAgree_normalize hU hC hm).out
    intro c step value hc hs he
    have hne := nonEnc_chainRow ⟨L,c⟩ step value
    apply hn
    rw [he]
    exact hne

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
