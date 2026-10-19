import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamFill
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamGame
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafTest
set_option Elab.async false

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

#print axioms evaluate_tYF
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

#print axioms evalT_testRunF
#print axioms tdepth_testImplF
#print axioms enT_testImplF
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

#print axioms otherHalf_ovF
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

#print axioms famCongr_progF
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

#print axioms famCongr_normalizeF
#print axioms route_programmedF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
