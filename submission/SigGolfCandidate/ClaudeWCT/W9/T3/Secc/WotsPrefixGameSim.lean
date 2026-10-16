import SigGolfCandidate.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameBase

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (R : RefTables adversary) :
    QueryImpl RefWorld (OracleComp (SeedSpec d))
  | .inl (.inl n) => liftM ((SeedSpec d).query (.inl n))
  | .inl (.inr input) =>
      match rowOf a d input with
      | some p => (fun w => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input))))) <$>
          liftM ((SeedSpec d).query (.inr p))
      | none => pure (restTable R (.inl (.inr input)))
  | .inr _ => pure ()
noncomputable def fillTable (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) : Answers :=
  restTable (ov a (restDepth a R) R (fun _ _ => endpoint, endpoint))
theorem prefixStep_none {T : Answers} {a : ChainAddr} {input : HashInput} (h : prefixStep T a input = none) :
    ¬∃ step value, step < depth T a ∧ input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · cases h
  · assumption
theorem evaluate_const_succ (n : Nat) (value start : Digest) :
    evaluate (fun (_ : Fin (n + 1)) (_ : Digest) => value) start = value := by
  simp only [evaluate]
  exact evaluate_const n value
theorem evaluate_fill (n : Nat) (tables : Fin n → Digest → Digest) (start : Digest) :
    evaluate (fun (_ : Fin n) (_ : Digest) => evaluate tables start) start = evaluate tables start := by
  cases n with
  | zero => rfl
  | succ n => exact evaluate_const_succ n _ start
theorem maskAt_ov_fill (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    maskAt (restTable (ov a (restDepth a R) R x)) a =
      maskAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) a := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  set e := evaluate x.1 (ovSeed a R x.2) with he
  have hdx : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hdf : depth (fillTable a R e) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
  apply maskAt_congr
  · intro input hp
    have hnone : rowOf a (restDepth a R) input = none := by
      rw [rowOf_none_iff]
      have := prefixStep_none hp
      rw [hdx] at this
      exact this
    unfold fillTable
    rw [restTable_ov_nonprefix a R x input hnone, restTable_ov_nonprefix a R _ input hnone]
  · intro coin
    rfl
  · intro coordinate
    rfl
  · rw [hdx, hdf]
  · rw [frontierValue_ov]
    unfold fillTable
    rw [frontierValue_ov]
    have h1 : ∀ v, ovSeed a R v = ovSeed a R x.2 := fun v => rfl
    rw [h1 e, he]
    exact (evaluate_fill _ _ _).symm
theorem referenceGame_fill (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (q : Nat) :
    referenceGame (restTable (ov a (restDepth a R) R x)) adversary q =
      referenceGame (fillTable a R (evaluate x.1 (ovSeed a R x.2))) adversary q := by
  rw [← referenceGame_maskAt _ a htree hleaf, maskAt_ov_fill a R x, referenceGame_maskAt _ a htree hleaf]
end PrefixGame
open PrefixGame in
noncomputable def seedGame (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) : OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (PrefixGame.routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R endpoint) adversary q))
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem fixed_route (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ((fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) ∘ₛ routeImpl a d R) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl ∘ₛ refImpl (restTable (ov a d R x))) := by
  funext query
  rcases query with (n | input) | u
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl]
    cases hp : rowOf a d input with
    | none =>
        simp only [simulateQ_pure]
        rw [restTable_ov_nonprefix a R x input hp]
    | some p =>
        have hin := rowOf_some hp
        simp only [simulateQ_map, simulateQ_spec_query, simulateQ_pure]
        simp only [fixedImpl, QueryImpl.add_apply_inr]
        rw [hin, restTable_ov_prefix a hd R x p.1 p.2, ← PMF.monad_pure_eq_pure, map_pure]
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_pure]
theorem fixed_seedGame (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) =
      (liftM (offlineRun (restTable (ov a (restDepth a R) R x)) adversary q) : PMF SeedResult) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold seedGame
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl
theorem route_step_observed (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) (input : RefWorld.Domain) (observed : Fin d → Digest → Option Digest)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (routeImpl a d R input)
      observed).support) (i : Fin d) (v : Digest) :
    result.2 i v = if input = .inl (.inr (chainRow a i v)) then some (tables i v) else observed i v := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
    simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simp
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        rw [if_neg]
        intro he
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
        simp only [observedImpl, StateT.run_mk, PMF.pure_bind, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        have hin := rowOf_some hp
        simp only [record]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [Function.update_self, hin, if_true]
        · have hne : input ≠ chainRow a i v := by
            rw [hin]
            intro he
            obtain ⟨hs, hv⟩ := chainRow_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          rw [if_neg (fun he => hne (Sum.inr.inj (Sum.inl.inj he)))]
          by_cases h1 : i = p.1
          · subst h1
            have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
            simp only [Function.update_self, Function.update_of_ne h2]
          · simp only [Function.update_of_ne h1]
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simp
theorem observed_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) {β : Type} (computation : OracleComp RefWorld β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : (β × List RefWorld.Domain) × (Fin d → Digest → Option Digest)),
      result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation)) observed).support →
      ∀ (i : Fin d) (v : Digest), result.2 i v =
        if (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ result.1.2 then some (tables i v) else observed i v := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr i v
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      simp only [List.not_mem_nil, if_false]
  | query_bind input next ih =>
      intro observed result hr i v
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query, observedRun_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [simulateQ_bind, observedRun_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨tail, htail, hr⟩ := hr
      simp only [simulateQ_pure, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
        PMF.mem_support_pure_iff] at hr
      subst hr
      have hstep := route_step_observed a hd R tables input observed middle hmiddle i v
      have htl := ih middle.1 middle.2 tail htail i v
      simp only [List.mem_cons]
      rw [htl, hstep]
      by_cases h1 : (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ tail.1.2
      · simp only [h1, or_true, if_true]
      · simp only [h1, if_false, or_false]
        by_cases h2 : input = .inl (.inr (chainRow a i v))
        · simp only [h2, if_true]
        · simp only [h2, if_false]
          rw [if_neg (fun he => h2 he.symm)]
theorem route_step_count (a : ChainAddr) {d : Nat} (R : RefTables adversary) (input : RefWorld.Domain)
    (first : RefWorld.Range input × Nat)
    (hfirst : first ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (routeImpl a d R input))) :
    first.2 = if PrefixQuery a d input then 1 else 0 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_query, support_map, Set.mem_image] at hfirst
    obtain ⟨answer, -, rfl⟩ := hfirst
    rw [if_neg, if_neg]
    · rintro ⟨i, v, he⟩
      cases he
    · exact fun h => h
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
        subst hfirst
        rw [if_neg]
        rintro ⟨i, v, he⟩
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_map, SphincsSecurity.QueryCap.counted_query,
          support_map, Set.mem_image] at hfirst
        obtain ⟨⟨answer, count⟩, hcount, rfl⟩ := hfirst
        obtain ⟨w, -, hw⟩ := hcount
        simp only [Prod.mk.injEq] at hw
        dsimp only
        rw [← hw.2, if_pos (show (IsPrefixQuery (Sum.inr p : (SeedSpec d).Domain) : Prop) from trivial),
          if_pos ⟨p.1, p.2, by rw [rowOf_some hp]⟩]
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
    subst hfirst
    rw [if_neg]
    rintro ⟨i, v, he⟩
    cases he
theorem counted_rows (a : ChainAddr) {d : Nat} (R : RefTables adversary) {β : Type}
    (computation : OracleComp RefWorld β) :
    ∀ result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation))),
      result.2 = SphincsSecurity.QueryCap.calls (PrefixQuery a d) result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro result hr
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      rfl
  | query_bind input next ih =>
      intro result hr
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨second, hsecond, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst hr
      rw [simulateQ_bind, SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hsecond
      obtain ⟨tail, htail, hsecond⟩ := hsecond
      simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, pure_bind, mem_support_pure_iff] at hsecond
      subst hsecond
      have hstep := route_step_count a R input first hfirst
      have htl := ih first.1 tail htail
      simp only [SphincsSecurity.QueryCap.calls_cons, hstep, htl, Nat.add_zero]
end PrefixGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
open PrefixGame in
noncomputable def seedCost {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) (result : SeedResult) :
    Nat :=
  SphincsSecurity.QueryCap.calls (PrefixQuery a (restDepth a R)) result.2
open PrefixGame in
theorem seedGame_charge (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) (result : SeedResult × Nat)
    (h : result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))) :
    result.2 = seedCost a R result.1 := by
  unfold seedGame at h
  revert h
  exact PrefixGame.counted_rows (d := restDepth a R) a R (referenceGame (PrefixGame.fillTable a R endpoint) adversary q) result
theorem referenceGame_queryBound (T : Answers) (adversary : AdversaryP) (q : Nat) :
    (referenceGame T adversary q).IsQueryBoundP RefCharged q := by
  unfold referenceGame
  exact SphincsSecurity.QueryCap.run_queryBound RefCharged (offlineGame T adversary) q
open PrefixGame in
theorem seedGame_real_cost (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (result : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)))
    (h : result ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
      (fun _ _ => none)).support) :
    seedCost a R result.2.1 ≤ q := by
  have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (fun _ _ => none) result h
  have hseed : result.2.1 ∈ support (seedGame adversary q a R result.1) := by
    revert hlazy
    exact lazyRun_mem_support (seedGame adversary q a R result.1) (fun _ _ => none) result.2
  have hrec : result.2.1 ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    unfold seedGame at hseed
    revert hseed
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (PrefixGame.routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) result.2.1
  have hcount : (result.2.1.1, SphincsSecurity.QueryCap.calls RefCharged result.2.1.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged
        (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result.2.1, hrec, rfl⟩
  have hbound := referenceGame_queryBound (PrefixGame.fillTable a R result.1) adversary q
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q hbound _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem maskAt_congr (answers answers' : Answers) (messages messages' : LeafAddr → WCT9.LayerMsg) (a : ChainAddr)
    (hrows : ∀ input, prefixStep answers messages a input = none →
      answers (.inl (.inr input)) = answers' (.inl (.inr input)))
    (hcoins : ∀ coin, answers (.inl (.inl coin)) = answers' (.inl (.inl coin)))
    (hprivate : ∀ coordinate, answers (.inr coordinate) = answers' (.inr coordinate))
    (hdepth : depth answers messages a = depth answers' messages' a)
    (hfrontier : frontierValue answers messages a = frontierValue answers' messages' a) :
    maskAt answers messages a = maskAt answers' messages' a := by
  have hstep : prefixStep answers messages a = prefixStep answers' messages' a := by
    funext input
    exact congrArg (fun d : Nat =>
      if h : ∃ step value, step<d ∧ input=chainRow a step value then some (Classical.choose h) else none) hdepth
  funext q
  rcases q with (coin | input) | c
  · exact hcoins coin
  · rw [Mask.maskAt_public, Mask.maskAt_public, ← hstep, hdepth, hfrontier]
    cases hp : prefixStep answers messages a input with
    | none => exact hrows input hp
    | some step => rfl
  · exact hprivate c

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
noncomputable def fill (a : ChainAddr) (R : Tables U) (endpoint : Digest) : Tables U :=
  ov a (restDepth a R) R (fun _ _ => endpoint, endpoint)

theorem prefixStep_none {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {a : ChainAddr} {input : HashInput}
    (h : CanonicalRef.prefixStep T messages a input=none) :
    ¬∃step value, step<CanonicalRef.depth T messages a ∧ input=chainRow a step value := by
  unfold CanonicalRef.prefixStep at h
  split at h
  · cases h
  · assumption

include hU in
theorem maskAt_ov_fill (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    CanonicalRef.maskAt (raw (ov a (restDepth a R) R x)) zeroMessages a=
      CanonicalRef.maskAt (raw (fill a R (evaluate x.1 (ovSeed a R x.2)))) zeroMessages a := by
  set e := evaluate x.1 (ovSeed a R x.2) with he
  have hdx : CanonicalRef.depth (raw (ov a (restDepth a R) R x)) zeroMessages a=restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hdf : CanonicalRef.depth (raw (fill a R e)) zeroMessages a=restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
  apply CanonicalRef.maskAt_congr
  · intro input hp
    have hn : rowOf a (restDepth a R) input=none := by
      rw [rowOf_none_iff]
      have hh := prefixStep_none hp
      rw [hdx] at hh
      exact hh
    unfold fill
    rw [raw_ov_nonprefix a R x input hn,raw_ov_nonprefix a R _ input hn]
  · intro _; rfl
  · intro _; rfl
  · rw [hdx,hdf]
  · rw [frontierValue_ov hU]
    unfold fill
    rw [frontierValue_ov hU]
    exact (Wots.PrefixGame.evaluate_fill _ _ _).symm

include hU in
theorem messages_ov_fill (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (restDepth a R)) :
    sourceMessages (raw (ov a (restDepth a R) R x))=
      sourceMessages (raw (fill a R (evaluate x.1 (ovSeed a R x.2)))) := by
  rw [←sourceMessages_maskAt (raw (ov a (restDepth a R) R x)) zeroMessages a (Or.inr hleaf),
    maskAt_ov_fill hU a R x,sourceMessages_maskAt _ zeroMessages a (Or.inr hleaf)]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
theorem depth_eq (R : Tables U) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.depth (answers hU R) (sourceMessages (answers hU R)) a=
      CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_eq hU R a.key ha]

theorem wotsSeed_eq (R : Tables U) (lay : Layer) (tree leaf chain : Nat) :
    WCT9.wotsSeed (answers hU R) lay tree leaf chain=WCT9.wotsSeed (raw R) lay tree leaf chain :=
  Wots.Mask.wotsSeed_congr_private (fun _ => rfl) _ _ _ _

theorem chain_eq (R : Tables U) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    evalWithAnswerFn (answers hU R) (chain lay tree leaf i start count v)=
      evalWithAnswerFn (raw R) (chain lay tree leaf i start count v) :=
  ((SigGolfCandidate.T3.Security.Wots.Enc.respects_chain lay tree leaf i start count v)
    _ _ (nonEnc hU R)).1

/-- C3 (#866): `chain_eq` for the chain of the current scheme. -/
theorem chainW_eq (R : Tables U) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    evalWithAnswerFn (answers hU R) (WCT9.chainW lay tree leaf i start count v)=
      evalWithAnswerFn (raw R) (WCT9.chainW lay tree leaf i start count v) :=
  ((ClaudeWCT.W9.T3.Security.Wots.Enc.respects_chainW lay tree leaf i start count v)
    _ _ (nonEnc hU R)).1

theorem frontier_eq (R : Tables U) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key) :
    CanonicalRef.frontierValue (answers hU R) (sourceMessages (answers hU R)) a=
      CanonicalRef.frontierValue (raw R) zeroMessages a := by
  unfold CanonicalRef.frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [depth_eq hU R a ha,wotsSeed_eq,chainW_eq]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open OracleComp OracleSpec
open RawPrefix
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem nonEnc_chainRow (a : ChainAddr) (step : Nat) (v : Digest) :
    SigGolfCandidate.T3.Security.Wots.Enc.NonEnc (.inl (.inr (chainRow a step v))) := by
  change SigGolfCandidate.T3.Security.Wots.Enc.NonEnc (.inl (.inr (chainInput a.key.lay a.key.tree a.key.leaf a.chain step v)))
  simpa only [chainInput_padded] using
    SigGolfCandidate.T3.Security.Wots.Enc.nonEnc_chainInput a.key.lay a.key.tree a.key.leaf a.chain step v

theorem rowOf_encInput (a : ChainAddr) (d : Nat) (e : Wots.Enc.EncIndex) :
    rowOf a d (Wots.Enc.encInput e)=none := by
  cases hh : rowOf a d (Wots.Enc.encInput e) with
  | none => rfl
  | some p =>
    have he := rowOf_some hh
    have hn := nonEnc_chainRow a p.1 p.2
    apply False.elim
    apply hn
    have hc := Wots.Enc.encInput_encHeader e
    rw [he] at hc
    exact hc

theorem answers_chainRow (R : Tables U) (a : ChainAddr) (step : Nat) (v : Digest) :
    answers hU R (.inl (.inr (chainRow a step v)))=raw R (.inl (.inr (chainRow a step v))) :=
  nonEnc hU R _ (nonEnc_chainRow a step v)

theorem answers_ov_prefix (a : ChainAddr) {d : Nat} (hd : d≤256) (R : Tables U) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    answers hU (RawPrefix.ov a d R x) (.inl (.inr (chainRow a i v)))=
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (answers hU R (.inl (.inr (chainRow a i v))))) := by
  rw [answers_chainRow,answers_chainRow,RawPrefix.raw_ov_prefix hU a hd R x]

theorem answers_ov_fill_nonprefix (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) (input : HashInput)
    (hn : rowOf a (RawPrefix.restDepth a R) input=none) :
    answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x) (.inl (.inr input))=
      answers hU (RawPrefix.fill a R (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (RawPrefix.ovSeed a R x.2)))
        (.inl (.inr input)) := by
  let F := RawPrefix.fill a R (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (RawPrefix.ovSeed a R x.2))
  have hm : sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x))=sourceMessages (raw F) :=
    RawPrefix.messages_ov_fill hU a hleaf R x
  have ht : MessageSwap.table zeroMessages (sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
      zeroMessages_fit (sourceMessages_fit _) hU=
      MessageSwap.table zeroMessages (sourceMessages (raw F)) zeroMessages_fit (sourceMessages_fit _) hU := by
    congr 1
  change eagerAnswers U R.1 (MessageSwap.table zeroMessages
      (sourceMessages (raw (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) zeroMessages_fit (sourceMessages_fit _) hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x).2)
        (.inl (.inr input))=
    eagerAnswers U R.1 (MessageSwap.table zeroMessages (sourceMessages (raw F)) zeroMessages_fit
      (sourceMessages_fit _) hU F.2) (.inl (.inr input))
  rw [ht]
  by_cases hu : input∈U
  · rw [SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_mem U R.1 _ ⟨input,hu⟩,
      SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_mem U R.1 _ ⟨input,hu⟩]
    by_cases he : ∃e,Wots.Enc.encInput e=input
    · obtain ⟨e,he⟩:=he
      have hh : (⟨input,hu⟩ : U)=⟨Wots.Enc.encInput e,hU (Wots.Enc.encInput_short e)⟩ := Subtype.ext he.symm
      rw [hh,MessageSwap.table_at,MessageSwap.table_at]
      change RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 x.1 _=RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 _ _
      rw [RawPrefix.ovPub_none _ _ _ _ (rowOf_encInput _ _ _),RawPrefix.ovPub_none _ _ _ _ (rowOf_encInput _ _ _)]
    · push_neg at he
      rw [MessageSwap.table_other _ _ _ _ _ _ _ he,MessageSwap.table_other _ _ _ _ _ _ _ he]
      change RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 x.1 ⟨input,hu⟩=RawPrefix.ovPub a (RawPrefix.restDepth a R) R.2 _ ⟨input,hu⟩
      rw [RawPrefix.ovPub_none _ _ _ _ hn,RawPrefix.ovPub_none _ _ _ _ hn]
  · rw [SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_not_mem U R.1 _ input hu,
      SigGolfCandidate.T3.Security.Wots.Enc.eagerAnswers_public_not_mem U R.1 _ input hu]
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem maskAt_ov_fill (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (hleaf : a.key.leaf<2^24) (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) :
    CanonicalRef.maskAt (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a=
    CanonicalRef.maskAt (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))))
      (sourceMessages (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))))) a := by
  let F := RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))
  have hdx : CanonicalRef.depth (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a=RawPrefix.restDepth a R := by
    rw [depth_eq hU _ a ha,←RawPrefix.restDepth_eq,RawPrefix.restDepth_ov]
  have hdf : CanonicalRef.depth (answers hU F) (sourceMessages (answers hU F)) a=RawPrefix.restDepth a R := by
    rw [depth_eq hU F a ha,←RawPrefix.restDepth_eq]
    exact RawPrefix.restDepth_ov a R _
  apply CanonicalRef.maskAt_congr
  · intro input hp
    apply answers_ov_fill_nonprefix hU a hleaf R x input
    rw [rowOf_none_iff]
    have hh := RawPrefix.prefixStep_none hp
    rw [hdx] at hh
    exact hh
  · intro coin
    rw [nonEnc hU _ _ (by trivial),nonEnc hU _ _ (by trivial)]
    rfl
  · intro coordinate
    rw [nonEnc hU _ _ (by trivial),nonEnc hU _ _ (by trivial)]
    rfl
  · exact hdx.trans hdf.symm
  · rw [frontier_eq hU _ a ha,frontier_eq hU _ a ha,
      RawPrefix.frontierValue_ov hU]
    unfold RawPrefix.fill
    rw [RawPrefix.frontierValue_ov hU]
    exact (Wots.PrefixGame.evaluate_fill _ _ _).symm

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Route
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (prefixBase otherBase : Answers) :
    QueryImpl RefWorld (OracleComp (SeedSpec d))
  | .inl (.inl n) => liftM ((SeedSpec d).query (.inl n))
  | .inl (.inr input) =>
      match rowOf a d input with
      | some p => (fun w => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (prefixBase (.inl (.inr input))))) <$>
          liftM ((SeedSpec d).query (.inr p))
      | none => pure (otherBase (.inl (.inr input)))
  | .inr _ => pure ()
theorem route_step_observed (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (prefixBase otherBase : Answers)
    (tables : Fin d → Digest → Digest) (input : RefWorld.Domain) (observed : Fin d → Digest → Option Digest)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (routeImpl a d prefixBase otherBase input)
      observed).support) (i : Fin d) (v : Digest) :
    result.2 i v = if input = .inl (.inr (chainRow a i v)) then some (tables i v) else observed i v := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
    simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simp
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        rw [if_neg]
        intro he
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
        simp only [observedImpl, StateT.run_mk, PMF.pure_bind, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        have hin := rowOf_some hp
        simp only [record]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [Function.update_self, hin, if_true]
        · have hne : input ≠ chainRow a i v := by
            rw [hin]
            intro he
            obtain ⟨hs, hv⟩ := chainRow_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          rw [if_neg (fun he => hne (Sum.inr.inj (Sum.inl.inj he)))]
          by_cases h1 : i = p.1
          · subst h1
            have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
            simp only [Function.update_self, Function.update_of_ne h2]
          · simp only [Function.update_of_ne h1]
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simp
theorem observed_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (prefixBase otherBase : Answers)
    (tables : Fin d → Digest → Digest) {β : Type} (computation : OracleComp RefWorld β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : (β × List RefWorld.Domain) × (Fin d → Digest → Option Digest)),
      result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables
        (simulateQ (routeImpl a d prefixBase otherBase) (SphincsSecurity.QueryCap.recorded computation)) observed).support →
      ∀ (i : Fin d) (v : Digest), result.2 i v =
        if (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ result.1.2 then some (tables i v) else observed i v := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr i v
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      simp only [List.not_mem_nil, if_false]
  | query_bind input next ih =>
      intro observed result hr i v
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query, observedRun_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [simulateQ_bind, observedRun_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨tail, htail, hr⟩ := hr
      simp only [simulateQ_pure, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
        PMF.mem_support_pure_iff] at hr
      subst hr
      have hstep := route_step_observed a hd prefixBase otherBase tables input observed middle hmiddle i v
      have htl := ih middle.1 middle.2 tail htail i v
      simp only [List.mem_cons]
      rw [htl, hstep]
      by_cases h1 : (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ tail.1.2
      · simp only [h1, or_true, if_true]
      · simp only [h1, if_false, or_false]
        by_cases h2 : input = .inl (.inr (chainRow a i v))
        · simp only [h2, if_true]
        · simp only [h2, if_false]
          rw [if_neg (fun he => h2 he.symm)]
theorem route_step_count (a : ChainAddr) {d : Nat} (prefixBase otherBase : Answers) (input : RefWorld.Domain)
    (first : RefWorld.Range input × Nat)
    (hfirst : first ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (routeImpl a d prefixBase otherBase input))) :
    first.2 = if PrefixQuery a d input then 1 else 0 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_query, support_map, Set.mem_image] at hfirst
    obtain ⟨answer, -, rfl⟩ := hfirst
    rw [if_neg, if_neg]
    · rintro ⟨i, v, he⟩
      cases he
    · exact fun h => h
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
        subst hfirst
        rw [if_neg]
        rintro ⟨i, v, he⟩
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_map, SphincsSecurity.QueryCap.counted_query,
          support_map, Set.mem_image] at hfirst
        obtain ⟨⟨answer, count⟩, hcount, rfl⟩ := hfirst
        obtain ⟨w, -, hw⟩ := hcount
        simp only [Prod.mk.injEq] at hw
        dsimp only
        rw [← hw.2, if_pos (show (IsPrefixQuery (Sum.inr p : (SeedSpec d).Domain) : Prop) from trivial),
          if_pos ⟨p.1, p.2, by rw [rowOf_some hp]⟩]
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
    subst hfirst
    rw [if_neg]
    rintro ⟨i, v, he⟩
    cases he
theorem counted_rows (a : ChainAddr) {d : Nat} (prefixBase otherBase : Answers) {β : Type}
    (computation : OracleComp RefWorld β) :
    ∀ result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (routeImpl a d prefixBase otherBase) (SphincsSecurity.QueryCap.recorded computation))),
      result.2 = SphincsSecurity.QueryCap.calls (PrefixQuery a d) result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro result hr
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      rfl
  | query_bind input next ih =>
      intro result hr
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨second, hsecond, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst hr
      rw [simulateQ_bind, SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hsecond
      obtain ⟨tail, htail, hsecond⟩ := hsecond
      simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, pure_bind, mem_support_pure_iff] at hsecond
      subst hsecond
      have hstep := route_step_count a prefixBase otherBase input first hfirst
      have htl := ih first.1 tail htail
      simp only [SphincsSecurity.QueryCap.calls_cons, hstep, htl, Nat.add_zero]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Route

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem referenceGame_fill (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) adversary q=
    PairedReference.referenceGame (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))) adversary q := by
  rw [←CanonicalRef.referenceGame_maskAt _ a htree hleaf,maskAt_ov_fill hU a ha hleaf R x,
    CanonicalRef.referenceGame_maskAt _ a htree hleaf]

noncomputable def seedGame (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (a : ChainAddr) (R : Tables U) (endpoint : Digest) : OracleComp (SeedSpec (RawPrefix.restDepth a R)) SeedResult :=
  simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R) (answers hU (RawPrefix.fill a R endpoint)))
    (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers hU (RawPrefix.fill a R endpoint)) adversary q))

theorem fixed_route (a : ChainAddr) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) :
    ((fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) ∘ₛ
      Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R)
        (answers hU (RawPrefix.fill a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))))=
    (SphincsSecurity.Concrete.OtsPrefix.uniformImpl ∘ₛ
      refImpl (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) := by
  have hd : RawPrefix.restDepth a R≤256 := by have := RawPrefix.restDepth_le a R;omega
  funext query
  rcases query with (n | input) | u
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl,simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl]
    cases hp : rowOf a (RawPrefix.restDepth a R) input with
    | none =>
      simp only [simulateQ_pure]
      rw [answers_ov_fill_nonprefix hU a hleaf R x input hp]
    | some p =>
      have hin := rowOf_some hp
      simp only [simulateQ_map,simulateQ_spec_query,simulateQ_pure]
      simp only [fixedImpl,QueryImpl.add_apply_inr]
      rw [hin,answers_ov_prefix hU a hd R x p.1 p.2,←PMF.monad_pure_eq_pure,map_pure]
  · simp only [QueryImpl.apply_compose,Route.routeImpl,refImpl,simulateQ_pure]

theorem fixed_seedGame (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (htree : a.key.tree<2^40) (hleaf : a.key.leaf<2^24)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (seedGame hU adversary q a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))=
      (liftM (PairedReference.offlineRun (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) adversary q) : PMF SeedResult) := by
  unfold seedGame
  rw [←QueryImpl.simulateQ_compose,fixed_route hU a hleaf R x,
    ←referenceGame_fill hU a ha htree hleaf R x adversary q,QueryImpl.simulateQ_compose]
  rfl

noncomputable def seedCost (a : ChainAddr) (R : Tables U) (result : SeedResult) : Nat :=
  SphincsSecurity.QueryCap.calls (PrefixQuery a (RawPrefix.restDepth a R)) result.2

theorem seedGame_charge (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (a : ChainAddr) (R : Tables U) (endpoint : Digest) (result : SeedResult×Nat)
    (h : result∈support (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame hU adversary q a R endpoint))) :
    result.2=seedCost a R result.1 := by
  unfold seedGame at h
  change result.2=SphincsSecurity.QueryCap.calls (PrefixQuery a (RawPrefix.restDepth a R)) result.1.2
  exact Route.counted_rows a (answers hU R) (answers hU (RawPrefix.fill a R endpoint))
    (PairedReference.referenceGame (answers hU (RawPrefix.fill a R endpoint)) adversary q) result h
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame
open SphincsSecurity.Concrete.PartialChainEndpoint (fixedImpl evaluate observedRun IsPrefixQuery realRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem referenceGame_queryBound (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    (PairedReference.referenceGame T adversary q).IsQueryBoundP RefCharged q := by
  unfold PairedReference.referenceGame
  exact SphincsSecurity.QueryCap.run_queryBound RefCharged (PairedReference.offlineGame T adversary) q
theorem seedGame_real_cost (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr) (R : Tables U)
    (result : Digest × (SeedResult × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)))
    (h : result ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame hU adversary q a R)
      (fun _ _ => none)).support) :
    seedCost a R result.2.1 ≤ q := by
  have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame hU adversary q a R) (fun _ _ => none) result h
  have hseed : result.2.1 ∈ support (seedGame hU adversary q a R result.1) := by
    revert hlazy
    exact lazyRun_mem_support (seedGame hU adversary q a R result.1) (fun _ _ => none) result.2
  have hrec : result.2.1 ∈ support (SphincsSecurity.QueryCap.recorded
      (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) := by
    unfold seedGame at hseed
    revert hseed
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU R) (answers hU (RawPrefix.fill a R result.1)))
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) result.2.1
  have hcount : (result.2.1.1, SphincsSecurity.QueryCap.calls RefCharged result.2.1.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged
        (PairedReference.referenceGame (answers hU (RawPrefix.fill a R result.1)) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result.2.1, hrec, rfl⟩
  have hbound := referenceGame_queryBound (answers hU (RawPrefix.fill a R result.1)) adversary q
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q hbound _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
