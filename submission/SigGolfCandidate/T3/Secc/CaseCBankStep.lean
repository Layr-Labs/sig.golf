import SigGolfCandidate.T3.Secc.CaseCBankReuse

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankStep : DecidableEq T3.Cache := Classical.decEq _
theorem lazy_of_recorded {α : Type} (program : M α) (s : QueryRecorded.State) :
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
      LazyPrivate.run program (lazyOf s) := by
  calc
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
        Prod.map id Prod.snd <$> (Prod.map id MonitoredPrivate.State.source <$>
          (Prod.map id QueryRecorded.State.base <$> QueryRecorded.run program s)) := by
      simp only [Functor.map_map]
      rfl
    _ = LazyPrivate.run program (lazyOf s) := by
      rw [QueryRecorded.run_erasure, MonitoredPrivate.run_erasure, CountedPrivate.run_erasure]
      rfl
theorem expected_recorded {α : Type} (program : M α) (s : QueryRecorded.State)
    (f : α × LazyPrivate.State → ENNReal) :
    expectedValue (QueryRecorded.run program s) (fun r => f (r.1, lazyOf r.2)) =
      expectedValue (LazyPrivate.run program (lazyOf s)) f := by
  rw [← lazy_of_recorded, expectedValue_map]
theorem recorded_lazy_support {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) :
    (r.1, lazyOf r.2) ∈ support (LazyPrivate.run program (lazyOf s)) := by
  rw [← lazy_of_recorded, support_map]
  exact ⟨r, hr, rfl⟩
theorem recorded_count_le {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) : countOf s ≤ countOf r.2 :=
  CreationGame.recorded_count_monotone program s r hr
noncomputable def bankValue (g : Ghost) : ENNReal :=
  (g.targets.map fun N => forecast (horizon - g.exposures.length) g.exposures N).sum
noncomputable def excessTerm (budget count : Nat) (g : Ghost) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * excessForecast (horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + reusePotential lazy
  else bankValue g + reusePotential lazy + excessTerm budget count g
noncomputable def potential (budget : Nat) (st : BankState) : ENNReal :=
  livePotential budget (countOf st.2) st.1 (lazyOf st.2)
theorem expectedValue_liftM {α : Type} (X : ProbComp α) (g : α → ENNReal) :
    expectedValue (liftM X : PMF α) g = expectedValue X g := by
  unfold expectedValue
  rfl
theorem expectedValue_pmf_map {α β : Type} (X : PMF α) (f : α → β) (g : β → ENNReal) :
    expectedValue (X.map f) g = expectedValue X (fun x => g (f x)) := by
  rw [← PMF.monad_map_eq_map, expectedValue_map]
theorem lazy_world_coin (n : Nat) (lazy : LazyPrivate.State)
    (r : SphincsSecurity.OracleWorld.Range (.inl n) × LazyPrivate.State)
    (hr : r ∈ support (LazyPrivate.run (forwardWorld (.inl n)) lazy)) : r.2 = lazy := by
  change r ∈ support (LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) lazy) at hr
  rw [LazyPrivate.run_query] at hr
  simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  change step ∈ support ((fun answer => (answer, lazy.2)) <$>
    ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
  rw [support_map] at hstep
  obtain ⟨_, _, rfl⟩ := hstep
  rfl
theorem lazy_world_cached (x : HashInput) (lazy : LazyPrivate.State) (a0 : HashOutput) (hx : lazy.2 x = some a0) :
    LazyPrivate.run (forwardWorld (.inr x)) lazy = pure (a0, lazy) := by
  change LazyPrivate.run (Sampling.publicHandler x) lazy = _
  rw [LazyPrivate.run_publicQuery, randomOracle.run_eq, hx]
  simp
theorem lazy_world_fresh (x : HashInput) (lazy : LazyPrivate.State) (hx : lazy.2 x = none)
    (f : HashOutput × LazyPrivate.State → ENNReal) :
    expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lazy) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => f (a, (lazy.1, lazy.2.cacheQuery x a))) := by
  change expectedValue (LazyPrivate.run (Sampling.publicHandler x) lazy) f = _
  rw [LazyPrivate.run_publicQuery, expectedValue_bind]
  simp only [expectedValue_pure]
  exact Sampling.expectedValue_fresh x lazy.2 hx (fun result => f (result.1, (lazy.1, result.2)))
theorem digestRowOf_isDigest {x : HashInput} {m : Message} (h : DigestRowOf x m) : IsDigestInput x := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨p.1, m, BitVec.ofNat 32 p.2.val, rfl⟩
theorem expectedValue_list_sum {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]
end SigGolfCandidate.T3.Security.CaseC
