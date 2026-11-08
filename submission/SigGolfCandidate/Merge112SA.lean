import SigGolfCandidate.Merge112S0
set_option debug.skipKernelTC true
set_option linter.all false

/-! # Z5 (A): per-chain kernels of the pre/post-marker split, family charge

For a source chain `a` and its marker stop `fun T trace => Restart.MarkerAt T trace a`:

* `markerFirst_split_leF`: contact after the first marker, charged `preCount + 2·(prefixCount - preCount)` on marked
  runs. This is `FamRestart2.source_contactAfterStop_chargeF` without the weakening
  `queryCount pre + 2·post ≤ 2·seedCost` (`Restart.checkpoint_charge`): the kernel
  `realCheckpointRun_contact_charge` already gives the split charge.
* `preContact_cost_leF`, `preTwoEdge_cost_leF`: the contact / two-edge kernels on the paused game (`seedBefore`,
  the run up to the first marker), charged to the pre-marker prefix count. These are the paused versions of
  `FamContacts.contactAt_cost_leF` / `twoEdgeAt_cost_leF`. -/

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec ENNReal
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}


open SigGolfCandidate.T3.Security.Wots.PrefixGame (Hidden stepTrace)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun idealRun lazyRun Contact TwoEdgeEvent
  IsPrefixQuery queryCount realCheckpointRun)
attribute [local irreducible] CanonicalRef.Normalized.raw CanonicalRef.Normalized.normalize
  CanonicalRef.Normalized.answers RawPrefix.fill PairedReference.referenceGame PairedReference.offlineGame

/-! ### Memory rows and the paused count -/

/-- Chain-`a` prefix rows (steps below `d`) of a memory, with repetitions. -/
noncomputable def memRows (a : ChainAddr) (d : Nat) (memory : List Entry) : Nat :=
  (memory.filter fun e => decide (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d (.inl (.inr e.1)))).length

theorem memRows_nil (a : ChainAddr) (d : Nat) : memRows a d [] = 0 := rfl

theorem memRows_zero (a : ChainAddr) (memory : List Entry) : memRows a 0 memory = 0 := by
  unfold memRows
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e _ h
  simp only [decide_eq_true_eq] at h
  obtain ⟨i, -, -⟩ := h
  exact i.elim0

theorem memRows_pos_depth {a : ChainAddr} {d : Nat} {memory : List Entry} (h : 0 < memRows a d memory) : 1 ≤ d := by
  cases d with
  | zero => rw [memRows_zero] at h; omega
  | succ d => omega

theorem memRows_stepTrace (a : ChainAddr) (d : Nat) (input : RefWorld.Domain) (answer : RefWorld.Range input)
    (memory : List Entry) :
    memRows a d (stepTrace input answer memory) =
      memRows a d memory + if ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d input then 1 else 0 := by
  unfold memRows stepTrace
  rw [List.filter_append, List.length_append]
  congr 1
  rcases input with (n | input) | u
  · rw [if_neg (by rintro ⟨i, v, he⟩; cases he)]
    rfl
  · by_cases h : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d (.inl (.inr input))
    · rw [if_pos h]
      simp only [SigGolfCandidate.T3.Security.Wots.PrefixGame.entryOf, List.filter_cons, List.filter_nil,
        decide_eq_true h, if_true, List.length_singleton]
    · rw [if_neg h]
      simp only [SigGolfCandidate.T3.Security.Wots.PrefixGame.entryOf, List.filter_cons, List.filter_nil,
        decide_eq_false h, List.length_nil]
      rfl
  · rw [if_neg (by rintro ⟨i, v, he⟩; cases he)]
    rfl

/-- The prefix queries of the paused run are the chain-`a` prefix rows its memory gains. -/
theorem paused_counted_rows (a : ChainAddr) {d : Nat} (prefixBase otherBase : Answers) (stop : List Entry → Prop)
    {γ : Type} (computation : OracleComp RefWorld γ) :
    ∀ (memory : List Entry) result, result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (Route.routeImpl a d prefixBase otherBase)
          (SphincsSecurity.QueryPause.run stop stepTrace computation memory))) →
      result.2 + memRows a d memory = memRows a d result.1.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro memory result hr
      simp only [SphincsSecurity.QueryPause.run_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      simp only [Nat.zero_add]
  | query_bind input next ih =>
      intro memory result hr
      rw [SphincsSecurity.QueryPause.run_query_bind] at hr
      by_cases hs : stop memory
      · rw [if_pos hs] at hr
        simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hr
        subst hr
        simp only [Nat.zero_add]
      · rw [if_neg hs, simulateQ_bind, simulateQ_spec_query, SphincsSecurity.QueryCap.counted_bind,
          mem_support_bind_iff] at hr
        obtain ⟨first, hfirst, hr⟩ := hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨second, hsecond, hr⟩ := hr
        rw [mem_support_pure_iff] at hr
        subst hr
        have hstep := Route.route_step_count a prefixBase otherBase input first hfirst
        have htl := ih first.1 _ second hsecond
        rw [memRows_stepTrace] at htl
        show first.2 + second.2 + memRows a d memory = memRows a d second.1.1
        by_cases hq : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d input
        · rw [if_pos hq] at hstep htl
          omega
        · rw [if_neg hq] at hstep htl
          omega

theorem lt_split_depth {a : ChainAddr} {d : Nat} {m : List Entry} {qs : List RefWorld.Domain} {k : Nat}
    (hk : k < memRows a d m + 2 * (SphincsSecurity.QueryCap.calls
      (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d) qs - memRows a d m)) : 1 ≤ d := by
  cases d with
  | zero => rw [ClaudeWCT.W9.T3.Security.Wots.Leaf.calls_prefixQuery_zero, memRows_zero] at hk; omega
  | succ d => omega

/-! ### Checkpoint facts of the paused prefix game -/

section Checkpoint
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

theorem seedBefore_rows (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (stop : List Entry → Prop) (endpoint : Digest) (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat)
    (h : middle ∈ support (Restart.seedBefore adversary q a R stop endpoint)) :
    middle.2 = memRows a (RawPrefix.restDepth a R) middle.1.1 := by
  have h' := paused_counted_rows a (answers (referenceInputs_subset adversary) R) (Restart.fillTable a R endpoint) stop
    (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (Restart.fillTable a R endpoint) adversary q))
    [] middle h
  rw [memRows_nil, Nat.add_zero] at h'
  exact h'

theorem checkpoint_total (q : Nat) (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (stop : List Entry → Prop) (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (Restart.seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (Restart.seedAfter a R endpoint middle.1)) middle.2).support) :
    middle.1.2 + result.1.2 = CanonicalRef.Normalized.seedCost a R result.1.1 ∧
      CanonicalRef.Normalized.seedCost a R result.1.1 ≤ q := by
  have hcomp : (do
      let m ← Restart.seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (Restart.seedAfter a R endpoint m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery
        (CanonicalRef.Normalized.seedGame (referenceInputs_subset adversary) adversary q a R endpoint) := by
    unfold Restart.seedBefore Restart.seedAfter CanonicalRef.Normalized.seedGame Restart.routeImpl Restart.fillTable
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (answers (referenceInputs_subset adversary)
        (RawPrefix.fill a R endpoint)) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery
          (CanonicalRef.Normalized.seedGame (referenceInputs_subset adversary) adversary q a R endpoint))
        (fun _ _ => none)).support := by
    rw [← hcomp, SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hmem := SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_mem_support _ _ _ hfull
  have hc := CanonicalRef.Normalized.seedGame_charge (referenceInputs_subset adversary) adversary q a R endpoint _ hmem
  have hs := Restart.seedGame_support_cost q a R endpoint result.1.1 (by
    have := SphincsSecurity.QueryCap.counted_forget IsPrefixQuery
      (CanonicalRef.Normalized.seedGame (referenceInputs_subset adversary) adversary q a R endpoint)
    rw [← this, support_map]
    exact ⟨_, hmem, rfl⟩)
  simp only at hc
  exact ⟨hc, hs⟩

theorem restart_proj (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary)) :
    (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e)
      (fun e middle => Restart.seedAfter a R e middle.1) (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
        (fun _ _ => none) := by
  have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
    (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e)
    (fun e middle => Restart.seedAfter a R e middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
  rw [h]
  congr 1
  funext e
  exact Restart.seedBefore_after q a R (Restart.stopAt Stop a R e) e

theorem restart_memRows_le (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)))
    (hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (Restart.restartGame adversary q a Stop R) (fun _ _ => none)).support) :
    memRows a (RawPrefix.restDepth a R) r.2.1.1 ≤ CanonicalRef.Normalized.seedCost a R r.2.1.2 := by
  rw [← restart_proj q a Stop R, PMF.mem_support_map_iff] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  obtain ⟨hm1, hm2⟩ := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support _ _ _ _ r' hr'
  have hrows := seedBefore_rows q a R _ r'.1 r'.2.1.1
    (SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_mem_support _ _ _ hm1)
  have htot := (checkpoint_total q a R _ r'.1 r'.2.1 hm1 r'.2.2 hm2).1
  show memRows a _ r'.2.1.1.1.1 ≤ CanonicalRef.Normalized.seedCost a R r'.2.2.1.1
  omega

end Checkpoint

/-! ### Pre-marker contacts and two-edges: the paused run before the stop -/

/-- A contact of chain `a` (depth `d`, frontier `e`) in a memory. -/
def memContact (a : ChainAddr) (d : Nat) (e : Digest) (memory : List Entry) : Prop :=
  1 ≤ d ∧ ∃ value, ClaudeWCT.W9.T3.Security.Wots.SeenRowW memory a (d - 1) value e

/-- A two-edge of chain `a` (depth `d`, frontier `e`) in a memory. -/
def memTwoEdge (a : ChainAddr) (d : Nat) (e : Digest) (memory : List Entry) : Prop :=
  2 ≤ d ∧ ∃ start middle, ClaudeWCT.W9.T3.Security.Wots.SeenRowW memory a (d - 2) start middle ∧
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW memory a (d - 1) middle e

theorem contact_iff_mem (a : ChainAddr) {d : Nat} (e : Digest) (memory : List Entry)
    (observed : Fin d → Digest → Option Digest)
    (hinv : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed) :
    Contact observed e ↔ memContact a d e memory := by
  unfold Contact memContact
  constructor
  · rintro ⟨i, hi, value, h⟩
    obtain ⟨answer, hm, hl⟩ := (hinv i value e).mp h
    have he : d - 1 = i.val := by omega
    exact ⟨by omega, value, answer, by rw [he]; exact hm, by rw [he]; exact hl⟩
  · rintro ⟨hd, value, answer, hm, hl⟩
    exact ⟨⟨d - 1, by omega⟩, by simp only; omega, value, (hinv _ value e).mpr ⟨answer, hm, hl⟩⟩

theorem twoEdge_iff_mem (a : ChainAddr) {d : Nat} (e : Digest) (memory : List Entry)
    (observed : Fin d → Digest → Option Digest)
    (hinv : ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed) :
    TwoEdgeEvent observed e ↔ memTwoEdge a d e memory := by
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.twoEdgeEvent_iff_rows]
  unfold memTwoEdge
  constructor
  · rintro ⟨⟨i, start⟩, ⟨j, middle⟩, hi, hj, h1, h2⟩
    simp only at hi hj h1 h2
    obtain ⟨a1, m1, l1⟩ := (hinv i start middle).mp h1
    obtain ⟨a2, m2, l2⟩ := (hinv j middle e).mp h2
    have hi' : d - 2 = i.val := by omega
    have hj' : d - 1 = j.val := by omega
    refine ⟨by omega, start, middle, ⟨a1, ?_, ?_⟩, ⟨a2, ?_, ?_⟩⟩
    · rw [hi']; exact m1
    · rw [hi']; exact l1
    · rw [hj']; exact m2
    · rw [hj']; exact l2
  · rintro ⟨hd, start, middle, ⟨a1, m1, l1⟩, ⟨a2, m2, l2⟩⟩
    exact ⟨(⟨d - 2, by omega⟩, start), (⟨d - 1, by omega⟩, middle), by simp only; omega, by simp only; omega,
      (hinv _ start middle).mpr ⟨a1, m1, l1⟩, (hinv _ middle e).mpr ⟨a2, m2, l2⟩⟩

/-! ### MarkerFirst: the split charge per rest table -/

/-- The split charge of a paused-game outcome: pre-stop prefix rows once, post-stop prefix queries twice. -/
noncomputable def splitCost (a : ChainAddr) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))) : Nat :=
  memRows a (RawPrefix.restDepth a R) r.2.1.1 +
    2 * (CanonicalRef.Normalized.seedCost a R r.2.1.2 - memRows a (RawPrefix.restDepth a R) r.2.1.1)

/-- **Per rest table: contact after the stop, against the split charge.** -/
theorem split_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceLeaf7 a.key)
    (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary)) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
        (fun _ _ => none) r * ((splitCost a R r : ENNReal) * (if Restart.genStop Stop a R r then 1 else 0)) := by
    let before := fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e
    let after := fun (endpoint : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => Restart.seedAfter a R endpoint middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) =>
        Restart.stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
        (fun _ _ => none)).map (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none) := restart_proj q a Stop R
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support
      (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none) r hr
    have hc : Pr[Restart.genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun
          (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := Restart.checkpoint_rows q a R (Restart.stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (Restart.stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Restart.ContactAt (Restart.fillTable a R r.1) r.2.1.1.1.1 a ∧
          Contact r.2.2.2 r.1) ↔
        ((Restart.stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [Restart.contact_iff_rowsInv a ha R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_charge
      (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (Restart.checkpoint_budget q a R (Restart.stopAt Stop a R e) e middle hmiddle result hresult).2)
    rw [SigGolfCandidate.T3.Security.Wots.card_digest] at hkernel
    rw [hc]
    refine hkernel.trans ?_
    have hexp : (∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none) r *
          ((splitCost a R r : ENNReal) * (if Restart.genStop Stop a R r then 1 else 0))) =
        ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
          (fun _ _ => none) r * ((splitCost a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) : ENNReal) *
            (if Restart.genStop Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) then 1 else 0)) := by
      rw [← hproj, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
    refine le_of_le_of_eq ?_ hexp.symm
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
        (fun _ _ => none)).support
    · apply mul_le_mul' le_rfl
      obtain ⟨hm1, hm2⟩ := hsupp r hr
      have hrows := seedBefore_rows q a R (Restart.stopAt Stop a R r.1) r.1 r.2.1.1
        (SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_mem_support _ _ _ hm1)
      have htot := (checkpoint_total q a R (Restart.stopAt Stop a R r.1) r.1 r.2.1 hm1 r.2.2 hm2).1
      have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
        SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) r.2.1 hm1
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
      by_cases hm : marked r.1 r.2.1
      · rw [if_pos hm, mul_one]
        have hgs : Restart.genStop Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := hm.1
        rw [if_pos hgs, mul_one]
        have hsc : queryCount r.2.1.2 + 2 * r.2.2.1.2 ≤ splitCost a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := by
          show _ ≤ memRows a _ r.2.1.1.1.1 + 2 * (CanonicalRef.Normalized.seedCost a R r.2.2.1.1 -
            memRows a _ r.2.1.1.1.1)
          omega
        exact_mod_cast hsc
      · rw [if_neg hm, mul_zero]
        exact bot_le
    · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]

/-! ### Couplings of the pre-marker trace -/

theorem markerAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : Restart.MarkerAt T (trace.take j) a) : Restart.MarkerAt T (trace.take k) a := by
  obtain ⟨message, counter, pad, answer, digits, hfit, hm, h⟩ := h
  exact ⟨message, counter, pad, answer, digits, hfit, (List.take_prefix_take_left hjk).subset hm, h⟩

theorem twoEdgeAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : CanonicalRef.TwoEdgeAt T (sourceMessages T) (trace.take j) a) :
    CanonicalRef.TwoEdgeAt T (sourceMessages T) (trace.take k) a := by
  obtain ⟨hd, start, middle, ⟨a1, h1, l1⟩, ⟨a2, h2, l2⟩⟩ := h
  exact ⟨hd, start, middle, ⟨a1, (List.take_prefix_take_left hjk).subset h1, l1⟩,
    ⟨a2, (List.take_prefix_take_left hjk).subset h2, l2⟩⟩

/-- A pre-marker event of a monotone trace property holds on the pre-marker trace. -/
theorem pre_mono (T : Answers) (trace : List Entry) (a : ChainAddr) (P : List Entry → Prop)
    (hP : ∀ j k, j ≤ k → P (trace.take j) → P (trace.take k))
    (h : ∃ k, P (trace.take k) ∧ ¬Restart.MarkerAt T (trace.take k) a) :
    P (trace.take (stopIdx T trace a)) := by
  obtain ⟨k, hk, hnk⟩ := h
  unfold stopIdx
  split_ifs with hm
  · refine hP k _ ?_ hk
    by_contra hlt
    exact hnk (markerAt_take_mono T trace a (by omega) (Nat.find_spec hm))
  · rcases le_total k trace.length with hkl | hkl
    · exact hP _ _ hkl hk
    · rw [List.take_of_length_le hkl] at hk
      rw [List.take_length]
      exact hk

theorem take_stopIdx_eq (T : Answers) (a : ChainAddr) {trace memory : List Entry}
    (hm : memory = trace.take memory.length)
    (hb : ∀ j, j < memory.length → ¬Restart.MarkerAt T (trace.take j) a)
    (hc : Restart.MarkerAt T memory a ∨ memory = trace) :
    trace.take (stopIdx T trace a) = memory := by
  unfold stopIdx
  split_ifs with h
  · have hS : Restart.MarkerAt T memory a :=
      (SigGolfCandidate.T3.Security.Wots.PrefixGame.first_stop_exists_iff (fun l => Restart.MarkerAt T l a)
        hm hb hc).mp h
    have hle : Nat.find h ≤ memory.length := Nat.find_min' h (by rw [← hm]; exact hS)
    have hge : memory.length ≤ Nat.find h := by
      by_contra hlt
      exact hb _ (by omega) (Nat.find_spec h)
    rw [le_antisymm hle hge]
    exact hm.symm
  · rcases hc with hc | hc
    · exact absurd ⟨memory.length, by rw [← hm]; exact hc⟩ h
    · rw [List.take_length]
      exact hc.symm

section Couple
variable (q : Nat) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a)
  (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
  (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
  (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
    (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R
      (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support)
include ha hmask hres

theorem pre_coupled :
    preTrace (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      res.1.2) a = res.1.1 := by
  obtain ⟨h1, h2, h3⟩ := Restart.coupled_paused q a ha R x
    (Restart.stopAt (fun T trace => Restart.MarkerAt T trace a) a R (evaluate x.1 (RawPrefix.ovSeed a R x.2)))
    res hres
  have hb := Restart.blind_frozen a ha (fun T trace => Restart.MarkerAt T trace a) hmask R x
  exact take_stopIdx_eq _ a h1 (fun j hj hS => h2 j hj ((hb _).mp hS)) (h3.imp_left (hb _).mpr)

theorem preCount_coupled :
    preCount a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      res.1.2) = memRows a (RawPrefix.restDepth a R) res.1.1 := by
  have hp := pre_coupled q ha hmask R x res hres
  have hdepth : CanonicalRef.depth (answers (referenceInputs_subset adversary)
      (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (sourceMessages (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a = RawPrefix.restDepth a R :=
    (CanonicalRef.Normalized.depth_eq (referenceInputs_subset adversary) _ a ha.1).trans
      ((RawPrefix.restDepth_eq a (RawPrefix.ov a (RawPrefix.restDepth a R) R x)).symm.trans
        (RawPrefix.restDepth_ov a R x))
  unfold preCount memRows
  rw [hp]
  congr 1
  apply List.filter_congr
  intro e _
  rw [decide_eq_decide]
  show CanonicalRef.Normalized.PrefixRowAt (answers (referenceInputs_subset adversary)
    (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a e.1 ↔ _
  constructor
  · rintro ⟨step, value, hs, he⟩
    rw [hdepth] at hs
    exact ⟨⟨step, hs⟩, value, by rw [he]⟩
  · rintro ⟨i, v, he⟩
    exact ⟨i, v, by rw [hdepth]; exact i.isLt, Sum.inr.inj (Sum.inl.inj he)⟩

theorem ov_depth : CanonicalRef.depth (answers (referenceInputs_subset adversary)
      (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (sourceMessages (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a = RawPrefix.restDepth a R :=
  (CanonicalRef.Normalized.depth_eq (referenceInputs_subset adversary) _ a ha.1).trans
    ((RawPrefix.restDepth_eq a (RawPrefix.ov a (RawPrefix.restDepth a R) R x)).symm.trans
      (RawPrefix.restDepth_ov a R x))

theorem ov_frontier : CanonicalRef.frontierValue (answers (referenceInputs_subset adversary)
      (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) (sourceMessages (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x))) a = evaluate x.1 (RawPrefix.ovSeed a R x.2) :=
  (CanonicalRef.Normalized.frontier_eq (referenceInputs_subset adversary) _ a ha.1).trans
    (RawPrefix.frontierValue_ov (referenceInputs_subset adversary) a R x)

theorem refContact_coupled :
    CanonicalRef.ContactAt (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
      (preTrace (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        res.1.2) a) a ↔
      memContact a (RawPrefix.restDepth a R) (evaluate x.1 (RawPrefix.ovSeed a R x.2)) res.1.1 := by
  rw [pre_coupled q ha hmask R x res hres]
  unfold CanonicalRef.ContactAt memContact
  rw [ov_depth q ha hmask R x res hres, ov_frontier q ha hmask R x res hres]

theorem refTwoEdge_coupled :
    CanonicalRef.TwoEdgeAt (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
      (sourceMessages (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
      (preTrace (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        res.1.2) a) a ↔
      memTwoEdge a (RawPrefix.restDepth a R) (evaluate x.1 (RawPrefix.ovSeed a R x.2)) res.1.1 := by
  rw [pre_coupled q ha hmask R x res hres]
  unfold CanonicalRef.TwoEdgeAt memTwoEdge
  rw [ov_depth q ha hmask R x res hres, ov_frontier q ha hmask R x res hres]

end Couple

/-! ### MarkerFirst: transfer to the reference experiment -/

section Split
variable (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (q : Nat) {a : ChainAddr}
  (ha : WotsExtract.SourceChain7 a)
include H ha

theorem split_layer_leF (k : ℕ) :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun r => k < splitCost a R r ∧ Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] ≤
      Pr[fun s => k < preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) ∧ Marked a s |
          PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  have hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a :=
    fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2
  have hStopL := FamRestart2.markerAt_stopLF S H.grp_le ha
  have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q (fun T trace => Restart.MarkerAt T trace a)) Prod.snd
    (Restart.GDr_snd q _)
    (fun s => k < preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) ∧ Marked a s)
    (fun d R z => k < memRows a d z.2.1.1 + 2 * (SphincsSecurity.QueryCap.calls
        (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.PrefixQuery a d) z.2.1.2.2 - memRows a d z.2.1.1) ∧
      Restart.MarkerAt (Restart.fillTable a R z.1) z.2.1.1 a)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hk, h1⟩
        exact ⟨hk, (hStopL _ _ (FamRestart2.fill_congrF S H.grp_le ha R (lt_split_depth hk) p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hk, h1⟩
        exact ⟨hk, (hStopL _ _ (FamRestart2.fill_congrF S H.grp_le ha R (lt_split_depth hk) p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by
      have := h.1
      rw [ClaudeWCT.W9.T3.Security.Wots.Leaf.calls_prefixQuery_zero, memRows_zero] at this
      omega)
    (FamRestart2.GDr_famF S H.grp_le q ha _ hStopL)
    (fun R x res hres => by
      have hc := Restart.count_coupled q ha (fun T trace => Restart.MarkerAt T trace a) R x res hres
      have hs := Restart.stop_coupled q a ha (fun T trace => Restart.MarkerAt T trace a) hmask R x res hres
      have hp := preCount_coupled q ha hmask R x res hres
      refine and_congr ?_ hs
      show k < preCount a (mkSample _ res.1.2) + 2 * (CanonicalRef.Normalized.prefixCount a (mkSample _ res.1.2) -
        preCount a (mkSample _ res.1.2)) ↔ _
      rw [hc, hp]
      exact Iff.rfl)
    H.grp_le H.caps H.width H.points
  simp only [Restart.mixLaw_restart] at h
  exact h

theorem split_charge_leF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
          ((splitCost a R r : ENNReal) *
            (if Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r then 1 else 0)) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s *
        (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
          (if Marked a s then 1 else 0)) +
        ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a := by
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
        ((splitCost a R r : ENNReal) *
          (if Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * q), Pr[fun r => k < splitCost a R r ∧
          Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] := by
    intro R
    have h := ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers
      (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none))
      (fun r => if Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r then splitCost a R r else 0)
      (2 * q) (fun r hr => by
        have h1 := Restart.restart_real_cost q a _ R r hr
        have h2 := restart_memRows_le q a _ R r hr
        unfold splitCost
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun r => ?_
    congr 1
    split_ifs <;> simp
  have href : ∑' s, PairedReference.referenceExperiment adversary q s *
        (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
          (if Marked a s then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * q), Pr[fun s => k < preCount a s +
          2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) ∧ Marked a s |
        PairedReference.referenceExperiment adversary q] := by
    have h := ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers (PairedReference.referenceExperiment adversary q)
      (fun s => if Marked a s then preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) else 0)
      (2 * q) (fun s hs => by
        have h1 := (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs)
        have h2 := preCount_le_prefixCount a s
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun s => ?_
    congr 1
    split_ifs <;> simp
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑ k ∈ Finset.range (2 * q),
        Pr[fun r => k < splitCost a R r ∧ Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)]
      = ∑ k ∈ Finset.range (2 * q), ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < splitCost a R r ∧ Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range (2 * q),
          (Pr[fun s => k < preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) ∧ Marked a s |
            PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun k _ => split_layer_leF S H q ha k
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Pre-stop rows: mixture ≤ reference + q · error.** -/
theorem mix_preCount_leF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
          (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
        q * FamLift.errCF S adversary q a := by
  have hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a :=
    fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2
  have hStopL := FamRestart2.markerAt_stopLF S H.grp_le ha
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
        (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) =
      ∑ k ∈ Finset.range q, Pr[fun r => k < memRows a (RawPrefix.restDepth a R) r.2.1.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] :=
    fun R => ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (fun r => memRows a (RawPrefix.restDepth a R) r.2.1.1) q
      (fun r hr => (restart_memRows_le q a _ R r hr).trans (Restart.restart_real_cost q a _ R r hr))
  have href : ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) =
      ∑ k ∈ Finset.range q, Pr[fun s => k < preCount a s | PairedReference.referenceExperiment adversary q] :=
    ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (preCount a) q (fun s hs =>
      (preCount_le_prefixCount a s).trans
        ((LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs)))
  have hlayer : ∀ k, ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
      Pr[fun r => k < memRows a (RawPrefix.restDepth a R) r.2.1.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] ≤
      Pr[fun s => k < preCount a s | PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
    intro k
    have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q (fun T trace => Restart.MarkerAt T trace a))
      Prod.snd (Restart.GDr_snd q _) (fun s => k < preCount a s) (fun d R z => k < memRows a d z.2.1.1)
      (fun _ _ _ _ _ => rfl)
      (fun R z h => by
        have h' : k < memRows a 0 z.2.1.1 := h
        rw [memRows_zero] at h'
        omega)
      (FamRestart2.GDr_famF S H.grp_le q ha _ hStopL)
      (fun R x res hres => by
        show k < preCount a (mkSample _ res.1.2) ↔ k < memRows a _ res.1.1
        rw [preCount_coupled q ha hmask R x res hres])
      H.grp_le H.caps H.width H.points
    simp only [Restart.mixLaw_restart] at h
    exact h
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑ k ∈ Finset.range q,
        Pr[fun r => k < memRows a (RawPrefix.restDepth a R) r.2.1.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)]
      = ∑ k ∈ Finset.range q, ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < memRows a (RawPrefix.restDepth a R) r.2.1.1 |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range q, (Pr[fun s => k < preCount a s | PairedReference.referenceExperiment adversary q] +
          FamLift.errCF S adversary q a) := Finset.sum_le_sum fun k _ => hlayer k
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Split


section Paused
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

/-- The paused run of chain `a`'s prefix game up to the stop (`seedBefore` without its counter). -/
noncomputable def pausedRun (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : Tables (PairedReference.referenceInputs adversary)) (e : Digest) :
    OracleComp (SigGolfCandidate.T3.Security.Wots.PrefixGame.SeedSpec (RawPrefix.restDepth a R))
      (List Entry × OracleComp RefWorld SeedResult) :=
  simulateQ (Restart.routeImpl a (RawPrefix.restDepth a R) R e)
    (SphincsSecurity.QueryPause.run (Restart.stopAt Stop a R e) stepTrace
      (SphincsSecurity.QueryCap.recorded (PairedReference.referenceGame (Restart.fillTable a R e) adversary q)) [])

variable (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
  (R : Tables (PairedReference.referenceInputs adversary))

theorem pausedRun_charge : ∀ e result, result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
    (pausedRun q a Stop R e)) → result.2 ≤ memRows a (RawPrefix.restDepth a R) result.1.1 :=
  fun e result h => le_of_eq (seedBefore_rows q a R _ e result h)

theorem pausedRun_real : ∀ r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
    (pausedRun q a Stop R) (fun _ _ => none)).support, memRows a (RawPrefix.restDepth a R) r.2.1.1 ≤ q := by
  intro r hr
  rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget, PMF.mem_support_map_iff] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  have hl := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r' hr'
  obtain ⟨result, hresult⟩ := (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
    (SphincsSecurity.QueryCap.counted IsPrefixQuery (Restart.seedAfter a R r'.1 r'.2.1)) r'.2.2).support_nonempty
  have hrows := seedBefore_rows q a R _ r'.1 r'.2.1
    (SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_mem_support _ _ _ hl)
  have htot := checkpoint_total q a R _ r'.1 r'.2 hl result hresult
  show memRows a _ r'.2.1.1.1 ≤ q
  omega

/-- A memory event of the paused game is the matching observed-table event of the run before the stop. -/
theorem pausedRun_event (E : Digest → List Entry → Prop)
    (O : Digest → (Fin (RawPrefix.restDepth a R) → Digest → Option Digest) → Prop)
    (hEO : ∀ e memory observed, ClaudeWCT.W9.T3.Security.Wots.PrefixGame.RowsInvW a memory observed →
      (E e memory ↔ O e observed)) :
    Pr[fun r => E r.1 r.2.1.1 | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] =
      Pr[fun r => O r.1 r.2.2 | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (pausedRun q a Stop R) (fun _ _ => none)] := by
  let before := fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e
  let after := fun (endpoint : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
    (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)) => Restart.seedAfter a R endpoint middle.1
  have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none)).map (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
        (fun _ _ => none) := restart_proj q a Stop R
  have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none) r hr
  have hm := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_mark_probability
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none) (fun e m => O e m.2)
  calc Pr[fun r => E r.1 r.2.1.1 | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none)]
      = Pr[fun r => O r.1 r.2.1.2 | realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          before after (fun _ _ => none)] := by
        rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
        apply pmf_probEvent_congr
        intro r hr
        exact hEO r.1 _ _ (Restart.checkpoint_rows q a R _ r.1 r.2.1 (hsupp r hr).1)
    _ = Pr[fun r => O r.1 r.2.2 | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
          (fun _ _ => none)] := hm
    _ = _ := by
        rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget _ (pausedRun q a Stop R),
          ← PMF.monad_map_eq_map, probEvent_map]
        rfl

theorem counted_pausedRun :
    (fun e => SphincsSecurity.QueryCap.counted IsPrefixQuery (pausedRun q a Stop R e)) =
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) := rfl

theorem realRun_counted_pausedRun :
    realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun e => SphincsSecurity.QueryCap.counted IsPrefixQuery (pausedRun q a Stop R e)) (fun _ _ => none) =
    realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none) := by
  rw [counted_pausedRun]

theorem tsum_counted_pausedRun :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun e => SphincsSecurity.QueryCap.counted IsPrefixQuery (pausedRun q a Stop R e)) (fun _ _ => none) r *
        (r.2.1.2 : ENNReal) =
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none) r *
          (r.2.1.2 : ENNReal) := by
  rw [realRun_counted_pausedRun]

theorem before_cost_rows :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none) r *
          (r.2.1.2 : ENNReal) =
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none) r *
          (memRows a (RawPrefix.restDepth a R) r.2.1.1.1 : ENNReal) := by
  refine tsum_congr fun r => ?_
  by_cases hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none)).support
  · rw [seedBefore_rows q a R _ r.1 r.2.1 (SigGolfCandidate.T3.Security.Wots.PrefixGame.lazyRun_mem_support _ _ _
      (SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r hr))]
  · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]

theorem before_cost_checkpoint :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e) (fun _ _ => none) r *
          (memRows a (RawPrefix.restDepth a R) r.2.1.1.1 : ENNReal) =
    ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e)
      (fun e middle => Restart.seedAfter a R e middle.1)
          (fun _ _ => none) r * (memRows a (RawPrefix.restDepth a R) r.2.1.1.1.1 : ENNReal) := by
  rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_before _ _
    (fun e middle => Restart.seedAfter a R e middle.1),
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

theorem checkpoint_cost_restart :
    ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun e => Restart.seedBefore adversary q a R (Restart.stopAt Stop a R e) e)
      (fun e middle => Restart.seedAfter a R e middle.1)
          (fun _ _ => none) r * (memRows a (RawPrefix.restDepth a R) r.2.1.1.1.1 : ENNReal) =
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none) r *
        (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) := by
  rw [← restart_proj q a Stop R, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

/-- The counted prefix queries of the run before the stop, in expectation, are the pre-stop memory rows. -/
theorem pausedRun_cost :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun e => SphincsSecurity.QueryCap.counted IsPrefixQuery (pausedRun q a Stop R e)) (fun _ _ => none) r *
        (r.2.1.2 : ENNReal) =
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none) r *
        (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) := by
  exact (tsum_counted_pausedRun q a Stop R).trans <| (before_cost_rows q a Stop R).trans ((before_cost_checkpoint q a Stop R).trans
    (checkpoint_cost_restart q a Stop R))

/-- **Per rest table: contact before the stop, against the pre-stop prefix rows.** -/
theorem preContact_le_R (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => memContact a (RawPrefix.restDepth a R) r.1 r.2.1.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none) r *
        (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R)
    (fun m => memRows a (RawPrefix.restDepth a R) m.1) q (pausedRun_charge q a Stop R) (pausedRun_real q a Stop R)
    hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R)
    (fun m => memRows a (RawPrefix.restDepth a R) m.1) q (pausedRun_charge q a Stop R) (pausedRun_real q a Stop R)
  rw [SigGolfCandidate.T3.Security.Wots.card_digest] at h2 h3
  rw [pausedRun_event q a Stop R (fun e m => memContact a (RawPrefix.restDepth a R) e m) (fun e o => Contact o e)
    (fun e m o h => (contact_iff_mem a e m o h).symm), ← pausedRun_cost q a Stop R]
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R) (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (pausedRun q a Stop R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (pausedRun q a Stop R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl h3

/-- **Per rest table: two-edge before the stop, against the pre-stop prefix rows.** -/
theorem preTwoEdge_le_R (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => memTwoEdge a (RawPrefix.restDepth a R) r.1 r.2.1.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none) r *
        (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) := by
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have h1 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R)
    (fun m => memRows a (RawPrefix.restDepth a R) m.1) q (pausedRun_charge q a Stop R) (pausedRun_real q a Stop R)
    hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R)
    (fun m => memRows a (RawPrefix.restDepth a R) m.1) q (pausedRun_charge q a Stop R) (pausedRun_real q a Stop R)
  rw [SigGolfCandidate.T3.Security.Wots.card_digest] at h1 h3
  rw [pausedRun_event q a Stop R (fun e m => memTwoEdge a (RawPrefix.restDepth a R) e m) (fun e o => TwoEdgeEvent o e)
    (fun e m o h => (twoEdge_iff_mem a e m o h).symm), ← pausedRun_cost q a Stop R]
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (pausedRun q a Stop R) (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (twoEdgeRate q * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (pausedRun q a Stop R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h1
    _ = twoEdgeRate q * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (pausedRun q a Stop R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl h3

end Paused

/-- **MarkerFirst, split charge.** -/
theorem markerFirst_split_leF (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s *
        (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) * (if Marked a s then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a :=
    fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2
  have hStopL := FamRestart2.markerAt_stopLF S H.grp_le ha
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          (∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
            Pr[Restart.genCAS (fun T trace => Restart.MarkerAt T trace a) a R |
              realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
                (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R)
            (fun _ _ => none)] + FamLift.errCF S adversary q a)) := by
        gcongr
        exact FamRestart2.lower_cas_le_mixF S H.grp_le H.caps H.width H.points q ha _ hmask hStopL
    _ = ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ((1 - (q : ENNReal) / 2 ^ 128) *
          ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS (fun T trace => Restart.MarkerAt T trace a) a R |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R)
            (fun _ _ => none)])) +
          (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
            ((splitCost a R r : ENNReal) *
              (if Restart.genStop (fun T trace => Restart.MarkerAt T trace a) a R r then 1 else 0)) +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (split_le_R q hq a ha.1 _ R))
          (mul_le_mul' hx le_rfl)
    _ ≤ (∑' s, PairedReference.referenceExperiment adversary q s *
          (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
            (if Marked a s then 1 else 0)) +
          ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a) +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        gcongr
        exact split_charge_leF S H q ha
    _ = _ := by ring

/-- **Contact before the first marker**, against the pre-marker prefix count. -/
theorem preContact_cost_leF (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreContact a | PairedReference.referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a := by
  have hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a :=
    fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2
  have hStopL := FamRestart2.markerAt_stopLF S H.grp_le ha
  have hA : Pr[PreContact a | PairedReference.referenceExperiment adversary q] ≤
      Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (preTrace s a) a |
        PairedReference.referenceExperiment adversary q] :=
    probEvent_mono'' fun s hs => pre_mono s.answers s.trace a
      (fun l => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) l a) (fun j k hjk h => Restart.contactAt_take_mono s.answers s.trace a hjk h) hs
  have hB := FamRef.ref_le_mixF S q ha (Restart.GDr adversary q (fun T trace => Restart.MarkerAt T trace a))
    Prod.snd (Restart.GDr_snd q _)
    (fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (preTrace s a) a)
    (fun d R z => memContact a d z.1 z.2.1.1) (fun _ _ _ _ _ => rfl) (fun R z h => by have := h.1; omega)
    (FamRestart2.GDr_famF S H.grp_le q ha _ hStopL)
    (fun R x res hres => refContact_coupled q ha hmask R x res hres)
    H.grp_le H.caps H.width H.points
  simp only [Restart.mixLaw_restart] at hB
  have hc := mix_preCount_leF (adversary := adversary) S H q ha
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
    Pr[fun r => memContact a (RawPrefix.restDepth a R) r.1 r.2.1.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] with hM
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
    realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
      (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) with hC
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128 : ENNReal) * C := by
    rw [hM, hC, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm ((2 / 2 ^ 128 : ENNReal))]
    exact mul_le_mul' le_rfl (preContact_le_R q a _ R hq)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreContact a | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) :=
        mul_le_mul' le_rfl (hA.trans hB)
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128 : ENNReal) * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128 : ENNReal) * (∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- **Two-edge before the first marker**, against the pre-marker prefix count. -/
theorem preTwoEdge_cost_leF (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
        (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a := by
  have hmask : ∀ T trace, Restart.MarkerAt (Restart.maskAt T a) trace a ↔ Restart.MarkerAt T trace a :=
    fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2
  have hStopL := FamRestart2.markerAt_stopLF S H.grp_le ha
  have hA : Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] ≤
      Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) (preTrace s a) a |
        PairedReference.referenceExperiment adversary q] :=
    probEvent_mono'' fun s hs => pre_mono s.answers s.trace a
      (fun l => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) l a) (fun j k hjk h => twoEdgeAt_take_mono s.answers s.trace a hjk h) hs
  have hB := FamRef.ref_le_mixF S q ha (Restart.GDr adversary q (fun T trace => Restart.MarkerAt T trace a))
    Prod.snd (Restart.GDr_snd q _)
    (fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) (preTrace s a) a)
    (fun d R z => memTwoEdge a d z.1 z.2.1.1) (fun _ _ _ _ _ => rfl) (fun R z h => by have := h.1; omega)
    (FamRestart2.GDr_famF S H.grp_le q ha _ hStopL)
    (fun R x res hres => refTwoEdge_coupled q ha hmask R x res hres)
    H.grp_le H.caps H.width H.points
  simp only [Restart.mixLaw_restart] at hB
  have hc := mix_preCount_leF (adversary := adversary) S H q ha
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
    Pr[fun r => memTwoEdge a (RawPrefix.restDepth a R) r.1 r.2.1.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none)] with hM
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
    realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (Restart.restartGame adversary q a (fun T trace => Restart.MarkerAt T trace a) R) (fun _ _ => none) r *
      (memRows a (RawPrefix.restDepth a R) r.2.1.1 : ENNReal) with hC
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ twoEdgeRate q * C := by
    rw [hM, hC, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
    exact mul_le_mul' le_rfl (preTwoEdge_le_R q a _ R hq)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) :=
        mul_le_mul' le_rfl (hA.trans hB)
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ twoEdgeRate q * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

end ClaudeWCT.W9.T3.Security.Wots.Z5
