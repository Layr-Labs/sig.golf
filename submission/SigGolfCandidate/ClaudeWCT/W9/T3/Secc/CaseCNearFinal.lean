import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsStructuralFinal
import SigGolfCandidate.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearSearch
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyEager
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyCount
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallContract
import SigGolfCandidate.ClaudeWCT.W9.New.C2.SignerCompleteBound

section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Extends (rows rows' : Sampling.RCache) : Prop := ∀ x a, rows x = some a → rows' x = some a
theorem Extends.refl (rows : Sampling.RCache) : Extends rows rows := fun _ _ h => h
theorem Extends.trans {r1 r2 r3 : Sampling.RCache} (h1 : Extends r1 r2) (h2 : Extends r2 r3) : Extends r1 r3 :=
  fun x a h => h2 x a (h1 x a h)
theorem search_replays_gen {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      Extends cache r.2 ∧ ∀ cache', Extends r.2 cache' → ∀ r' ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache'),
          r' = (r.1, cache') := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨Extends.refl _, fun cache' _ r' hr' => ?_⟩
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr'
      change r' ∈ support (Sampling.roRun secret (pure none) cache') at hr'
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
      exact hr'
  | succ fuel ih =>
      intro counter cache r hr
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfirst' : Extends cache first.2 ∧ first.2 (inputs counter) = some first.1 := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            subst hfirst
            exact ⟨Extends.refl _, hc⟩
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            subst hfa
            refine ⟨fun x b hx => ?_, QueryCache.cacheQuery_self _ _ _⟩
            have hne : x ≠ inputs counter := fun he => by rw [he, hc] at hx; cases hx
            exact (QueryCache.cacheQuery_of_ne cache a hne).trans hx
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          obtain ⟨h1, h2⟩ := ih (counter + 1) first.2 r hr
          refine ⟨hfirst'.1.trans h1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ (h1 _ _ hfirst'.2)
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          exact h2 cache' hc' r' hr'
      | some value =>
          rw [hd] at hr
          simp only at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨hfirst'.1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ hfirst'.2
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
          exact hr'
def Replays (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) cache'), r' = (found, cache')
theorem Replays.mono {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : Replays rows rho m found) (hext : Extends rows rows') : Replays rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) rows)) :
    Extends rows r.2 ∧ Replays r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) nearSpec.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, Replays M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty : InvM (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  nearMemPotential q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (q : Nat) (s : GState) : ENNReal := if InvM s.memory then ghostPot q s.memory else ⊤
theorem ΦI_initial (q : Nat) : ΦI q initG ≤ (q : ENNReal) * 300 / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial q
theorem nearCoveredBy_mono {X Y : List HashOutput} (h : ∀ v ∈ X, v ∈ Y) {N : HashOutput}
    (hN : Guess.NearCoveredBy X N) : Guess.NearCoveredBy Y N := by
  obtain ⟨k, t, hkt⟩ := hN
  exact ⟨k, t, hkt.mono_log h⟩
theorem payoff_le_ΦI (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × GState) :
    WPair.nearPayoff q (r.1, projS r.2) ≤ ΦI q r.2 := by
  unfold ΦI
  split_ifs with hinv
  · unfold WPair.nearPayoff
    split_ifs with hp
    · obtain ⟨hb, hl, N, hN, hadm, hcov⟩ := hp
      exact mem_win q _ _ _ _ _ hb (hinv.2.1.trans hl) (Or.inr ⟨N, hN, hadm, nearCoveredBy_mono hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_mono {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  rw [SPMF.probOutput_eq_apply]
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul' le_rfl (h x hx)
theorem spmf_ev_le {α : Type} (p : SPMF α) {f : α → ENNReal} {c : ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ c) :
    expectedValue p f ≤ c :=
  (spmf_ev_mono p h).trans (expectedValue_le_of_le p fun _ => le_rfl)
theorem superProg_of_memory {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implG slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg (implG slot) (ΦI q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory {β : Type} (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · change ((fun hit => (hit, SecretGuessObservation.afterTrial (envG WPair.envL) s c v hit)) <$>
      SecretGuessObservation.forcedTrialWith samplerG slot s c v) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · change ((fun value => (value, SecretGuessObservation.afterDisclosure (envG WPair.envL) s c value)) <$>
      samplerG.discloseLaw s c) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (slot q n : Nat) : SuperProg (implG slot) (ΦI q) (WPair.coinReqL n) :=
  superProg_of_memory slot q _ fun s r hr => coin_memory slot n s r hr
theorem guess_ΦI (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Bool) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (slot q : Nat) (c : Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Digest) slot (.inr c) s r hr
theorem mapM_ΦI {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg (implG slot) (ΦI q) (f a)) :
    ∀ l : List α, SuperProg (implG slot) (ΦI q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ (mapM_ΦI slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  mapM_ΦI slot q _ (fun c => disclose_ΦI slot q c) cs
theorem probeW_ΦI (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 4 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 4) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ (guess_ΦI slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ (disclose_ΦI slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem finishL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    SuperProg (implG slot) (ΦI q) (WPair.finishL hU ω request rho found) := by
  rcases found with _ | ⟨c, output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.finishL]
    generalize WPair.signerLayersW hU ω request output = g
    cases g with
    | none => exact superProg_pure _ _ _
    | some pieces =>
        refine superProg_bind _ _ (discloseAll_ΦI slot q _) ?_
        intro values
        exact superProg_pure _ _ _
theorem ev_uniform_digest (g : Digest → ENNReal) :
    expectedValue (PMF.uniformOfFintype Digest) g = expectedValue ($ᵗ Digest : ProbComp Digest) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem ev_single_aux (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) })) := by
  have h := ev_aux_bind slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (slot q : Nat) (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [ev_single_aux]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq]
        have hpt : ∀ a : HashOutput, ΦI q { s with memory := (s.memory.1.readRow x a true,
            ghostStep s.memory.1 (.birth x) a s.memory.2) } =
            nearMemPotential q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : InvM (s.memory.1.readRow x a true, ghostStep s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact mem_birth q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact probeW_ΦI slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_ΦI slot q x
      · exact superProg_pure _ _ _
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_zero {α : Type} (p : SPMF α) {f : α → ENNReal} (h : expectedValue p f = 0) :
    ∀ x, p x ≠ 0 → f x = 0 := by
  intro x hx
  unfold expectedValue at h
  have h0 := ENNReal.tsum_eq_zero.mp h x
  rw [SPMF.probOutput_eq_apply] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hx
  · exact h1
theorem pc_ev_offsupport {α : Type} (p : ProbComp α) :
    expectedValue p (fun r => if r ∈ support p then 0 else 1) = 0 := by
  unfold expectedValue
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support p
  · simp [hr]
  · simp [hr, probOutput_eq_zero_of_not_mem_support hr]
theorem search_support (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m 0 WCT9.digestAttemptLimit) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈
      support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows) := by
  have hlaw := search_law slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows)
    then 0 else 1) WCT9.digestAttemptLimit 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0
theorem ev_nonce_cached {β : Type} (slot : Nat) (m : Message) (rho : Digest)
    (k : Digest → OracleComp WPair.WSpecL β) (s : GState) (hn : s.memory.1.nonces m = some rho)
    (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith (implG slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, ghostStep s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]
theorem ev_nonce_fresh {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp WPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]
theorem ev_expose_finish_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat)
    (ω : CanonTable.Omega U) (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput))
    (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith (implG slot)
      (WPair.exposeReq (found.map Prod.snd) >>= fun _ => WPair.finishL hU ω request rho found) s2)
      (fun r => ΦI q r.2) ≤
    ΦI q ⟨s2.allowed, s2.retired, s2.guesses, s2.probes, (s2.memory.1.expose (found.map Prod.snd),
      ghostStep s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold WPair.exposeReq
  rw [ev_aux_bind]
  change expectedValue (pure ((), s2.memory.1.expose (found.map Prod.snd)) : PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact finishL_ΦI hU slot q ω request rho found _
theorem signL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SuperProg (implG slot) (ΦI q) (WPair.signL hU ω published request) := by
  unfold WPair.signL
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte]
    exact superProg_pure _ _ _
  simp only [hc, ↓reduceIte]
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  set m := request.message with hm
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI q s = ghostPot q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      rw [ev_nonce_cached slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := search_support slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot rho m WCT9.digestAttemptLimit 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      rw [ev_nonce_fresh slot m _ s hn, hΦs]
      refine le_trans ?_ (mem_sign_fresh q _ _ _ _ _ m hn 0 WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le)
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ (search_law slot v m (fun found rows' =>
        nearMemPotential q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) WCT9.digestAttemptLimit 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := search_support slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := replays_of_search v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot v m WCT9.digestAttemptLimit 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, LazyMem.expose]
      rw [hbir1, hnon1]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem honestMsg_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (index : Nat) (lay : Layer) :
    ClaudeWCT.W9.T3M.Extract.honestMsg A index lay = ClaudeWCT.W9.T3M.Extract.honestMsg T index lay := by
  unfold ClaudeWCT.W9.T3M.Extract.honestMsg
  split_ifs
  · unfold ClaudeWCT.W9.T3M.Extract.honestPair
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h]
  · rw [ClaudeWCT.W9.T3.Security.Wots.Ref.honestTop_short h _]
theorem good_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (w : WBytes)
    (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.Extract.Good A w index lay) :
    ClaudeWCT.W9.T3M.Extract.Good T w index lay := by
  obtain ⟨digits, ⟨hctr, hdec⟩, hpath, hchain, hleaf⟩ := hg
  refine ⟨digits, ⟨hctr, ?_⟩, ?_, ?_, hleaf⟩
  · rw [← honestMsg_short h]
    rw [← ClaudeWCT.W9.T3.Security.Wots.Ref.shortRespects_encodingHash lay _
      (by rw [ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]; unfold SeccLaw.maxInputLength; omega) A T h]
    exact hdec
  · intro j hj
    obtain ⟨h1, h2⟩ := hpath j hj
    exact ⟨by rw [h1, ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h], h2⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hchain i hi
    refine ⟨?_, h2⟩
    rw [h1]
    unfold WCT9.wotsValue
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsSeed_short h]
    exact ClaudeWCT.W9.T3.Security.Wots.Ref.chainW_respects _ _ _ _ _ _ _ A T h
theorem goodZ_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (w : WBytes) (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.BC.GoodZ A w index lay) :
    ClaudeWCT.W9.T3M.BC.GoodZ T w index lay :=
  ⟨good_short h w index lay hg.1, hg.2⟩
theorem slotDisclosed_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (log : QueryLog Requests) (N : HashOutput) (k : WCT9.Coord) (t : Fin 6) (hd : SlotDisclosed A log N k t) :
    SlotDisclosed T log N k t := by
  obtain ⟨entry, he, signature, output, hs, ho, h1, h2, h3⟩ := hd
  exact ⟨entry, he, signature, output, hs, by rw [← WPair.signedOutput_short h]; exact ho, h1, h2, h3⟩
def NearIn (A : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ (m : Message) (w : WBytes) (N : HashOutput) (k : WCT9.Coord) (t : Fin 6) (c : Guess.GCoord),
    (pad64 (digestInput (wrho w) m (wdc w)), N) ∈ entries ∧
    evalWithAnswerFn A (digest (wrho w) m (wdc w)) = N ∧ Shaped N w ∧
    (∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ A w (WCT9.digestIndex N) lay) ∧ ¬SignedDigest log m w ∧
    log.length ≤ 2 ^ 32 ∧
    c.1 = Guess.chainOf N k t ∧ c.2.val = 4 - Guess.deficit N k t ∧ WPair.GuessedIn A log entries c ∧
    (∀ k' t', (k', t') ≠ (k, t) → SlotDisclosed A log N k' t') ∧ BPB.SignerComplete A
theorem nearIn_short (A T : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (hn : NearIn A log entries) : NearIn T log entries := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  refine ⟨m, w, N, k, t, c, hx, ?_, hS, fun lay => goodZ_short h w _ lay (hgood lay), hsd, hlen, h1, h2,
    WPair.guessedIn_short h log entries c hguess, fun k' t' hne => slotDisclosed_short h log N k' t' (hdis k' t' hne),
    BPB.signerComplete_short h hcomp⟩
  rw [← WPair.eval_congr_allowed (WPair.digest_short _ _ _) h]
  exact hN
theorem nearIn_mono (A : Correctness.Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (hn : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  exact ⟨m, w, N, k, t, c, hsub _ hx, hN, hS, hgood, hsd, hlen, h1, h2,
    WPair.guessedIn_mono A log entries entries' hsub c hguess, hdis, hcomp⟩
theorem near_shared (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hnear : PinnedC caseCExtraction adversary NearQ z) :
    ∀ generated interaction checked, GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction
      checked → NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, hQ⟩ := hnear
  intro g' i' c' hs'
  obtain ⟨hg', hi', hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce, hi']
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hs.2.2.2).symm.trans hclean.1
  have ha : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)
  obtain ⟨N, -, hN, -, hS, hgood, -, hcomp⟩ := (show BPB.CaseCAt z.2 m w _ from hCat)
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting g.value.1 i.value i.state c hs.2.2.1 z.2 ha hvalue f hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  obtain ⟨N', -, hN', hdq, -⟩ := ClaudeWCT.W9.T3M.WctExtract.verifyP_walk_wct z.2 m g.value.1 w hv
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
    (PaddedExtraction.check_hashOnly _ _ f) _ check hcheck z.2 (by rw [hst]; exact ha) _ (hsub _ hdq)
  rw [hev] at hevent
  have hans : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N' := hN'
  rw [hans] at hevent
  obtain ⟨k, t, c0, h1, h2, hguess, hdis⟩ := hQ
  rw [hN'] at h1 h2 hdis
  exact ⟨m, w, N', k, t, c0, SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hevent, hN', hS, hgood, hsd, hlen,
    h1, h2, hguess, hdis, hcomp⟩
theorem caseC_not_signer_eval (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (FullGame.authenticatedSign published entry.1))
    (m : Message) (w : WBytes) (hcomp : BPB.SignerComplete answers) (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := BPB.signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨sig, hsig', hsrho⟩ := BPB.payload_succeeds_of_complete answers hcomp published (wrho w) m
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [hsig entry he, BPB.eval_authenticatedSign, if_pos hc, ← hrho, hm]
  exact hsig'
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section WorldBoundL
open SecretGuessObservation (fixedRun withRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
/-- The eager family world of the near experiment is bounded by the lazy family engine (`Guess.Fam.fam_erasure`). -/
theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : CanonTable.HiddenF → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ g result, fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU ω adversary) initL result ≠ 0 → event g result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤
      Pr[wevent | withRun (envE (digestOf ω) (nonceOf ω)) samplerL (worldGameL hU ω adversary) initL] := by
  rw [← Guess.Fam.fam_erasure (envE (digestOf ω) (nonceOf ω)) (worldGameL hU ω adversary) initL
    (Guess.Fam.inv_initial LazyMem.empty)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL]
  rw [hiddenLaw_univ_bind]
  unfold ftsRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGameL hU ω g adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
end WorldBoundL
section Chain
/-- First-guess forcing for the near experiment over FTS seed families; `hno` supplies `¬Guess.Fam.Bad`. -/
theorem near_chain_slot (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (hno : ∀ A log entries, P A log entries → ¬OverflowIn A log)
    (payoff : Nat → (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω g r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (wA (canon_subset adversary) ω g) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        SeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
  refine (shared_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : CanonTable.Omega (Wots.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun g run => run.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω g) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r)
      ?_).trans ?_
    · rintro g r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω g r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω g adversary r hr).1.trans hlen,
        worldGameL_noBad (canon_subset adversary) ω g adversary r hr (hno _ _ _ hP), hp⟩
    · exact Guess.Fam.fam_event_le_forced_slot (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q _ payoff (fun _ _ h => h)
  calc (∑' ω, Pr[= ω | omegaLaw adversary] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw adversary])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy adversary slot (payoff slot))
end Chain
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem interactionT_honest (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (WPair.interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [WPair.interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [WPair.interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [WPair.interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [WPair.interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he
theorem entriesOf_honest (T : Correctness.Answers) (qs : List SigGolfCandidate.T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP)
    (r : Bool × QueryLog Requests × List Wots.Entry) (hr : r ∈ support (WPair.pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign
        (evalWithAnswerFn T SigGolfCandidate.T3.keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold WPair.pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he
theorem payoff_of_ghosts_birthBudget (q : Nat) (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hlog : ∀ e ∈ r.1.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1))
    (hexp : ∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
      signedOutput T entry.1.message σ = some output → output ∈ r.2.memory.exposures)
    (hrows : ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ SigGolfCandidate.T3.Security.BPair.digestInputs →
      a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)
    (htrials : ∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1,
      (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈ queried T (FullGame.authenticatedSign published entry.1))
    (hbirths : r.2.memory.births.length ≤ q)
    (hexplen : r.2.memory.exposures.length ≤ r.1.2.1.length)
    (hP : NearIn T r.1.2.1 r.1.2.2) : 1 ≤ WPair.nearPayoff q r := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, -, -, -, hdis, hcomp⟩ := hP
  have hbirth : N ∈ r.2.memory.births := by
    rcases hrows _ N hx (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨entry, he, hqe⟩ := htrials _ ht
      exact caseC_not_signer_eval T published r.1.2.1 hlog m w hcomp hsd entry he hqe
  have hcov : Guess.NearCoveredBy r.2.memory.exposures N := by
    refine ⟨k, t, fun k' t' hne => ?_⟩
    obtain ⟨entry, he, σ, output, hσ, hout, h1, h2, h3⟩ := hdis k' t' hne
    exact ⟨output, hexp entry he σ output hσ hout, congrArg Fin.val h1, h2, h3⟩
  unfold WPair.nearPayoff
  rw [if_pos ⟨hbirths, hexplen.trans hlen, N, hbirth, hS, hcov⟩]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem worldGame_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    SuperProg (implG slot) (ΦI q) (WPair.worldGameCore hU ω adversary) :=
  worldGameCore_super hU (implG slot) (ΦI q) ω adversary (coin_ΦI slot q) (hashL_ΦI hU slot q ω)
    (fun published request => signL_ΦI hU slot q ω published request)
theorem forced_payoff_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.worldGameCore hU ω adversary) WPair.initL) (WPair.nearPayoff q) ≤ (q : ENNReal) * 300 / 2 ^ 128 := by
  unfold SecretGuessObservation.forcedWithRun
  rw [← projS_initG, expectedValue_project WPair.envL slot _ initG (WPair.nearPayoff q)]
  calc
    _ ≤ expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.worldGameCore hU ω adversary) initG)
        (fun r => ΦI q r.2) := expectedValue_mono _ fun r => payoff_le_ΦI q r
    _ ≤ ΦI q initG := worldGame_ΦI hU ω adversary slot q initG
    _ ≤ _ := ΦI_initial q
theorem forced_payoff_sum_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.worldGameCore hU ω adversary) WPair.initL] * WPair.nearPayoff q r ≤ (q : ENNReal) * 300 / 2 ^ 128 :=
  forced_payoff_le hU ω adversary slot q
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3.Security.CaseC (pmf_probEvent_mono_support)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
/-- `NearBound` restricted to runs without FTS overflow (same right-hand side; campaign X1, stage A). -/
abbrev NearBoundNO (nearTerm : Nat → ENNReal) : Prop :=
  NearBoundOn caseCExtraction NearQ WPair.NoOverflow nearTerm
/-- The near event in the game split, together with the absence of FTS overflow. -/
def NearAll (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
    GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) ∧
        ¬WPair.OverflowIn z.2 interaction.value.2
theorem near_le_all (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC caseCExtraction adversary NearQ z ∧
        WPair.NoOverflow adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := by
  apply pmf_probEvent_mono_support
  intro z hz h
  exact ⟨h.1, fun g i c hs => ⟨near_shared adversary q hq z hz h.1 h.2.1 g i c hs, h.2.2 g i c hs⟩⟩
theorem omega_avg_le {Ω : Type} (L : ProbComp Ω) (f : Ω → ENNReal) (B : ENNReal) (h : ∀ ω, f ω ≤ B) :
    ∑' ω, Pr[= ω | L] * f ω ≤ B :=
  calc
    _ ≤ ∑' ω, Pr[= ω | L] * B := ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)
    _ = (∑' ω, Pr[= ω | L]) * B := ENNReal.tsum_mul_right
    _ ≤ 1 * B := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = B := one_mul B
theorem fixed_support_pairRun (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω))
      (Guess.Fam.phi g.1 g.2)
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0) :
    r.1 ∈ support (WPair.pairRun (WPair.wA (WPair.canon_subset adversary) ω g) adversary) := by
  rw [mem_support_iff, probOutput_def, ← WPair.fixed_worldGameL (WPair.canon_subset adversary) ω g adversary,
    map_eq_bind_pure_comp]
  rw [SphincsSecurity.Concrete.RetainedObservation.bind_nonzero]
  refine ⟨r, hr, ?_⟩
  simp only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]
theorem near_event_slot (adversary : AdversaryP) (q : Nat) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω))
      (Guess.Fam.phi g.1 g.2)
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0)
    (hq : r.1.2.2.length ≤ q) (hP : NearIn (WPair.wA (WPair.canon_subset adversary) ω g) r.1.2.1 r.1.2.2) :
    r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ WPair.nearPayoff (q - (slot + 1)) r := by
  obtain ⟨hexp, hrows, -, htrack, -, htrials, hexplen⟩ :=
    WPair.worldGameL_bank (WPair.canon_subset adversary) ω g adversary r hr
  have hpb := WPair.worldGameL_probes_births (WPair.canon_subset adversary) ω g adversary r hr
  obtain ⟨hlog, -⟩ := pairRun_honest _ adversary r.1 (fixed_support_pairRun adversary ω g r hr)
  refine ⟨?_, fun slot hslot => payoff_of_ghosts_birthBudget (q - (slot + 1)) _ _ r hlog hexp
    (fun x a hx hd => (hrows x a hx hd).2) htrials (by omega) hexplen hP⟩
  obtain ⟨-, -, -, -, -, c, -, -, -, -, -, -, -, -, hguess, -⟩ := hP
  exact Guess.nonempty_of_prefixIn (htrack c hguess)
theorem sum_range_sub_succ_twice_le (q : Nat) :
    (∑ slot ∈ Finset.range q, (q - (slot + 1))) * 2 ≤ q * q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      nlinarith
theorem sum_range_sub_succ_mul_le (q coefficient : Nat) :
    (∑ slot ∈ Finset.range q, (q - (slot + 1))) * (2 * coefficient) ≤ coefficient * q * q := by
  calc
    _ = coefficient * ((∑ slot ∈ Finset.range q, (q - (slot + 1))) * 2) := by ring
    _ ≤ coefficient * (q * q) := Nat.mul_le_mul_left coefficient (sum_range_sub_succ_twice_le q)
    _ = _ := by ring
noncomputable def nearTermTight (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (150 * q / 2 ^ 128)
theorem nearBoundTight : NearBoundNO nearTermTight := by
  intro adversary q hq _ _
  have hchain := WPair.near_chain_slot adversary q hq
    (fun A log entries => NearIn A log entries ∧ ¬WPair.OverflowIn A log)
    (fun A T log entries h hP => ⟨nearIn_short A T log entries h hP.1,
      fun ho => hP.2 (WPair.overflowIn_short h.symm log ho)⟩)
    (fun A log entries entries' hsub hP => ⟨nearIn_mono A log entries entries' hsub hP.1, hP.2⟩)
    (fun _ _ _ hP => hP.2) (fun slot => WPair.nearPayoff (q - (slot + 1)))
    (fun ω g r hr hlen hP => near_event_slot adversary q ω g r hr hlen hP.1)
  have hslot : ∀ slot, (∑' ω, Pr[= ω | WPair.omegaLaw adversary] *
      ∑' r, Pr[= r | SphincsSecurity.Concrete.SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
        (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL] * WPair.nearPayoff (q - (slot + 1)) r) ≤
      ((q - (slot + 1) : Nat) : ENNReal) * 300 / 2 ^ 128 :=
    fun slot => omega_avg_le _ _ _ fun ω => forced_payoff_sum_le (WPair.canon_subset adversary) ω adversary slot (q - (slot + 1))
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ _ := hchain
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ((q - (slot + 1) : Nat) : ENNReal) * 300 / 2 ^ 128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _ => hslot slot)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
          ((((∑ slot ∈ Finset.range q, (q - (slot + 1))) * 300 : Nat) : ENNReal) / 2 ^ 128) := by
      congr 1
      push_cast
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (((150 * q * q : Nat) : ENNReal) / 2 ^ 128) :=
      mul_le_mul' le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (by simpa using sum_range_sub_succ_mul_le q 150)) _)
    _ = nearTermTight q := by
      unfold nearTermTight
      push_cast
      simp only [div_eq_mul_inv]
      ring
theorem nearTermTight_le (q : Nat) : nearTermTight q ≤ Wots.nearTerm q := by
  unfold nearTermTight Wots.nearTerm
  apply mul_le_mul' le_rfl
  refine le_trans (le_of_eq ?_) (le_self_add.trans le_self_add)
  rfl
/-- The near bound of case C for FTS seed families: unchanged right-hand side, given no FTS overflow. -/
theorem nearBound : NearBoundNO Wots.nearTerm :=
  fun adversary q hq h1 h2 => (nearBoundTight adversary q hq h1 h2).trans (nearTermTight_le q)
end ClaudeWCT.W9.T3.Security.CaseC
end

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure
  queried_length_shortHash queried_length_privatePair queried_length_foldlM sum_map_one)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem queried_length_chain (T : Answers) (index coord selected i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (WCT9.chain index coord selected i start count v)).length = count := by
  unfold WCT9.chain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_shortHash _ _),
    sum_map_one, List.length_range']
theorem queried_length_childStep (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (state : List Digest × List Digest) (i : Fin 6) :
    (SourceReplay.queried T (childStep index coord selected word coefs state i)).length = 4 := by
  unfold childStep
  rw [queried_length_bind, queried_length_chain, queried_length_bind, queried_length_chain,
    queried_length_pure]
  have h := wordDigit_le_four word i
  omega
theorem queried_length_childRows (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) :
    (SourceReplay.queried T (childRows index coord selected word coefs)).length = 24 := by
  unfold childRows
  rw [queried_length_foldlM T _ _ (fun _ => 4)
    (fun i _ state => queried_length_childStep T index coord selected word coefs state i)]
  decide
theorem queried_length_buildChildF (T : Answers) (index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (buildChildF index coord selected word coefs pad)).length = 25 := by
  rw [buildChildF_factor, queried_length_bind, queried_length_childRows,
    queried_length_bind, queried_length_pure]
  rfl
/-- C1: the paired child of heap `heap` makes the same 25 queries. -/
theorem queried_length_buildChildH (T : Answers) (heap index coord selected : Nat) (word : Rank)
    (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (buildChildH heap index coord selected word coefs pad)).length = 25 := by
  rw [buildChildH_factor, queried_length_bind, queried_length_childRows,
    queried_length_bind, queried_length_pure]
  unfold leafHashH ftsHash
  split <;> rfl
theorem queried_length_ftsCoefs (T : Answers) (index coord : Nat) :
    (SourceReplay.queried T (ftsCoefs index coord)).length = 27 := by
  unfold ftsCoefs
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_pure]
    rfl), sum_map_one]
  rfl
theorem queried_length_coordRows (T : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (coefs : List Digest) (pad : Digest) :
    (SourceReplay.queried T (coordRows index coord selected word coefs pad)).length = 3200 := by
  unfold coordRows
  rw [queried_length_foldlM T _ _ (fun _ => 25) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_buildChildF, queried_length_pure])]
  decide
theorem queried_length_heapNode (T : Answers) (index coord heap : Nat) (pad left right : Digest) :
    (SourceReplay.queried T (wctHeapNode coord index heap pad left right)).length = 1 := by
  unfold wctHeapNode
  split <;> rfl
theorem queried_length_heapBuild (T : Answers) (index coord : Nat) (pad : Digest) (leaves : List Digest) :
    (SourceReplay.queried T (heapBuild index coord pad leaves)).length = 126 := by
  unfold heapBuild
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_heapNode, queried_length_pure]), sum_map_one]
  simp
theorem queried_length_buildCoordinateF (T : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (prev : Digest × Digest) :
    (SourceReplay.queried T (buildCoordinateF index coord selected word prev)).length = 3353 := by
  rw [buildCoordinateF_factor, queried_length_bind, queried_length_ftsCoefs,
    queried_length_bind, queried_length_coordRows, queried_length_bind, queried_length_heapBuild,
    queried_length_pure]
theorem queried_length_openingStep (T : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List (Digest × Digest)) (coord : Coord) :
    (SourceReplay.queried T (openingStep index output state coord)).length = 3353 := by
  unfold openingStep
  rw [queried_length_bind, queried_length_buildCoordinateF, queried_length_pure]
theorem queried_length_forestRows (T : Answers) (index : Nat) (output : HashOutput) :
    (SourceReplay.queried T (forestRows index output)).length = 30177 := by
  unfold forestRows
  rw [queried_length_foldlM T _ _ (fun _ => 3353) (fun _ _ _ => queried_length_openingStep _ _ _ _ _)]
  decide
theorem queried_length_signForest (T : Answers) (index : Nat) (output : HashOutput) :
    (SourceReplay.queried T (signForest index output)).length = 30177 := by
  unfold signForest
  rw [queried_length_bind, queried_length_forestRows, queried_length_pure]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem queried_free (g g' : CanonTable.HiddenF) {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program WFree) :
    SourceReplay.queried (wA hU ω g) program = SourceReplay.queried (wA hU ω g') program :=
  (ClaudeWCT.WCT9.Wots.respects_of_allQueriesSatisfy hp).queried_eq (answers_free hU ω g g')
theorem queried_length_free (g g' : CanonTable.HiddenF) {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program WFree) :
    (SourceReplay.queried (wA hU ω g) program).length =
      (SourceReplay.queried (wA hU ω g') program).length :=
  congrArg List.length (queried_free hU ω g g' hp)
theorem keygenCharge_eq (g g' : CanonTable.HiddenF) :
    SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω g) =
      SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω g') :=
  queried_length_free hU ω g g' keygen_free

theorem queried_length_pure_option (answers : Answers) {α β : Type} (found : Option α)
    (finish : α → β) (fallback : β) :
    (SourceReplay.queried answers (match found with
      | some value => pure (finish value)
      | _ => pure fallback : M β)).length = 0 := by
  cases found <;> exact queried_length_pure _ _

attribute [local irreducible] WCT9.honestTop WCT9.expectedOpening WCT9.signForest
  WCT9.digestSearch WCT9.signLayersBC

theorem signCharge_congr_free (answers answers' : Answers)
    (heval : ∀ {α : Type} {program : M α}, AllQueriesSatisfy program WFree →
      evalWithAnswerFn answers program = evalWithAnswerFn answers' program)
    (hquery : ∀ {α : Type} {program : M α}, AllQueriesSatisfy program WFree →
      (SourceReplay.queried answers program).length = (SourceReplay.queried answers' program).length)
    (hroot : ∀ index < 2 ^ 31, WCT9.honestTop answers index = WCT9.honestTop answers' index)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Wots.signCharge answers published request = Wots.signCharge answers' published request := by
  classical
  unfold Wots.signCharge FullGame.authenticatedSign
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [hquery (privateMac_free _)]
  apply congrArg (Nat.add _)
  rcases Classical.em (request.cache = published) with hc | hc
  · rw [if_pos hc]
    change (SourceReplay.queried answers (WCT9.Rev3.signPayload request.cache request.message)).length =
      (SourceReplay.queried answers' (WCT9.Rev3.signPayload request.cache request.message)).length
    rw [WCT9.Rev3.signPayload_eq]
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [hquery (privateNonce_free _),
      heval (privateNonce_free _)]
    apply congrArg (Nat.add _)
    generalize evalWithAnswerFn answers' (privateNonce request.message) = rho
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [hquery (wctDigestSearch_free _ _ _ _),
      heval (wctDigestSearch_free _ _ _ _)]
    apply congrArg (Nat.add _)
    cases evalWithAnswerFn answers' (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) with
    | none => rfl
    | some found =>
        obtain ⟨ctr, output⟩ := found
        simp only
        conv_lhs => rw [queried_length_bind, queried_length_signForest, WCT9.eval_signForest]
        conv_rhs => rw [queried_length_bind, queried_length_signForest, WCT9.eval_signForest]
        apply congrArg (Nat.add _)
        simp only
        rw [hroot (WCT9.digestIndex output) (outIndex_lt output)]
        conv_lhs => rw [queried_length_bind]
        conv_rhs => rw [queried_length_bind]
        rw [hquery (signLayersBC_free _ _ _ _),
          heval (signLayersBC_free _ _ _ _)]
        apply congrArg (Nat.add _)
        split <;> (try split) <;> simp only [queried_length_pure]
  · rw [if_neg hc]
    rfl

theorem signCharge_eq (g g' : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache)
    (request : Request) :
    Wots.signCharge (wA hU ω g) published request = Wots.signCharge (wA hU ω g') published request :=
  signCharge_congr_free _ _ (fun hp => eval_free hU ω g g' hp)
    (fun hp => queried_length_free hU ω g g' hp)
    (honestForest_world hU ω g g') published request

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- `some x` charges and records an external public query; `none` charges one
    query made internally by key generation or an authenticated signing call. -/
abbrev ClockSpec : OracleSpec (Option HashInput) := Option HashInput →ₒ Unit
abbrev CountAux := unifSpec + ClockSpec
abbrev CountSpec := SecretGuessObservation.World CountAux Guess.GCoord Digest
abbrev CountState := SecretGuessObservation.State Guess.GCoord Digest PUnit

def charged : CountSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False
instance chargedDecidable : DecidablePred charged := fun input => by
  rcases input with (n | x) | (p | c) <;> unfold charged <;> infer_instance

def clock (x : Option HashInput) : OracleComp CountSpec Unit :=
  liftM (CountSpec.query (.inl (.inr x)))
def clocks : Nat → OracleComp CountSpec Unit
  | 0 => pure ()
  | n + 1 => clock none >>= fun _ => clocks n
noncomputable def liftW {α : Type} (program : OracleComp WSpec α) : OracleComp CountSpec α :=
  simulateQ (fun input => match input with
    | .inl n => liftM (CountSpec.query (.inl (.inl n)))
    | .inr input => liftM (CountSpec.query (.inr input))) program
noncomputable def countAuxImpl : QueryImpl CountAux ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr _ => pure ()
noncomputable def countEnvironment : SecretGuessObservation.Environment CountAux Guess.GCoord Digest PUnit :=
  SecretGuessObservation.environment countAuxImpl
noncomputable def fixedCount (g : CanonTable.HiddenF) : QueryImpl CountSpec ProbComp :=
  SecretGuessObservation.fixedAnswers countAuxImpl (Guess.Fam.phi g.1 g.2)
def countInit : CountState := SecretGuessObservation.initialState PUnit.unit

def publicInputs (inputs : List CountSpec.Domain) : List HashInput :=
  inputs.filterMap fun input => match input with
    | .inl (.inr (some x)) => some x
    | _ => none

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def hashC (x : HashInput) : OracleComp CountSpec HashOutput := do
  clock (some x)
  liftW (hashW hU ω x)
noncomputable def signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp CountSpec (Option Signature) := do
  clocks (Wots.signCharge (wA hU ω 0) published request)
  liftW (signW hU ω published request)
noncomputable def interactionC (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp CountSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signC hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programC {β : Type} : M β → OracleComp CountSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldC (adversary : AdversaryP) :
    OracleComp CountSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  clocks (SigGolfCandidate.T3.Security.Wots.keygenCharge (wA hU ω 0))
  let generated := evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen
  let interaction ← interactionC hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programC hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
noncomputable def cappedProgram {α : Type} (program : OracleComp CountSpec α) (budget : Nat) :=
  SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run charged program budget)
noncomputable def cappedWorld (adversary : AdversaryP) (budget : Nat) :=
  cappedProgram (worldC hU ω adversary) budget

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable

theorem probeInput_other (T : Answers) (a : Guess.ChainAddr) (step : Fin 4) (value : Digest) :
    Wots.OtherInput T (Guess.probeInput a step value) := by
  let pos : Extract.Pos := .wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val step.val
  have hb : pos.Bounded := ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
  -- #866: `posOf_eq` also takes the input length (a chain row is 64 bytes, `Pos.len` of a chain position).
  refine ⟨pos, Extract.posOf_eq hb (Guess.probeInput_length a step value) ?_, hb, ?_, trivial⟩
  · exact Guess.hdrBlock_wctChainInput _ _ _ _ _ _
  · exact ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
theorem decodeProbe_other (T : Answers) {x : HashInput} {probe : Guess.GCoord × Digest}
    (h : Guess.decodeProbe x = some probe) : Wots.OtherInput T x := by
  rw [Guess.eq_of_decodeProbe h]
  exact probeInput_other T _ _ _
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
noncomputable def probeCount (inputs : List HashInput) : Nat :=
  (inputs.filter fun x => (Guess.decodeProbe x).isSome).length

theorem probeCount_le_other (T : Answers) (pk : Digest) (trace : List Wots.Entry) :
    probeCount (trace.map Prod.fst) ≤ Wots.otherCount ⟨T, pk, trace⟩ := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      obtain ⟨x, a⟩ := entry
      cases hd : Guess.decodeProbe x with
      | none =>
          by_cases ho : Wots.OtherQuery T (.inl (.inr x))
          · have h : probeCount (trace.map Prod.fst) ≤ 1 + Wots.otherCount ⟨T, pk, trace⟩ := by omega
            simpa [probeCount, Wots.otherCount, hd, ho, Nat.add_comm] using h
          · simpa [probeCount, Wots.otherCount, hd, ho] using ih
      | some probe =>
          have ho : Wots.OtherQuery T (.inl (.inr x)) := decodeProbe_other T hd
          simpa [probeCount, Wots.otherCount, hd, ho] using Nat.add_le_add_left ih 1
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable

theorem fixed_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α) :
    simulateQ (fixedCount g) (liftW program) = simulateQ (fixedW g) program := by
  induction program using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer

theorem run_liftW {α : Type} (program : OracleComp WSpec α) (budget : Nat) :
    SphincsSecurity.QueryCap.run charged (liftW program) budget =
      (fun result => some (result, budget)) <$> liftW program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query, SphincsSecurity.QueryCap.run_query_bind,
          charged, if_false, map_bind]
        apply bind_congr
        intro answer
        exact ih answer

theorem fixed_clock (g : CanonTable.HiddenF) (input : Option HashInput) :
    simulateQ (fixedCount g) (clock input) = pure () := rfl
theorem fixed_clocks (g : CanonTable.HiddenF) (n : Nat) :
    simulateQ (fixedCount g) (clocks n) = pure () := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [clocks, simulateQ_bind, fixed_clock, pure_bind, ih]

theorem run_clock_bind {α : Type} (input : Option HashInput) (next : Unit → OracleComp CountSpec α) :
    ∀ budget, SphincsSecurity.QueryCap.run charged (clock input >>= next) budget =
      match budget with
      | 0 => pure none
      | remaining + 1 => clock input >>= fun answer => SphincsSecurity.QueryCap.run charged (next answer) remaining := by
  intro budget
  rw [clock, SphincsSecurity.QueryCap.run_query_bind]
  simp only [charged, if_true]
  cases budget <;> rfl

theorem fixed_run_clocks_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : OracleComp CountSpec α) (budget : Nat) :
    simulateQ (fixedCount g) (SphincsSecurity.QueryCap.run charged (clocks n >>= fun _ => next) budget) =
      if n ≤ budget then simulateQ (fixedCount g) (SphincsSecurity.QueryCap.run charged next (budget - n))
      else pure none := by
  induction n generalizing budget with
  | zero => simp [clocks]
  | succ n ih =>
      simp only [clocks, bind_assoc, run_clock_bind]
      cases budget with
      | zero => simp [simulateQ_pure]
      | succ budget =>
          simp only [simulateQ_bind, fixed_clock, pure_bind, ih, Nat.succ_le_succ_iff,
            Nat.succ_sub_succ_eq_sub]
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

open SphincsSecurity.Concrete

/-- Record only charged external hash calls. In particular, private disclosures
    and the internal signing charge do not enter this public transcript. -/
noncomputable def observed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) : ProbComp (α × List HashInput) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← fixedCount g input
      let rest ← next answer
      pure (rest.1, publicInputs [input] ++ rest.2)) program

theorem observed_pure (g : CanonTable.HiddenF) {α : Type} (result : α) :
    observed g (pure result : OracleComp CountSpec α) = pure (result, []) := rfl

theorem observed_query_bind (g : CanonTable.HiddenF) {α : Type} (input : CountSpec.Domain)
    (next : CountSpec.Range input → OracleComp CountSpec α) :
    observed g (liftM (CountSpec.query input) >>= next) =
      (fixedCount g input >>= fun answer => observed g (next answer) >>= fun rest =>
        pure (rest.1, publicInputs [input] ++ rest.2)) := rfl

theorem observed_bind (g : CanonTable.HiddenF) {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) :
    observed g (program >>= next) =
      (observed g program >>= fun first => observed g (next first.1) >>= fun second =>
        pure (second.1, first.2 ++ second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, observed_pure, List.nil_append, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, observed_query_bind, ih, pure_bind, List.append_assoc]

theorem observed_map (g : CanonTable.HiddenF) {α β : Type} (f : α → β) (program : OracleComp CountSpec α) :
    observed g (f <$> program) = (fun result => (f result.1, result.2)) <$> observed g program := by
  rw [← bind_pure_comp, observed_bind]
  simp only [observed_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]

theorem observed_recorded (g : CanonTable.HiddenF) {α : Type} (program : OracleComp CountSpec α) :
    observed g program = (fun result => (result.1, publicInputs result.2)) <$>
      simulateQ (fixedCount g) (SphincsSecurity.QueryCap.recorded program) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [observed_query_bind, ih, SphincsSecurity.QueryCap.recorded_query_bind,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_map_left, map_bind, map_pure]
      congr 1
      funext answer
      congr 1
      funext rest
      congr 1
      rcases input with (n | x) | (p | c)
      all_goals try (cases x)
      all_goals simp [publicInputs, List.filterMap_cons]

theorem observed_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α) :
    observed g (liftW program) = (fun result => (result, [])) <$> simulateQ (fixedW g) program := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query]
        rw [observed_query_bind]
        change (_ >>= fun answer => observed g (liftW (next answer)) >>= fun rest => pure (rest.1, [] ++ rest.2)) = _
        simp only [ih, List.nil_append, Prod.mk.eta, bind_pure, map_bind]
        rfl

theorem observed_clock (g : CanonTable.HiddenF) (input : Option HashInput) :
    observed g (clock input) = pure ((), input.toList) := by
  cases input <;> rfl

theorem observed_clocks (g : CanonTable.HiddenF) (n : Nat) :
    observed g (clocks n) = pure ((), []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [clocks, observed_bind, observed_clock, pure_bind, ih, Option.toList_none, List.nil_append]

theorem observed_run_clocks_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (clocks n >>= fun _ => next) budget) =
      if n ≤ budget then observed g (SphincsSecurity.QueryCap.run charged next (budget - n))
      else pure (none, []) := by
  induction n generalizing budget with
  | zero => simp [clocks, observed_pure]
  | succ n ih =>
      simp only [clocks, bind_assoc, run_clock_bind]
      cases budget with
      | zero => simp [observed_pure]
      | succ budget =>
          simp only [observed_bind, observed_clock, pure_bind, Option.toList_none, List.nil_append, ih,
            Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, Prod.mk.eta, bind_pure]

theorem fixedRun_liftW (g : CanonTable.HiddenF) {α : Type} (program : OracleComp WSpec α)
    (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (liftW program) state =
      SecretGuessObservation.fixedRun env (Guess.Fam.phi g.1 g.2) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, simulateQ_bind, simulateQ_spec_query, SecretGuessObservation.fixedRun,
          SecretGuessObservation.runWith_query_bind]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2

theorem fixedRun_clock (g : CanonTable.HiddenF) (input : Option HashInput) (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock input) state =
      pure ((), state) := by
  obtain ⟨allowed, retired, guesses, probes, memory⟩ := state
  cases memory
  simp [SecretGuessObservation.fixedRun, SecretGuessObservation.runWith, clock,
    SecretGuessObservation.fixedImpl, countEnvironment, SecretGuessObservation.environment, countAuxImpl,
    StateT.run_mk, simulateQ_spec_query]

theorem fixedRun_clocks (g : CanonTable.HiddenF) (n : Nat) (state : CountState) :
    SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clocks n) state =
      pure ((), state) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [clocks, SecretGuessObservation.fixedRun, SecretGuessObservation.runWith,
        simulateQ_bind, StateT.run_bind]
      change (SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock none) state >>=
        fun result => SecretGuessObservation.fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clocks n) result.2) = _
      rw [fixedRun_clock, pure_bind, ih]

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged refImpl tick ticks)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def refPublicInputs (inputs : List RefWorld.Domain) : List HashInput :=
  inputs.filterMap fun input => match input with
    | .inl (.inr x) => some x
    | _ => none

noncomputable def refObserved (T : Answers) {α : Type} (program : OracleComp RefWorld α) :
    ProbComp (α × List HashInput) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← refImpl T input
      let rest ← next answer
      pure (rest.1, refPublicInputs [input] ++ rest.2)) program

theorem refObserved_pure (T : Answers) {α : Type} (result : α) :
    refObserved T (pure result : OracleComp RefWorld α) = pure (result, []) := rfl

theorem refObserved_query_bind (T : Answers) {α : Type} (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld α) :
    refObserved T (liftM (RefWorld.query input) >>= next) =
      (refImpl T input >>= fun answer => refObserved T (next answer) >>= fun rest =>
        pure (rest.1, refPublicInputs [input] ++ rest.2)) := rfl

theorem refObserved_bind (T : Answers) {α β : Type} (program : OracleComp RefWorld α)
    (next : α → OracleComp RefWorld β) :
    refObserved T (program >>= next) =
      (refObserved T program >>= fun first => refObserved T (next first.1) >>= fun second =>
        pure (second.1, first.2 ++ second.2)) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, refObserved_pure, List.nil_append, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, refObserved_query_bind, ih, pure_bind, List.append_assoc]

theorem refObserved_map (T : Answers) {α β : Type} (f : α → β) (program : OracleComp RefWorld α) :
    refObserved T (f <$> program) = (fun result => (f result.1, result.2)) <$> refObserved T program := by
  rw [← bind_pure_comp, refObserved_bind]
  simp only [refObserved_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]

theorem refObserved_recorded (T : Answers) {α : Type} (program : OracleComp RefWorld α) :
    refObserved T program = (fun result => (result.1, refPublicInputs result.2)) <$>
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded program) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [refObserved_query_bind, ih, SphincsSecurity.QueryCap.recorded_query_bind,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_map_left, map_bind, map_pure]
      congr 1
      funext answer
      congr 1
      funext rest
      congr 1
      rcases input with (n | x) | u <;> simp [refPublicInputs, List.filterMap_cons]

theorem refPublicInputs_eq_trace (T : Answers) (inputs : List RefWorld.Domain) :
    refPublicInputs inputs = (SigGolfCandidate.T3.Security.Wots.traceOf T inputs).map Prod.fst := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rcases input with (n | x) | u
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons] using ih
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons, List.map_cons] using congrArg (List.cons x) ih
      · simpa only [refPublicInputs, SigGolfCandidate.T3.Security.Wots.traceOf,
          List.filterMap_cons] using ih

theorem run_tick_bind {α : Type} (next : Unit → OracleComp RefWorld α) (budget : Nat) :
    SphincsSecurity.QueryCap.run RefCharged (tick >>= next) budget =
      match budget with
      | 0 => pure none
      | remaining + 1 => tick >>= fun answer => SphincsSecurity.QueryCap.run RefCharged (next answer) remaining := by
  rw [tick, SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_true]
  cases budget <;> rfl

theorem refObserved_tick (T : Answers) : refObserved T tick = pure ((), []) := rfl

theorem refObserved_run_ticks_bind (T : Answers) {α : Type} (n : Nat)
    (next : OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged (ticks n >>= fun _ => next) budget) =
      if n ≤ budget then refObserved T (SphincsSecurity.QueryCap.run RefCharged next (budget - n))
      else pure (none, []) := by
  induction n generalizing budget with
  | zero => simp [ticks, refObserved_pure]
  | succ n ih =>
      simp only [ticks, bind_assoc, run_tick_bind]
      cases budget with
      | zero => simp [refObserved_pure]
      | succ budget =>
          simp only [refObserved_bind, refObserved_tick, pure_bind, List.nil_append, ih,
            Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, Prod.mk.eta, bind_pure]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem observed_run_liftW_bind (g : CanonTable.HiddenF) {α β : Type} (program : OracleComp WSpec α)
    (next : α → OracleComp CountSpec β) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (liftW program >>= next) budget) =
      (simulateQ (fixedW g) program >>= fun result =>
        observed g (SphincsSecurity.QueryCap.run charged (next result) budget)) := by
  rw [SphincsSecurity.QueryCap.run_bind, run_liftW, bind_map_left, observed_bind, observed_liftW]
  simp only [bind_map_left, List.nil_append, Prod.mk.eta, bind_pure]

theorem observed_run_hashC_bind (g : CanonTable.HiddenF) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (hashC hU ω x >>= next) budget) =
      match budget with
      | 0 => pure (none, [])
      | remaining + 1 =>
          (fun rest => (rest.1, x :: rest.2)) <$>
            observed g (SphincsSecurity.QueryCap.run charged
              (next (wA hU ω g (.inl (.inr x)))) remaining) := by
  simp only [hashC, bind_assoc, run_clock_bind]
  cases budget with
  | zero => rfl
  | succ remaining =>
      rw [observed_bind, observed_clock, pure_bind, observed_run_liftW_bind, fixed_hashW, pure_bind]
      simp only [Option.toList_some, List.singleton_append, bind_pure_comp]

theorem observed_run_signC_bind (g : CanonTable.HiddenF) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (signC hU ω published request >>= next) budget) =
      if Wots.signCharge (wA hU ω g) published request ≤ budget then
        observed g (SphincsSecurity.QueryCap.run charged
          (next (evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request)))
          (budget - Wots.signCharge (wA hU ω g) published request))
      else pure (none, []) := by
  simp only [signC, bind_assoc, observed_run_clocks_bind]
  rw [signCharge_eq hU ω 0 g]
  split_ifs
  · rw [observed_run_liftW_bind, fixed_signW, pure_bind]
  · rfl

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged refImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem observed_run_coin_bind (g : CanonTable.HiddenF) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (liftM (CountSpec.query (.inl (.inl n))) >>= next) budget) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin =>
        observed g (SphincsSecurity.QueryCap.run charged (next coin) budget)) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [charged, if_false, observed_query_bind, publicInputs,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, Prod.mk.eta, bind_pure]
  rfl

theorem refObserved_run_coin_bind (T : Answers) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (liftM (RefWorld.query (.inl (.inl n))) >>= next) budget) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin =>
        refObserved T (SphincsSecurity.QueryCap.run RefCharged (next coin) budget)) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_false, refObserved_query_bind, refPublicInputs,
    List.filterMap_cons, List.filterMap_nil, List.nil_append, Prod.mk.eta, bind_pure]
  rfl

theorem refObserved_run_public_bind (T : Answers) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (liftM (RefWorld.query (.inl (.inr x))) >>= next) budget) =
      match budget with
      | 0 => pure (none, [])
      | remaining + 1 =>
          (fun rest => (rest.1, x :: rest.2)) <$>
            refObserved T (SphincsSecurity.QueryCap.run RefCharged (next (T (.inl (.inr x)))) remaining) := by
  rw [SphincsSecurity.QueryCap.run_query_bind]
  simp only [RefCharged, if_true]
  cases budget with
  | zero => rfl
  | succ remaining =>
      simp only [refObserved_query_bind, refImpl, pure_bind, refPublicInputs,
        List.filterMap_cons, List.filterMap_nil, List.singleton_append, bind_pure_comp]

theorem refObserved_run_offlineSign_bind (T : Answers) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (Wots.offlineSign T published request >>= next) budget) =
      if Wots.signCharge T published request ≤ budget then
        refObserved T (SphincsSecurity.QueryCap.run RefCharged
          (next (evalWithAnswerFn T (FullGame.authenticatedSign published request)))
          (budget - Wots.signCharge T published request))
      else pure (none, []) := by
  simp only [Wots.offlineSign, bind_assoc, pure_bind, refObserved_run_ticks_bind]

theorem interactionC_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionC hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionC_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => interactionC hU ω published (next coin)) := rfl
theorem interactionC_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => interactionC hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionC_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionC hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signC hU ω published request >>= fun signature => interactionC hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

/-- The count world and the reference experiment have the same capped public
    transcript, including the prefix retained when the query budget expires. -/
theorem interactionC_transport (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α β : Type}
    (program : OracleComp LazyPrivate.Interaction α)
    (nextC : (α × QueryLog Requests) → OracleComp CountSpec β)
    (nextR : (α × QueryLog Requests) → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (interactionC hU ω published program >>= fun result => nextC (result.1, result.2.1)) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (Wots.offlineInteraction (wA hU ω g) published program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [interactionC_pure, Wots.Ref.offlineInteraction_pure, pure_bind, pure_bind]
      exact hn (value, []) budget
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, Wots.Ref.offlineInteraction_world, bind_assoc, bind_assoc,
          observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [interactionC_public, Wots.Ref.offlineInteraction_world]
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [interactionC_request, Wots.Ref.offlineInteraction_request]
        simp only [bind_assoc, pure_bind, bind_map_left]
        rw [observed_run_signC_bind, refObserved_run_offlineSign_bind]
        split_ifs
        · exact ih _
            (fun value => nextC (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (FullGame.authenticatedSign published request)⟩ :: value.2))
            (fun value => nextR (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (FullGame.authenticatedSign published request)⟩ :: value.2))
            (fun value remaining => hn _ remaining) _
        · rfl

theorem programC_pure {α : Type} (value : α) :
    programC hU ω (pure value : M α) = pure (value, []) := rfl
theorem programC_coin {α : Type} (n : Nat) (next : Fin (n + 1) → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => programC hU ω (next coin)) := rfl
theorem programC_public {α : Type} (x : HashInput) (next : HashOutput → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => programC hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programC_private {α : Type} (coordinate : Coordinate) (next : HashOutput → M α) :
    programC hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr coordinate)) >>= next) =
      programC hU ω (next 0) := rfl

theorem programC_transport (g : CanonTable.HiddenF) {α β : Type} (program : M α)
    (nextC : α → OracleComp CountSpec β) (nextR : α → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (programC hU ω program >>= fun result => nextC result.1) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [programC_pure, simulateQ_pure, pure_bind, pure_bind]
      exact hn value budget
  | query_bind input next ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, simulateQ_bind, simulateQ_spec_query]
        change observed g (SphincsSecurity.QueryCap.run charged
          ((liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => programC hU ω (next coin)) >>=
            fun result => nextC result.1) budget) =
          refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
            ((liftM (RefWorld.query (.inl (.inl n))) >>= fun coin =>
              simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next coin)) >>= nextR) budget)
        rw [bind_assoc, bind_assoc, observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [programC_public, simulateQ_bind, simulateQ_spec_query]
        change observed g (SphincsSecurity.QueryCap.run charged
          ((hashC hU ω x >>= fun answer => programC hU ω (next answer) >>= fun rest =>
            pure (rest.1, (x, answer) :: rest.2)) >>= fun result => nextC result.1) budget) =
          refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
            ((liftM (RefWorld.query (.inl (.inr x))) >>= fun answer =>
              simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next answer)) >>= nextR) budget)
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [programC_private, simulateQ_bind, simulateQ_spec_query]
        change _ = refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
          ((pure (0 : HashOutput) >>= fun answer =>
            simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl (next answer)) >>= nextR) budget)
        rw [pure_bind]
        exact ih (0 : HashOutput) nextC nextR hn budget

theorem worldC_transport (g : CanonTable.HiddenF) (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU ω adversary >>= fun result => pure result.1) budget) =
      refObserved (wA hU ω g) (Wots.referenceGame (wA hU ω g) adversary budget) := by
  unfold worldC Wots.referenceGame Wots.offlineGame
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU ω 0 g, keygen_answers hU ω g]
  split_ifs
  · refine interactionC_transport hU ω g _ _
      (fun result => programC hU ω (GameWith.verdict PaddedGame.checker
        (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result) >>= fun checked => pure checked.1)
      (fun result => simulateQ SigGolfCandidate.T3.Security.Wots.verdictImpl
        (GameWith.verdict PaddedGame.checker
          (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result)) ?_ _
    intro result remaining
    have h := programC_transport hU ω g
      (GameWith.verdict PaddedGame.checker
        (evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen).1 result)
      (fun value => pure value) (fun value => pure value)
      (fun value remaining => rfl) remaining
    simpa only [bind_pure] using h
  · rfl

theorem run_map_result {Index : Type} {spec : OracleSpec Index} (selected : Index → Prop)
    [DecidablePred selected] {α β : Type} (f : α → β) (program : OracleComp spec α) (budget : Nat) :
    SphincsSecurity.QueryCap.run selected (f <$> program) budget =
      (fun result => result.map (fun value => (f value.1, value.2))) <$>
        SphincsSecurity.QueryCap.run selected program budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [map_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : selected input
      · rw [if_pos hc, if_pos hc]
        cases budget <;> simp only [map_pure, map_bind, ih, Option.map_none]
      · simp only [if_neg hc, map_bind, ih]

theorem worldC_public_transport (g : CanonTable.HiddenF) (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount g) (cappedWorld hU ω adversary budget) =
      (fun result => refPublicInputs result.2) <$> Wots.offlineRun (wA hU ω g) adversary budget := by
  have h := congrArg (Functor.map Prod.snd) (worldC_transport hU ω g adversary budget)
  rw [bind_pure_comp, run_map_result, observed_map] at h
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedWorld, cappedProgram,
    Wots.offlineRun] using h

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- An FTS-labelled external query provides one unit of credit before the
    corresponding hidden-label trial is made. -/
noncomputable def clockCredit : CountSpec.Domain → Nat
  | .inl (.inr (some x)) => if (Guess.decodeProbe x).isSome then 1 else 0
  | _ => 0

/-- Every hidden-label trial has already been charged to an external FTS query.
    The definition is prefix closed, so it also covers aborted runs. -/
noncomputable def Funded {α : Type} (program : OracleComp CountSpec α) : Nat → Prop :=
  OracleComp.construct (fun _ _ => True)
    (fun input _ next credit =>
      probeStep input ≤ credit + clockCredit input ∧
      ∀ answer, next answer (credit + clockCredit input - probeStep input)) program

theorem funded_pure {α : Type} (value : α) (credit : Nat) :
    Funded (pure value : OracleComp CountSpec α) credit := trivial

theorem funded_query_bind {α : Type} (input : CountSpec.Domain)
    (next : CountSpec.Range input → OracleComp CountSpec α) (credit : Nat) :
    Funded (liftM (CountSpec.query input) >>= next) credit ↔
      probeStep input ≤ credit + clockCredit input ∧
        ∀ answer, Funded (next answer) (credit + clockCredit input - probeStep input) := Iff.rfl

theorem funded_bind {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) (credit : Nat) (hfirst : Funded program credit)
    (hnext : ∀ value remaining, Funded (next value) remaining) : Funded (program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing credit with
  | pure value => simpa only [pure_bind] using hnext value credit
  | query_bind input continuation ih =>
      rw [funded_query_bind] at hfirst
      rw [bind_assoc, funded_query_bind]
      exact ⟨hfirst.1, fun answer => ih answer _ (hfirst.2 answer)⟩

theorem funded_run {α : Type} (program : OracleComp CountSpec α) (credit budget : Nat)
    (hfunded : Funded program credit) :
    Funded (SphincsSecurity.QueryCap.run charged program budget) credit := by
  induction program using OracleComp.inductionOn generalizing credit budget with
  | pure value => exact funded_pure _ _
  | query_bind input next ih =>
      rw [funded_query_bind] at hfunded
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : charged input
      · rw [if_pos hc]
        cases budget with
        | zero => exact funded_pure _ _
        | succ budget =>
            rw [funded_query_bind]
            exact ⟨hfunded.1, fun answer => ih answer _ _ (hfunded.2 answer)⟩
      · rw [if_neg hc, funded_query_bind]
        exact ⟨hfunded.1, fun answer => ih answer _ _ (hfunded.2 answer)⟩

theorem funded_recorded_bound {α : Type} (program : OracleComp CountSpec α) (credit : Nat)
    (hfunded : Funded program credit) (result : α × List CountSpec.Domain)
    (hr : result ∈ support (SphincsSecurity.QueryCap.recorded program)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ credit + (result.2.map clockCredit).sum := by
  induction program using OracleComp.inductionOn generalizing credit result with
  | pure value =>
      rw [SphincsSecurity.QueryCap.recorded_pure, mem_support_pure_iff] at hr
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [funded_query_bind] at hfunded
      rw [SphincsSecurity.QueryCap.recorded_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, -, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨tail, ht, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst result
      have hi := ih answer _ (hfunded.2 answer) tail ht
      simp only [List.map_cons, List.sum_cons]
      omega

theorem clockCredit_sum (inputs : List CountSpec.Domain) :
    (inputs.map clockCredit).sum = probeCount (publicInputs inputs) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rcases input with (n | x) | (p | c)
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih
      · cases x with
        | none => simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
            List.filterMap_cons] using ih
        | some x =>
            simp only [List.map_cons, List.sum_cons, clockCredit, publicInputs, List.filterMap_cons,
              probeCount, List.filter_cons]
            split <;> simp_all [probeCount, publicInputs, Nat.add_comm]
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih
      · simpa only [List.map_cons, List.sum_cons, clockCredit, Nat.zero_add, publicInputs,
          List.filterMap_cons] using ih

theorem funded_clocks (n credit : Nat) : Funded (clocks n) credit := by
  induction n with
  | zero => exact funded_pure _ _
  | succ n ih =>
      change 0 ≤ credit + 0 ∧ ∀ _ : Unit, Funded (clocks n) (credit + 0 - 0)
      exact ⟨Nat.zero_le _, fun _ => ih⟩

theorem liftW_pure {α : Type} (value : α) : liftW (pure value : OracleComp WSpec α) = pure value := rfl
theorem liftW_bind {α β : Type} (program : OracleComp WSpec α) (next : α → OracleComp WSpec β) :
    liftW (program >>= next) = liftW program >>= fun value => liftW (next value) :=
  simulateQ_bind _ _ _

theorem funded_disclose_bind {α : Type} (coordinate : Guess.GCoord)
    (next : Digest → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (liftW (Guess.discloseQ (auxSpec := unifSpec) coordinate) >>= next) credit := by
  change 0 ≤ credit + 0 ∧ ∀ value : Digest, Funded (next value) (credit + 0 - 0)
  exact ⟨Nat.zero_le _, fun value => hn value credit⟩

theorem funded_discloseAll_bind {α : Type} (coordinates : List Guess.GCoord)
    (next : List Digest → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ values remaining, Funded (next values) remaining) :
    Funded (liftW (Guess.discloseAll (auxSpec := unifSpec) (V := Digest) coordinates) >>= next) credit := by
  induction coordinates generalizing next credit with
  | nil => simpa only [Guess.discloseAll, List.mapM_nil, liftW_pure, pure_bind] using hn [] credit
  | cons coordinate coordinates ih =>
      simp only [Guess.discloseAll, List.mapM_cons, liftW_bind, liftW_pure, bind_assoc, pure_bind]
      apply funded_disclose_bind
      intro value remaining
      exact ih (fun values => next (value :: values)) remaining (fun values remaining => hn _ remaining)

theorem funded_probe_bind {α : Type}
    (step : Guess.ChainAddr → Fin 4 → Digest → HashOutput) (top : Guess.ChainAddr → HashOutput)
    (miss : HashOutput) (a : Guess.ChainAddr) (p : Fin 4) (value : Digest)
    (next : HashOutput → OracleComp CountSpec α) (credit : Nat) (hcredit : 1 ≤ credit)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (liftW (Guess.probeW (auxSpec := unifSpec) step top miss a p value) >>= next) credit := by
  rw [Guess.probeW, liftW_bind, bind_assoc]
  rw [show liftW (Guess.trialQ (auxSpec := unifSpec) (a, p) value) =
    (liftM (CountSpec.query (.inr (.inl ((a, p), value)))) : OracleComp CountSpec Bool) from rfl,
    funded_query_bind]
  simp only [probeStep, clockCredit, Nat.add_zero]
  refine ⟨hcredit, ?_⟩
  intro hit
  cases hit with
  | false =>
      simpa only [Bool.false_eq_true, if_false, liftW_pure, pure_bind] using hn miss (credit - 1)
  | true =>
      simp only [if_true]
      cases hp : Guess.succPos p with
      | none => simpa only [liftW_pure, pure_bind] using hn (top a) (credit - 1)
      | some p' =>
          simp only [liftW_bind, liftW_pure, bind_assoc, pure_bind]
          exact funded_disclose_bind _ _ _ (fun value remaining => hn _ remaining)

attribute [local irreducible] worldC interactionC programC signC hashC cappedWorld
  Wots.signCharge Wots.keygenCharge keygen

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem funded_hashC_bind {α : Type} (x : HashInput) (next : HashOutput → OracleComp CountSpec α)
    (credit : Nat) (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (hashC hU ω x >>= next) credit := by
  rw [hashC, bind_assoc]
  change 0 ≤ credit + (if (Guess.decodeProbe x).isSome then 1 else 0) ∧
    ∀ _ : Unit, Funded (liftW (hashW hU ω x) >>= next)
      (credit + (if (Guess.decodeProbe x).isSome then 1 else 0) - 0)
  refine ⟨Nat.zero_le _, ?_⟩
  intro _
  unfold hashW Guess.ChainTable.hashW
  cases hd : Guess.decodeProbe x with
  | none => simpa only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.add_zero, Nat.sub_zero,
      liftW_pure, pure_bind] using hn _ credit
  | some probe =>
      simp only [Option.isSome_some, if_true, Nat.sub_zero]
      exact funded_probe_bind _ _ _ _ _ _ next (credit + 1) (by omega) hn

theorem funded_signC_bind {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option Signature → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (signC hU ω published request >>= next) credit := by
  rw [signC, bind_assoc]
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  unfold signW
  rw [liftW_bind, bind_assoc]
  simp only [liftW_pure, pure_bind]
  exact funded_discloseAll_bind _ _ _ (fun values remaining => hn _ remaining)

theorem funded_interactionC_bind {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α)
    (next : (α × QueryLog Requests × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (interactionC hU ω published program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [interactionC_pure, pure_bind] using hn (value, [], []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [interactionC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [interactionC_request]
        simp only [bind_assoc, pure_bind]
        apply funded_signC_bind
        intro signature remaining
        exact ih signature _ remaining (fun result remaining => hn _ remaining)

theorem funded_programC_bind {α β : Type} (program : M α)
    (next : (α × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (programC hU ω program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [programC_pure, pure_bind] using hn (value, []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [programC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [programC_private]
        exact ih (0 : HashOutput) next credit hn

theorem funded_worldC (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (credit : Nat) :
    Funded (worldC hU ω adversary) credit := by
  unfold worldC
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  apply funded_interactionC_bind
  intro result remaining
  apply funded_programC_bind
  intro verdict remaining
  exact funded_pure _ _

theorem cappedWorld_probe_count (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedWorld hU ω adversary budget)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2) := by
  rw [cappedWorld] at hr
  have h := funded_recorded_bound _ 0 (funded_run _ 0 budget (funded_worldC hU ω adversary 0)) result hr
  simpa only [Nat.zero_add, clockCredit_sum] using h

theorem withRun_bind_counted {α β : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) (state : CountState) :
    withRun environment sampler (program >>= next) state =
      (withRun environment sampler program state >>= fun middle =>
        withRun environment sampler (next middle.1) middle.2) := by
  simp only [withRun, runWith, simulateQ_bind, StateT.run_bind]

theorem withRun_result_support {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (state : CountState) (result : α × CountState)
    (hr : withRun environment sampler program state result ≠ 0) : result.1 ∈ support program := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [mem_support_bind_iff]
      exact ⟨middle.1, by simp only [support_query, Set.mem_univ], ih middle.1 middle.2 result hr⟩

theorem withRun_recorded_probes {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (state : CountState) (result : (α × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (SphincsSecurity.QueryCap.recorded program) state result ≠ 0) :
    result.2.probes = state.probes + (result.1.2.map (probeStep (auxSpec := CountAux))).sum := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, withRun, runWith_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, withRun, runWith_query_bind,
        SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      change withRun environment sampler
        (SphincsSecurity.QueryCap.recorded (next middle.1) >>= fun tail => pure (tail.1, input :: tail.2))
        middle.2 result ≠ 0 at hr
      rw [withRun_bind_counted, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr
      obtain ⟨tail, ht, hr⟩ := hr
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      have hfirst := withImpl_probes environment sampler state input middle hm
      have htail := ih middle.1 middle.2 tail ht
      simp only [List.map_cons, List.sum_cons]
      omega

theorem recorded_probes_le_class {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α)
    (hclass : ∀ result : α × List CountSpec.Domain, result ∈ support (SphincsSecurity.QueryCap.recorded program) →
      (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2))
    (result : (α × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (SphincsSecurity.QueryCap.recorded program)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  have hp := withRun_recorded_probes environment sampler program countInit result hr
  have hc := hclass result.1
    (withRun_result_support environment sampler _ countInit result hr)
  simp only [countInit, initialState, Nat.zero_add] at hp
  exact hp.trans_le hc

theorem cappedProgram_probes_le_class {α : Type}
    (environment : Environment CountAux Guess.GCoord Digest PUnit)
    (sampler : Sampler Guess.GCoord Digest PUnit) (program : OracleComp CountSpec α) (budget : Nat)
    (hclass : ∀ result ∈ support (cappedProgram program budget),
      (result.2.map probeStep).sum ≤ probeCount (publicInputs result.2))
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun environment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  unfold cappedProgram at hclass hr
  exact recorded_probes_le_class environment sampler
    (SphincsSecurity.QueryCap.run charged program budget) hclass result hr

theorem cappedWorld_probes_le_class_for (sampler : Sampler Guess.GCoord Digest PUnit)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) := by
  have hc : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by
    unfold cappedWorld; rfl
  have hr' := Eq.mp (congrArg (fun program => withRun countEnvironment sampler program countInit result ≠ 0) hc) hr
  have hp := cappedWorld_probe_count hU ω adversary budget
  have hp' := Eq.mp (congrArg (fun program => ∀ result ∈ support program,
    (result.2.map probeStep).sum ≤ probeCount (publicInputs result.2)) hc) hp
  exact cappedProgram_probes_le_class countEnvironment sampler (worldC hU ω adversary) budget hp' result hr'

theorem cappedWorld_probes_le_class (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ probeCount (publicInputs result.1.2) :=
  cappedWorld_probes_le_class_for hU ω (Guess.Fam.sampler PUnit) adversary budget result hr

theorem clockCredit_le_charged (input : CountSpec.Domain) :
    clockCredit input ≤ if charged input then 1 else 0 := by
  rcases input with (n | x) | (p | c)
  · exact Nat.zero_le _
  · cases x with
    | none => exact Nat.zero_le _
    | some x =>
        simp only [clockCredit, charged, if_true]
        split <;> omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem clockCredits_le_calls (inputs : List CountSpec.Domain) :
    (inputs.map clockCredit).sum ≤ SphincsSecurity.QueryCap.calls charged inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rw [List.map_cons, List.sum_cons, SphincsSecurity.QueryCap.calls_cons]
      exact Nat.add_le_add (clockCredit_le_charged input) ih

theorem cappedProgram_calls_le {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (result : Option (α × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedProgram program budget)) :
    SphincsSecurity.QueryCap.calls charged result.2 ≤ budget := by
  exact SphincsSecurity.QueryCap.recorded_calls_le charged
    (SphincsSecurity.QueryCap.run charged program budget) (fun _ => budget)
    (fun value hv => SphincsSecurity.QueryCap.counted_le_of_queryBound charged _ budget
      (SphincsSecurity.QueryCap.run_queryBound charged _ budget) value hv) result hr

theorem cappedWorld_probes_le_budget_for (sampler : Sampler Guess.GCoord Digest PUnit)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ budget := by
  have hs := withRun_result_support countEnvironment sampler
    (cappedWorld hU ω adversary budget) countInit result hr
  have heq : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by
    unfold cappedWorld; rfl
  have hs' := Eq.mp (congrArg (fun program => result.1 ∈ support program) heq) hs
  have hc := cappedProgram_calls_le (worldC hU ω adversary) budget result.1 hs'
  calc
    result.2.probes ≤ probeCount (publicInputs result.1.2) :=
      cappedWorld_probes_le_class_for hU ω sampler adversary budget result hr
    _ = (result.1.2.map clockCredit).sum := (clockCredit_sum _).symm
    _ ≤ SphincsSecurity.QueryCap.calls charged result.1.2 := clockCredits_le_calls _
    _ ≤ budget := hc

theorem cappedWorld_probes_le_budget (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget)
      countInit result ≠ 0) : result.2.probes ≤ budget :=
  cappedWorld_probes_le_budget_for hU ω (Guess.Fam.sampler PUnit) adversary budget result hr

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

theorem fixed_count_noFail (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (state : CountState) :
    Pr[⊥ | fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state] = 0 := by
  have h := congrArg (fun law : SPMF α => Pr[⊥ | law])
    (fixedRun_projection countAuxImpl (Guess.Fam.phi g.1 g.2) program state)
  have hn : Pr[⊥ | 𝒮[simulateQ (fixedAnswers countAuxImpl (Guess.Fam.phi g.1 g.2)) program]] = 0 := by simp
  simpa only [probFailure_map, countEnvironment] using h.trans hn

theorem count_noFail {α : Type} (program : OracleComp CountSpec α) :
    Pr[⊥ | withRun countEnvironment (Guess.Fam.sampler PUnit) program countInit] = 0 := by
  rw [← Guess.Fam.fam_erasure countEnvironment program countInit (Guess.Fam.inv_initial PUnit.unit)]
  change Pr[⊥ | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun countEnvironment g program countInit] = 0
  rw [hiddenLaw_univ_bind, probFailure_bind_eq_add_tsum]
  simp only [fixed_count_noFail, mul_zero, tsum_zero, add_zero]
  simp

theorem count_total_mass {α : Type} (program : OracleComp CountSpec α) :
    (∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit) program countInit]) = 1 :=
  tsum_probOutput_eq_one' (count_noFail program)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

/-- Accounting queries do not change the cryptographic transcript or the
    hidden-family state. This erasure keeps the original near-event semantics. -/
noncomputable def dropClocks {α : Type} (program : OracleComp CountSpec α) : OracleComp WSpec α :=
  simulateQ (fun input => match input with
    | .inl (.inl n) => liftM (WSpec.query (.inl n))
    | .inl (.inr _) => pure ()
    | .inr query => liftM (WSpec.query (.inr query))) program

theorem dropClocks_pure {α : Type} (value : α) :
    dropClocks (pure value : OracleComp CountSpec α) = pure value := rfl

theorem dropClocks_bind {α β : Type} (program : OracleComp CountSpec α)
    (next : α → OracleComp CountSpec β) :
    dropClocks (program >>= next) = (dropClocks program >>= fun value => dropClocks (next value)) :=
  simulateQ_bind _ _ _

theorem dropClocks_liftW {α : Type} (program : OracleComp WSpec α) :
    dropClocks (liftW program) = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with n | (p | c)
      all_goals
        simp only [liftW, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer

theorem dropClocks_clock (input : Option HashInput) : dropClocks (clock input) = pure () := rfl

theorem dropClocks_clocks (n : Nat) : dropClocks (clocks n) = pure () := by
  induction n with
  | zero => rfl
  | succ n ih => rw [clocks, dropClocks_bind, dropClocks_clock, pure_bind, ih]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem dropClocks_hashC (x : HashInput) : dropClocks (hashC hU ω x) = hashW hU ω x := by
  rw [hashC, dropClocks_bind, dropClocks_clock, pure_bind, dropClocks_liftW]

theorem dropClocks_signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    dropClocks (signC hU ω published request) = signW hU ω published request := by
  rw [signC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_liftW]

theorem dropClocks_interactionC (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    dropClocks (interactionC hU ω published program) = interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, interactionW_coin, dropClocks_bind]
        change (liftM (WSpec.query (.inl n)) >>= _) = _
        apply bind_congr
        intro answer
        exact ih answer
      · rw [interactionC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [interactionC_request, dropClocks_bind, dropClocks_signC]
        change (_ >>= _) = (signW hU ω published request >>= fun signature =>
          interactionW hU ω published (next signature) >>= fun rest =>
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
        apply bind_congr
        intro signature
        rw [dropClocks_bind, ih]
        rfl

theorem dropClocks_programC {α : Type} (program : M α) :
    dropClocks (programC hU ω program) = programW hU ω program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | coordinate
      · rw [programC_coin, dropClocks_bind]
        change (_ >>= _) = (liftM (WSpec.query (.inl n)) >>= fun answer => programW hU ω (next answer))
        apply bind_congr
        intro answer
        exact ih answer
      · rw [programC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
          pure (rest.1, (x, answer) :: rest.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [programC_private]
        exact ih (0 : HashOutput)

theorem dropClocks_worldC (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) :
    dropClocks (worldC hU ω adversary) = worldGame hU ω adversary := by
  unfold worldC worldGame
  rw [dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_bind, dropClocks_interactionC]
  apply bind_congr
  intro interaction
  rw [dropClocks_bind, dropClocks_programC]
  rfl

theorem fixedRun_dropClocks (g : CanonTable.HiddenF) {α : Type} (program : OracleComp CountSpec α)
    (state : CountState) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state =
      fixedRun env (Guess.Fam.phi g.1 g.2) (dropClocks program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with (n | x) | (p | c)
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2
      · change fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock x >>= next) state =
          fixedRun env (Guess.Fam.phi g.1 g.2) (dropClocks (clock x >>= next)) state
        rw [dropClocks_bind, dropClocks_clock, pure_bind]
        simp only [fixedRun, runWith, simulateQ_bind, StateT.run_bind]
        change (fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (clock x) state >>=
          fun middle => fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2) = _
        rw [fixedRun_clock, pure_bind]
        simpa only [fixedRun, runWith] using ih () state
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2
      · simp only [fixedRun, runWith_query_bind, dropClocks, simulateQ_bind, simulateQ_spec_query]
        apply bind_congr
        intro answer
        exact ih answer.1 answer.2

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

theorem fixedRun_bind_counted (g : CanonTable.HiddenF) {α β : Type}
    (program : OracleComp CountSpec α) (next : α → OracleComp CountSpec β) (state : CountState) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (program >>= next) state =
      (fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state >>= fun middle =>
        fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2) := by
  simp only [fixedRun, runWith, simulateQ_bind, StateT.run_bind]

/-- A completed capped run is a run of the uncapped program with exactly the
    same secret-family state. Aborted prefixes are intentionally excluded. -/
theorem fixedRun_cap_completed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (budget : Nat) (state final : CountState)
    (value : α) (remaining : Nat)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (SphincsSecurity.QueryCap.run charged program budget) state (some (value, remaining), final) ≠ 0) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state (value, final) ≠ 0 := by
  induction program using OracleComp.inductionOn generalizing budget state final remaining with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.run_pure, fixedRun, runWith_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq, Option.some.injEq] at hr
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
      simp [fixedRun, runWith_pure]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind] at hr
      by_cases hc : charged input
      · rw [if_pos hc] at hr
        cases budget with
        | zero => simpa [fixedRun, runWith_pure] using hr
        | succ budget =>
            simp only [fixedRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr ⊢
            obtain ⟨middle, hm, hr⟩ := hr
            exact ⟨middle, hm, ih middle.1 budget middle.2 final remaining hr⟩
      · rw [if_neg hc] at hr
        simp only [fixedRun, runWith_query_bind, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero] at hr ⊢
        obtain ⟨middle, hm, hr⟩ := hr
        exact ⟨middle, hm, ih middle.1 budget middle.2 final remaining hr⟩

theorem fixedRun_recorded_forget (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (state final : CountState) (value : α) (queries : List CountSpec.Domain)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (SphincsSecurity.QueryCap.recorded program) state ((value, queries), final) ≠ 0) :
    fixedRun countEnvironment (Guess.Fam.phi g.1 g.2) program state (value, final) ≠ 0 := by
  have hmap : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (Prod.fst <$> SphincsSecurity.QueryCap.recorded program) state (value, final) ≠ 0 := by
    rw [← bind_pure_comp, fixedRun_bind_counted, SphincsSecurity.Concrete.RetainedObservation.bind_nonzero]
    refine ⟨((value, queries), final), hr, ?_⟩
    simp [fixedRun, runWith_pure]
  simpa only [SphincsSecurity.QueryCap.recorded_forget] using hmap

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem fixedRun_recorded_cap_erasure (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (erased : OracleComp WSpec α)
    (herased : dropClocks program = erased) (budget remaining : Nat)
    (value : α) (queries : List CountSpec.Domain) (start final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedProgram program budget)
      start ((some (value, remaining), queries), final) ≠ 0) :
    fixedRun env (Guess.Fam.phi g.1 g.2) erased start (value, final) ≠ 0 := by
  unfold cappedProgram at hr
  have hrec := fixedRun_recorded_forget g
    (SphincsSecurity.QueryCap.run charged program budget) start final (some (value, remaining)) queries hr
  have hfull := fixedRun_cap_completed g program budget start final value remaining hrec
  rw [fixedRun_dropClocks, herased] at hfull
  exact hfull

set_option backward.isDefEq.respectTransparency true in
theorem cappedWorld_completed_support (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0) :
    fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init (result, final) ≠ 0 := by
  have hc : cappedWorld hU ω adversary budget = cappedProgram (worldC hU ω adversary) budget := by unfold cappedWorld; rfl
  have hr' := Eq.mp (congrArg (fun program => fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
    program countInit ((some (result, remaining), queries), final) ≠ 0) hc) hr
  have hs := fixedRun_recorded_cap_erasure g (worldC hU ω adversary) (worldGame hU ω adversary)
    (dropClocks_worldC hU ω adversary) budget remaining result queries countInit final hr'
  have hi : countInit = init := rfl
  exact Eq.mp (congrArg (fun state => fixedRun env (Guess.Fam.phi g.1 g.2)
    (worldGame hU ω adversary) state (result, final) ≠ 0) hi) hs

theorem cappedWorld_completed_noBad (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0)
    (hno : ¬OverflowIn (wA hU ω g) result.2.1) : ¬Guess.Fam.Bad final :=
  worldGame_noBad hU ω g adversary (result, final)
    (cappedWorld_completed_support hU ω g adversary budget remaining result queries final hr) hno

theorem cappedWorld_completed_guessed (g : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget remaining : Nat)
    (result : Bool × QueryLog Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi g.1 g.2)
      (cappedWorld hU ω adversary budget) countInit ((some (result, remaining), queries), final) ≠ 0)
    (coordinate : Guess.GCoord) (hg : GuessedIn (wA hU ω g) result.2.1 result.2.2 coordinate) :
    final.guesses.Nonempty := by
  have ht := worldGame_tracking hU ω g adversary (result, final)
    (cappedWorld_completed_support hU ω g adversary budget remaining result queries final hr)
  exact Guess.nonempty_of_prefixIn (ht.2 coordinate hg)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The first hidden-family hit is paid by actual external FTS probes. Internal
    signing charges and unrelated WOTS queries do not contribute to this cost. -/
theorem first_probe_le_external (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128) :
    Pr[fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty |
      withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result |
          withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply CountedFirst.event_le_class_cost (Guess.Fam.hazardFam countEnvironment budget)
    (cappedWorld hU ω adversary budget) countInit (Guess.Fam.inv_initial PUnit.unit)
    rfl rfl hbudget (count_total_mass _) _ (fun _ _ h => h)
    (fun result => probeCount (publicInputs result.1.2))
  intro result hr
  exact (Nat.min_le_left _ _).trans (cappedWorld_probes_le_class hU ω adversary budget result hr)

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
abbrev CountResult := Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain

noncomputable def countedProgramRun (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :
    ProbComp (CanonTable.HiddenF × (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) := do
  let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
  let result ← simulateQ (fixedCount hidden) program
  pure (hidden, result)
noncomputable def countedFtsRun (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    ProbComp (CanonTable.HiddenF × (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :=
  countedProgramRun (cappedWorld hU ω adversary budget)

/-- Transfer events from the eagerly sampled hidden family to the lazy engine
    before applying the expected-probe estimate. -/
theorem counted_program_event_le_world (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain))
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (wevent : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState → Prop)
    (himp : ∀ hidden result, fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun program] ≤
      Pr[wevent | withRun countEnvironment (Guess.Fam.sampler PUnit)
        program countInit] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun hidden =>
    fixedRun countEnvironment hidden program countInit]
  rw [hiddenLaw_univ_bind]
  unfold countedProgramRun
  simp only [bind_pure_comp]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  have hfixed := fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
    program countInit
  change (Prod.fst <$> fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [← probEvent_evalSPMF, ← hfixed, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp hidden result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he

set_option backward.isDefEq.respectTransparency true in
theorem counted_event_le_world (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (wevent : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState → Prop)
    (himp : ∀ hidden result, fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU ω adversary budget) countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      Pr[wevent | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU ω adversary budget) countInit] :=
  counted_program_event_le_world (cappedWorld hU ω adversary budget) event wevent himp

noncomputable def fixedSampler (labels : Guess.GCoord → Digest) : Sampler Guess.GCoord Digest PUnit where
  trialLaw _ coordinate value := pure (decide (labels coordinate = value))
  discloseLaw _ coordinate := pure (labels coordinate)

theorem withRun_fixedSampler (labels : Guess.GCoord → Digest) {α : Type}
    (program : OracleComp CountSpec α) (state : CountState) :
    withRun countEnvironment (fixedSampler labels) program state =
      fixedRun countEnvironment labels program state := by
  have he : withImpl countEnvironment (fixedSampler labels) = fixedImpl countEnvironment labels := by
    funext input
    rcases input with auxiliary | (probe | coordinate)
    · rfl
    · rcases probe with ⟨coordinate, value⟩
      funext state
      simp only [withImpl, fixedSampler, fixedImpl, StateT.run_mk, map_pure]
    · funext state
      simp only [withImpl, fixedSampler, fixedImpl, StateT.run_mk, map_pure]
  unfold withRun fixedRun
  rw [he]

theorem fixed_probes_le_budget (hidden : CanonTable.HiddenF)
    (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat)
    (result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU ω adversary budget) countInit result ≠ 0) : result.2.probes ≤ budget := by
  apply cappedWorld_probes_le_budget_for hU ω
    (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) adversary budget result
  rwa [withRun_fixedSampler]

/-- All cryptographic hypotheses of the first-hit estimate are checked on
    completed runs; an incomplete run cannot count as a forgery. -/
theorem counted_event_le_external (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧
      ¬OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ coordinate, GuessedIn (wA hU ω hidden) output.2.1 output.2.2 coordinate) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
          (cappedWorld hU ω adversary budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply (counted_event_le_world hU ω adversary budget event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (first_probe_le_external hU ω adversary budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, coordinate, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  refine ⟨cappedWorld_completed_noBad hU ω hidden adversary budget remaining output queries final hr hno,
    ?_, cappedWorld_completed_guessed hU ω hidden adversary budget remaining output queries final hr coordinate hg⟩
  exact fixed_probes_le_budget hU ω hidden adversary budget _ hr

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The exact public trace law is the reference experiment's law, including
    a prefix left by an exhausted budget. This is what identifies the payment
    above with the `OtherQuery` budget rather than a fresh global query bound. -/
theorem public_program_distribution (program : OracleComp CountSpec (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) program countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← simulateQ (fixedCount hidden) program
      pure (publicInputs result.2)] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit), map_bind]
  change (Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun labels =>
    (fun result => publicInputs result.1.2) <$>
      fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment labels program countInit) = _
  rw [hiddenLaw_univ_bind]
  apply SPMF.ext
  intro inputs
  rw [← SPMF.probOutput_eq_apply, ← SPMF.probOutput_eq_apply]
  simp only [probOutput_evalSPMF]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  congr 1
  have hfixed := congrArg (Functor.map (fun result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) => publicInputs result.2))
    (fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
      program countInit)
  simp only [Functor.map_map] at hfixed
  change ((fun result => publicInputs result.1.2) <$>
    fixedRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    (fun result => publicInputs result.2) <$>
      𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [hfixed]
  simp only [← evalSPMF_map, probOutput_evalSPMF, bind_pure_comp]

set_option backward.isDefEq.respectTransparency true in
theorem public_distribution (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) (cappedWorld hU ω adversary budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← Wots.offlineRun (wA hU ω hidden) adversary budget
      pure (refPublicInputs result.2)] := by
  rw [public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using worldC_public_transport hU ω hidden adversary budget

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

/-- The first-hit payment is bounded by the actual reference experiment's
    external `OtherQuery` count, with the same query cap and the same trace. -/
theorem public_payment_le_reference (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (budget : Nat) :
    (∑' result, Pr[= result | withRun (Result := (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedWorld hU ω adversary budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.offlineRun (wA hU ω hidden) adversary budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω adversary budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other (wA hU ω hidden) _
    (SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2)

end ClaudeWCT.W9.T3.Security.WPair.Counted


namespace ClaudeWCT.W9.T3.Security.WPair.Counted
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] worldC cappedWorld worldGame Wots.offlineRun
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem counted_event_le_other (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget < 2 ^ 128)
    (event : CanonTable.HiddenF → (Option ((Bool × QueryLog Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧
      ¬OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ coordinate, GuessedIn (wA hU ω hidden) output.2.1 output.2.2 coordinate) :
    Pr[fun result => event result.1 result.2 | countedProgramRun (cappedWorld hU ω adversary budget)] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.offlineRun (wA hU ω hidden) adversary budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          SigGolfCandidate.T3.Security.Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) := by
  exact (counted_event_le_external hU ω adversary budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference hU ω adversary budget))

end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask (queried_length_bind queried_length_pure
  queried_length_shortHash queried_length_foldlM sum_map_one)
open ClaudeWCT.WCT9
open WPair.Counted (queried_length_buildChildF queried_length_buildChildH queried_length_ftsCoefs queried_free
  queried_length_free)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem queried_length_sharedNode (answers : Answers) (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    (SourceReplay.queried answers (sharedNode first coord index heap pads left right)).length = 1 := by
  unfold sharedNode sharedOuterHash
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · unfold wctNodeHashH ftsHash
      split <;> rfl

theorem queried_length_sharedHeap (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) :
    (SourceReplay.queried answers (sharedHeap first index coord pads leaves)).length =
      if first then 124 else 126 := by
  unfold sharedHeap
  rw [queried_length_foldlM answers _ _ (fun _ => 1) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_sharedNode, queried_length_pure]), sum_map_one,
    List.length_reverse, List.length_range']

theorem queried_length_buildSharedCoordinate (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    (SourceReplay.queried answers (buildSharedCoordinate first index coord selected word pads)).length =
      3227 + (if first then 124 else 126) := by
  unfold buildSharedCoordinate
  rw [queried_length_bind, queried_length_ftsCoefs, queried_length_bind,
    queried_length_foldlM answers _ _ (fun _ => 25) (fun _ _ _ => by
      rw [queried_length_bind, queried_length_buildChildH, queried_length_pure]),
    queried_length_bind, queried_length_sharedHeap, queried_length_pure]
  have : ((List.range 128).map (fun _ => (25 : Nat))).sum = 3200 := by decide
  simp only [this]
  omega

theorem queried_length_buildPair (answers : Answers) (index pair : Nat)
    (selected : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot) :
    (SourceReplay.queried answers (buildPair index pair selected aWord bWord prev)).length = 6704 := by
  unfold buildPair
  rw [queried_length_bind, queried_length_buildSharedCoordinate, queried_length_bind,
    queried_length_buildSharedCoordinate, queried_length_pure]
  decide

theorem queried_length_buildSingleton (answers : Answers) (index : Nat)
    (selected : Child) (word : Rank) (prev : PairRoot) :
    (SourceReplay.queried answers (buildSingleton index selected word prev)).length = 3353 := by
  unfold buildSingleton
  rw [queried_length_bind, queried_length_buildSharedCoordinate, queried_length_pure]
  decide

theorem queried_length_buildForest (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (SourceReplay.queried answers (buildForest index selected words)).length = 30169 := by
  unfold buildForest
  rw [queried_length_bind, queried_length_foldlM answers _ _ (fun _ => 6704) (fun _ _ _ => by
    rw [queried_length_bind, queried_length_buildPair, queried_length_pure]),
    queried_length_bind, queried_length_buildSingleton, queried_length_pure]
  decide

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

attribute [local irreducible] searchPreparedLayers prepareRoots buildForest
  sharedDigestSearch forestCommitment

theorem signFromOutput_charge_eq (hidden hidden' : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    (SourceReplay.queried (wA hU omega hidden) (signFromOutput cache rho counter output)).length =
      (SourceReplay.queried (wA hU omega hidden') (signFromOutput cache rho counter output)).length := by
  unfold signFromOutput
  conv_lhs => rw [queried_length_bind, queried_length_buildForest]
  conv_rhs => rw [queried_length_bind, queried_length_buildForest]
  apply congrArg (Nat.add _)
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (prepareRoots_free _),
    eval_free hU omega hidden hidden' (prepareRoots_free _),
    buildForest_commitment, buildForest_commitment,
    forestCommitment_world hU omega hidden hidden' (digestIndex output) (digestIndex_lt output)]
  apply congrArg (Nat.add _)
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (searchPreparedLayers_free _ _ _ _),
    eval_free hU omega hidden hidden' (searchPreparedLayers_free _ _ _ _)]
  apply congrArg (Nat.add _)
  trans 0
  · split <;> exact queried_length_pure _ _
  · symm
    split <;> exact queried_length_pure _ _

noncomputable def signCharge (answers : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried answers (authenticatedSign published request)).length

theorem signCharge_eq (hidden hidden' : CanonTable.HiddenF)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    signCharge (wA hU omega hidden) published request = signCharge (wA hU omega hidden') published request := by
  unfold signCharge authenticatedSign
  conv_lhs => rw [queried_length_bind]
  conv_rhs => rw [queried_length_bind]
  rw [queried_length_free hU omega hidden hidden' (privateMac_free _)]
  apply congrArg (Nat.add _)
  by_cases hc : request.cache = published
  · rw [if_pos hc]
    unfold SigGolfCandidate.Research.SharedForest.signPayload
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [queried_length_free hU omega hidden hidden' (privateNonce_free _),
      eval_free hU omega hidden hidden' (privateNonce_free _)]
    apply congrArg (Nat.add _)
    conv_lhs => rw [queried_length_bind]
    conv_rhs => rw [queried_length_bind]
    rw [queried_length_free hU omega hidden hidden' (sharedDigestSearch_free _ _ _ _),
      eval_free hU omega hidden hidden' (sharedDigestSearch_free _ _ _ _)]
    apply congrArg (Nat.add _)
    cases evalWithAnswerFn (wA hU omega hidden') (sharedDigestSearch
        (evalWithAnswerFn (wA hU omega hidden') (privateNonce request.message)) request.message 0 digestAttemptLimit) with
    | none => exact (queried_length_pure _ _).trans (queried_length_pure _ _).symm
    | some found =>
      obtain ⟨counter, output⟩ := found
      dsimp only
      conv_lhs => rw [queried_length_bind]
      conv_rhs => rw [queried_length_bind]
      rw [signFromOutput_charge_eq hU omega hidden hidden']
      apply congrArg (Nat.add _)
      trans 0
      · split <;> exact queried_length_pure _ _
      · symm
        split <;> exact queried_length_pure _ _
  · rw [if_neg hc]
    exact (queried_length_pure _ _).trans (queried_length_pure _ _).symm
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted.Generic
attribute [local instance] Classical.propDecidable
attribute [local instance] chargedDecidable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def countedProgramRun {α : Type} (program : OracleComp CountSpec α) :
    ProbComp (CanonTable.HiddenF × α) := do
  let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
  let result ← simulateQ (fixedCount hidden) program
  pure (hidden, result)
theorem counted_program_event_le_world {α : Type} (program : OracleComp CountSpec α)
    (event : CanonTable.HiddenF → α → Prop)
    (wevent : α × CountState → Prop)
    (himp : ∀ hidden result, fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit result ≠ 0 → event hidden result.1 → wevent result) :
    Pr[fun result => event result.1 result.2 | countedProgramRun program] ≤
      Pr[wevent | withRun countEnvironment (Guess.Fam.sampler PUnit)
        program countInit] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun hidden =>
    fixedRun countEnvironment hidden program countInit]
  rw [hiddenLaw_univ_bind]
  unfold countedProgramRun
  simp only [bind_pure_comp]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  have hfixed := fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
    program countInit
  change (Prod.fst <$> fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [← probEvent_evalSPMF, ← hfixed, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp hidden result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he


theorem capped_probe_count {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (result : Option (α × Nat) × List CountSpec.Domain)
    (hr : result ∈ support (cappedProgram program budget)) :
    (result.2.map (probeStep (auxSpec := CountAux))).sum ≤ probeCount (publicInputs result.2) := by
  have h := funded_recorded_bound _ 0 (funded_run program 0 budget hf) result hr
  simpa only [Nat.zero_add, clockCredit_sum] using h

theorem capped_probes_le_class {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (sampler : Sampler Guess.GCoord Digest PUnit)
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ probeCount (publicInputs result.1.2) :=
  cappedProgram_probes_le_class countEnvironment sampler program budget
    (capped_probe_count program budget hf) result hr

theorem capped_probes_le_budget {α : Type} (program : OracleComp CountSpec α) (budget : Nat)
    (hf : Funded program 0) (sampler : Sampler Guess.GCoord Digest PUnit)
    (result : (Option (α × Nat) × List CountSpec.Domain) × CountState)
    (hr : withRun countEnvironment sampler (cappedProgram program budget) countInit result ≠ 0) :
    result.2.probes ≤ budget := by
  have hs := withRun_result_support countEnvironment sampler (cappedProgram program budget) countInit result hr
  calc
    result.2.probes ≤ probeCount (publicInputs result.1.2) := capped_probes_le_class program budget hf sampler result hr
    _ = (result.1.2.map clockCredit).sum := (clockCredit_sum _).symm
    _ ≤ SphincsSecurity.QueryCap.calls charged result.1.2 := clockCredits_le_calls _
    _ ≤ budget := cappedProgram_calls_le program budget result.1 hs

theorem first_probe_le_external {α : Type} (program : OracleComp CountSpec α)
    (hf : Funded program 0) (budget : Nat) (hbudget : budget < 2 ^ 128) :
    Pr[fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty |
      withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedProgram program budget) countInit] ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ *
        ∑' result, Pr[= result |
          withRun countEnvironment (Guess.Fam.sampler PUnit) (cappedProgram program budget) countInit] *
            (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply CountedFirst.event_le_class_cost (Guess.Fam.hazardFam countEnvironment budget)
    (cappedProgram program budget) countInit (Guess.Fam.inv_initial PUnit.unit)
    rfl rfl hbudget (count_total_mass _) _ (fun _ _ h => h)
    (fun result => probeCount (publicInputs result.1.2))
  intro result hr
  exact (Nat.min_le_left _ _).trans
    (capped_probes_le_class program budget hf (Guess.Fam.sampler PUnit) result hr)
theorem public_program_distribution {α : Type} (program : OracleComp CountSpec (α × List CountSpec.Domain)) :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := (α × List CountSpec.Domain)) countEnvironment (Guess.Fam.sampler PUnit) program countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← simulateQ (fixedCount hidden) program
      pure (publicInputs result.2)] := by
  rw [← Guess.Fam.fam_erasure countEnvironment program
    countInit (Guess.Fam.inv_initial PUnit.unit), map_bind]
  change (Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun labels =>
    (fun result => publicInputs result.1.2) <$>
      fixedRun (Result := (α × List CountSpec.Domain)) countEnvironment labels program countInit) = _
  rw [hiddenLaw_univ_bind]
  apply SPMF.ext
  intro inputs
  rw [← SPMF.probOutput_eq_apply, ← SPMF.probOutput_eq_apply]
  simp only [probOutput_evalSPMF]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro hidden
  simp only [probOutput_evalSPMF, probOutput_uniformSample]
  congr 1
  have hfixed := congrArg (Functor.map (fun result : (α × List CountSpec.Domain) => publicInputs result.2))
    (fixedRun_projection countAuxImpl (Guess.Fam.phi hidden.1 hidden.2)
      program countInit)
  simp only [Functor.map_map] at hfixed
  change ((fun result => publicInputs result.1.2) <$>
    fixedRun (Result := (α × List CountSpec.Domain)) countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      program countInit) =
    (fun result => publicInputs result.2) <$>
      𝒮[simulateQ (fixedCount hidden) program] at hfixed
  rw [hfixed]
  simp only [← evalSPMF_map, probOutput_evalSPMF, bind_pure_comp]


end ClaudeWCT.W9.T3.Security.WPair.Counted.Generic

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp CountSpec (Option SigGolfCandidate.Research.SharedForest.Signature) := do
  clocks (Paired.signCharge (wA hU ω 0) published request)
  liftW (Paired.signW hU ω published request)
noncomputable def interactionC (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Paired.Interaction α → OracleComp CountSpec (α × QueryLog Paired.Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (CountSpec.query (.inl (.inl n))) : OracleComp CountSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashC hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signC hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))

noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option SigGolfCandidate.Research.SharedForest.Signature) :=
  ticks (Paired.signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (Paired.authenticatedSign published request))
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Paired.Interaction α → OracleComp RefWorld (α × QueryLog Paired.Requests) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl input => do
          let answer ← (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (SphincsSecurity.OracleWorld.Range input))
          next answer
      | .inr request => do
          let signature ← offlineSign T published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2))
theorem offlineInteraction_pure (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp Paired.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp Paired.Interaction α) :
    offlineInteraction T published (liftM (Paired.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := rfl
theorem offlineInteraction_request (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Paired.Interaction α) :
    offlineInteraction T published (liftM (Paired.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun signature => offlineInteraction T published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2)) := rfl
theorem observed_run_signC_bind (g : CanonTable.HiddenF) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp CountSpec α) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged (signC hU ω published request >>= next) budget) =
      if Paired.signCharge (wA hU ω g) published request ≤ budget then
        observed g (SphincsSecurity.QueryCap.run charged
          (next (evalWithAnswerFn (wA hU ω g) (Paired.authenticatedSign published request)))
          (budget - Paired.signCharge (wA hU ω g) published request))
      else pure (none, []) := by
  simp only [signC, bind_assoc, observed_run_clocks_bind]
  rw [Paired.signCharge_eq hU ω 0 g]
  split_ifs
  · rw [observed_run_liftW_bind, Paired.fixed_signW, pure_bind]
  · rfl

theorem refObserved_run_offlineSign_bind (T : Answers) {α : Type}
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp RefWorld α) (budget : Nat) :
    refObserved T (SphincsSecurity.QueryCap.run RefCharged
      (offlineSign T published request >>= next) budget) =
      if Paired.signCharge T published request ≤ budget then
        refObserved T (SphincsSecurity.QueryCap.run RefCharged
          (next (evalWithAnswerFn T (Paired.authenticatedSign published request)))
          (budget - Paired.signCharge T published request))
      else pure (none, []) := by
  simp only [offlineSign, bind_assoc, pure_bind, refObserved_run_ticks_bind]

theorem interactionC_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionC hU ω published (pure value : OracleComp Paired.Interaction α) = pure (value, [], []) := rfl
theorem interactionC_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inl (.inl n))) >>= next) =
      (liftM (CountSpec.query (.inl (.inl n))) >>= fun coin => interactionC hU ω published (next coin)) := rfl
theorem interactionC_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inl (.inr x))) >>= next) =
      (hashC hU ω x >>= fun answer => interactionC hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionC_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Paired.Interaction α) :
    interactionC hU ω published (liftM (Paired.Interaction.query (.inr request)) >>= next) =
      (signC hU ω published request >>= fun signature => interactionC hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

/-- The count world and the reference experiment have the same capped public
    transcript, including the prefix retained when the query budget expires. -/
theorem interactionC_transport (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α β : Type}
    (program : OracleComp Paired.Interaction α)
    (nextC : (α × QueryLog Paired.Requests) → OracleComp CountSpec β)
    (nextR : (α × QueryLog Paired.Requests) → OracleComp RefWorld β)
    (hn : ∀ value budget,
      observed g (SphincsSecurity.QueryCap.run charged (nextC value) budget) =
        refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged (nextR value) budget))
    (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (interactionC hU ω published program >>= fun result => nextC (result.1, result.2.1)) budget) =
    refObserved (wA hU ω g) (SphincsSecurity.QueryCap.run RefCharged
      (offlineInteraction (wA hU ω g) published program >>= nextR) budget) := by
  induction program using OracleComp.inductionOn generalizing nextC nextR budget with
  | pure value =>
      rw [interactionC_pure, offlineInteraction_pure, pure_bind, pure_bind]
      exact hn (value, []) budget
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, offlineInteraction_world, bind_assoc, bind_assoc,
          observed_run_coin_bind, refObserved_run_coin_bind]
        apply bind_congr
        intro coin
        exact ih coin nextC nextR hn budget
      · rw [interactionC_public, offlineInteraction_world]
        simp only [bind_assoc, pure_bind]
        rw [observed_run_hashC_bind, refObserved_run_public_bind]
        cases budget with
        | zero => rfl
        | succ remaining => exact congrArg _ (ih _ nextC nextR hn remaining)
      · rw [interactionC_request, offlineInteraction_request]
        simp only [bind_assoc, pure_bind, bind_map_left]
        rw [observed_run_signC_bind, refObserved_run_offlineSign_bind]
        split_ifs
        · exact ih _
            (fun value => nextC (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (Paired.authenticatedSign published request)⟩ :: value.2))
            (fun value => nextR (value.1, ⟨request, evalWithAnswerFn (wA hU ω g)
              (Paired.authenticatedSign published request)⟩ :: value.2))
            (fun value remaining => hn _ remaining) _
        · rfl


end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
attribute [local irreducible] signC interactionC Paired.signCharge WPair.Counted.hashC WPair.Counted.programC keygen
theorem funded_signC_bind {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp CountSpec α) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (signC hU ω published request >>= next) credit := by
  rw [signC, bind_assoc]
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  unfold Paired.signW
  rw [liftW_bind, bind_assoc]
  simp only [liftW_pure, pure_bind]
  exact funded_discloseAll_bind _ _ _ (fun values remaining => hn _ remaining)

theorem funded_interactionC_bind {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α)
    (next : (α × QueryLog Paired.Requests × List Wots.Entry) → OracleComp CountSpec β) (credit : Nat)
    (hn : ∀ value remaining, Funded (next value) remaining) :
    Funded (interactionC hU ω published program >>= next) credit := by
  induction program using OracleComp.inductionOn generalizing next credit with
  | pure value => simpa only [interactionC_pure, pure_bind] using hn (value, [], []) credit
  | query_bind input continuation ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, bind_assoc, funded_query_bind]
        refine ⟨Nat.zero_le _, ?_⟩
        intro coin
        exact ih coin next credit hn
      · rw [interactionC_public]
        simp only [bind_assoc, pure_bind]
        apply funded_hashC_bind
        intro answer remaining
        exact ih answer _ remaining (fun result remaining => hn _ remaining)
      · rw [interactionC_request]
        simp only [bind_assoc, pure_bind]
        apply funded_signC_bind
        intro signature remaining
        exact ih signature _ remaining (fun result remaining => hn _ remaining)

theorem dropClocks_signC (published : SigGolfCandidate.T3.Cache) (request : Request) :
    dropClocks (signC hU ω published request) = Paired.signW hU ω published request := by
  rw [signC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_liftW]

theorem dropClocks_interactionC (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Paired.Interaction α) :
    dropClocks (interactionC hU ω published program) = Paired.interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionC_pure, Paired.interactionW_pure, dropClocks_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionC_coin, Paired.interactionW_coin, dropClocks_bind]
        change (liftM (WSpec.query (.inl n)) >>= _) = _
        apply bind_congr
        intro answer
        exact ih answer
      · rw [interactionC_public, dropClocks_bind, dropClocks_hashC]
        change (_ >>= _) = (hashW hU ω x >>= fun answer => Paired.interactionW hU ω published (next answer) >>= fun rest =>
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2))
        apply bind_congr
        intro answer
        rw [dropClocks_bind, ih]
        rfl
      · rw [interactionC_request, dropClocks_bind, dropClocks_signC]
        change (_ >>= _) = (Paired.signW hU ω published request >>= fun signature =>
          Paired.interactionW hU ω published (next signature) >>= fun rest =>
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
        apply bind_congr
        intro signature
        rw [dropClocks_bind, ih]
        rfl


noncomputable def experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    OracleComp CountSpec (β × QueryLog Paired.Requests × List Wots.Entry) := do
  let interaction ← interactionC hU ω published program
  let result ← WPair.Counted.programC hU ω (finish (interaction.1, interaction.2.1))
  pure (result.1, interaction.2.1, interaction.2.2 ++ result.2)
noncomputable def experimentR {α β : Type} (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    OracleComp RefWorld β := do
  let interaction ← offlineInteraction answers published program
  simulateQ Wots.verdictImpl (finish interaction)
noncomputable def referenceRun {α β : Type} (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :=
  simulateQ (Wots.refImpl answers)
    (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run RefCharged
      (experimentR answers published program finish) budget))

attribute [local irreducible] experimentC experimentR referenceRun

theorem funded_experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) (credit : Nat) :
    Funded (experimentC hU ω published program finish) credit := by
  unfold experimentC
  apply funded_interactionC_bind
  intro result remaining
  apply WPair.Counted.funded_programC_bind
  intro value remaining
  exact funded_pure _ _

theorem dropClocks_experimentC {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    dropClocks (experimentC hU ω published program finish) = Paired.experimentW hU ω published program finish := by
  unfold experimentC Paired.experimentW
  rw [dropClocks_bind, dropClocks_interactionC]
  apply bind_congr
  intro interaction
  rw [dropClocks_bind, WPair.Counted.dropClocks_programC]
  rfl

theorem experimentC_transport (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :
    observed hidden (SphincsSecurity.QueryCap.run charged
      (experimentC hU ω published program finish >>= fun result => pure result.1) budget) =
    refObserved (wA hU ω hidden) (SphincsSecurity.QueryCap.run RefCharged
      (experimentR (wA hU ω hidden) published program finish) budget) := by
  unfold experimentC experimentR
  simp only [bind_assoc, pure_bind]
  refine interactionC_transport hU ω hidden published program
    (fun interaction => WPair.Counted.programC hU ω (finish interaction) >>= fun checked => pure checked.1)
    (fun interaction => simulateQ Wots.verdictImpl (finish interaction)) ?_ budget
  intro interaction remaining
  have ht := WPair.Counted.programC_transport hU ω hidden (finish interaction)
    (fun value => pure value) (fun value => pure value) (fun value remaining => rfl) remaining
  simpa only [bind_pure] using ht

theorem public_transport (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount hidden)
      (cappedProgram (experimentC hU ω published program finish) budget) =
    (fun result => refPublicInputs result.2) <$>
      referenceRun (wA hU ω hidden) published program finish budget := by
  have ht := congrArg (Functor.map Prod.snd)
    (experimentC_transport hU ω hidden published program finish budget)
  rw [bind_pure_comp, run_map_result, observed_map] at ht
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedProgram,
    referenceRun] using ht

theorem completed_tracks (hidden : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β)
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (budget remaining : Nat)
    (value : β × QueryLog Paired.Requests × List Wots.Entry) (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedProgram (experimentC hU ω published program finish) budget)
      countInit ((some (value, remaining), queries), final) ≠ 0) :
    Paired.Tracks hU ω hidden init final value.2.1 value.2.2 := by
  apply Paired.experimentW_tracks hU ω hidden published program finish hfinish init (value, final)
  exact fixedRun_recorded_cap_erasure hidden _ _ (dropClocks_experimentC hU ω published program finish)
    budget remaining value queries countInit final hr

theorem event_le_external {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β)
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (budget : Nat) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → (Option ((β × QueryLog Paired.Requests × List Wots.Entry) × Nat) × List CountSpec.Domain) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      ∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit)
        (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal) := by
  apply (WPair.Counted.Generic.counted_program_event_le_world _ event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (WPair.Counted.Generic.first_probe_le_external _
      (funded_experimentC hU ω published program finish 0) budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, cell, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  have ht := completed_tracks hU ω hidden published program finish hfinish budget remaining output queries final hr
  refine ⟨Paired.tracked_noBad hU ω hidden final _ _ ht hno, ?_,
    Paired.tracked_guessed hU ω hidden final _ _ ht cell hg⟩
  apply WPair.Counted.Generic.capped_probes_le_budget _ budget
    (funded_experimentC hU ω published program finish 0)
    (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) _
  rwa [withRun_fixedSampler]
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
variable {α β : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
  (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat)

abbrev RunResult := Option ((β × QueryLog Paired.Requests × List Wots.Entry) × Nat) × List CountSpec.Domain

 theorem public_distribution :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedProgram (experimentC hU ω published program finish) budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← referenceRun (wA hU ω hidden) published program finish budget
      pure (refPublicInputs result.2)] := by
  rw [WPair.Counted.Generic.public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using public_transport hU ω hidden published program finish budget

 theorem public_payment_le_reference :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := β) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω published program finish budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other (wA hU ω hidden) _ (Wots.traceOf (wA hU ω hidden) run.2)

 theorem event_le_other
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := β) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) :=
  (event_le_external hU ω published program finish hfinish budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference hU ω published program finish budget))
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open ENNReal
set_option maxHeartbeats 1000000

theorem hazard_normalized {n q : Nat} (hq : q<n) {event charge : ENNReal}
    (hc : charge≠⊤) (he : event≤((n-q:Nat):ENNReal)⁻¹*charge) :
    (1-(q:ℝ)/(n:ℝ))*event.toReal≤charge.toReal/(n:ℝ) := by
  have hsub : 0<n-q := Nat.sub_pos_of_lt hq
  have hdn : ((n-q:Nat):ENNReal)≠0 := by exact_mod_cast Nat.ne_of_gt hsub
  have hfin : ((n-q:Nat):ENNReal)⁻¹*charge≠⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hdn) hc
  have hr := ENNReal.toReal_mono hfin he
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Nat.cast_sub (Nat.le_of_lt hq)] at hr
  have hnr : (0:ℝ)<n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le q) hq)
  have hqr : (q:ℝ)<n := by exact_mod_cast hq
  have hh : event.toReal≤charge.toReal/((n:ℝ)-q) := by
    simpa only [div_eq_mul_inv,mul_comm] using hr
  have hp := (le_div_iff₀ (by linarith : (0:ℝ)<n-q)).mp hh
  apply (le_div_iff₀ hnr).mpr
  calc
    ((1-(q:ℝ)/(n:ℝ))*event.toReal)*(n:ℝ) = event.toReal*((n:ℝ)-q) := by field_simp
    _ ≤ charge.toReal := hp
#print axioms hazard_normalized
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG RowsFrame
 runWith_bind' runWith_pure' expectedValue_liftM_pmf expectedValue_uniformOfFintype Extends search_replays_gen
 SuperProg superProg_pure superProg_bind spmf_ev_mono spmf_ev_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def Replays (S : FtsBankSpec P) (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) cache'), r' = (found, cache')
theorem Replays.mono {S : FtsBankSpec P} {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : (Replays S) rows rho m found) (hext : Extends rows rows') : (Replays S) rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (S : FtsBankSpec P) (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) rows)) :
    Extends rows r.2 ∧ (Replays S) r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) S.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (S : FtsBankSpec P) (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, (Replays S) M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty (S : FtsBankSpec P) : (InvM S) (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (S : FtsBankSpec P) (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  NearMemory.nearMemPotential S q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (S : FtsBankSpec P) (q : Nat) (s : GState) : ENNReal := if (InvM S) s.memory then (ghostPot S) q s.memory else ⊤
theorem ΦI_initial (S : FtsBankSpec P) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price ≤ rate) (q : Nat) :
    (ΦI S) q initG ≤ (q:ENNReal)*(rate+S.admBound)/2^128 := by
  unfold ΦI
  rw [if_pos (show (InvM S) initG.memory from (invM_empty S))]
  exact NearMemory.mem_initial S rate hrate q
theorem superProg_of_memory (S : FtsBankSpec P) {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith ((implG S) slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg ((implG S) slot) ((ΦI S) q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (S : FtsBankSpec P) (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := (aux_nonzero S) slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory (S : FtsBankSpec P) (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · change ((fun hit => (hit, SecretGuessObservation.afterTrial ((envG S) WPair.envL) s c v hit)) <$>
      SecretGuessObservation.forcedTrialWith samplerG slot s c v) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · change ((fun value => (value, SecretGuessObservation.afterDisclosure ((envG S) WPair.envL) s c value)) <$>
      samplerG.discloseLaw s c) r ≠ 0 at hr
    simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (S : FtsBankSpec P) (slot q n : Nat) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.coinReqL n) :=
  (superProg_of_memory S) slot q _ fun s r hr => (coin_memory S) slot n s r hr
theorem guess_ΦI (S : FtsBankSpec P) (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  (superProg_of_memory S) slot q _ fun s r hr => (secret_memory S) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (S : FtsBankSpec P) (slot q : Nat) (c : Guess.GCoord) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  (superProg_of_memory S) slot q _ fun s r hr => (secret_memory S) slot (.inr c) s r hr
theorem mapM_ΦI (S : FtsBankSpec P) {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg ((implG S) slot) ((ΦI S) q) (f a)) :
    ∀ l : List α, SuperProg ((implG S) slot) ((ΦI S) q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ ((mapM_ΦI S) slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (S : FtsBankSpec P) (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  (mapM_ΦI S) slot q _ (fun c => (disclose_ΦI S) slot q c) cs
theorem probeW_ΦI (S : FtsBankSpec P) (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 4 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 4) (v : Digest) :
    SuperProg ((implG S) slot) ((ΦI S) q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ ((guess_ΦI S) slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ ((disclose_ΦI S) slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem ev_single_aux (S : FtsBankSpec P) (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, (ghostStep S) s.memory.1 i r.1 s.memory.2) })) := by
  have h := (ev_aux_bind S) slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (S : FtsBankSpec P) (slot q : Nat) (x : HashInput) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : (InvM S) s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [(ev_single_aux S)]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq S]
        have hpt : ∀ a : HashOutput, (ΦI S) q { s with memory := (s.memory.1.readRow x a true,
            (ghostStep S) s.memory.1 (.birth x) a s.memory.2) } =
            NearMemory.nearMemPotential S q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : (InvM S) (s.memory.1.readRow x a true, (ghostStep S) s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact NearMemory.mem_birth S q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI (S : FtsBankSpec P) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : ClaudeWCT.W9.CanonTable.Omega U)
    (x : HashInput) : SuperProg ((implG S) slot) ((ΦI S) q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact (probeW_ΦI S) slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact (birth_ΦI S) slot q x
      · exact superProg_pure _ _ _
#print axioms ΦI_initial
#print axioms birth_ΦI
#print axioms hashL_ΦI
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG RowsFrame
 runWith_bind' runWith_pure' Extends SuperProg spmf_ev_mono spmf_ev_le spmf_ev_zero pc_ev_offsupport ev_uniform_digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
theorem search_support (S : FtsBankSpec P) (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith ((implG S) slot) ((searchL S) rho m 0 (2^21)) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈
      support (Sampling.roRun 0 (S.search rho m 0 (2^21)) s.memory.1.rows) := by
  have hlaw := (search_law S) slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (S.search rho m 0 (2^21)) s.memory.1.rows)
    then 0 else 1) (2^21) 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0
theorem ev_nonce_cached (S : FtsBankSpec P) {β : Type} (slot : Nat) (m : Message) (rho : Digest)
    (k : Digest → OracleComp WPair.WSpecL β) (s : GState) (hn : s.memory.1.nonces m = some rho)
    (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith ((implG S) slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, (ghostStep S) s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold WPair.nonceReq
  rw [(ev_aux_bind S)]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]
theorem ev_nonce_fresh (S : FtsBankSpec P) {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp WPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith ((implG S) slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, (ghostStep S) s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold WPair.nonceReq
  rw [(ev_aux_bind S)]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]
theorem ev_expose_finish_le (S : FtsBankSpec P) {β : Type} (slot q : Nat)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β)
    (hfinish : ∀ rho found, SuperProg ((implG S) slot) ((ΦI S) q) (finish rho found))
    (rho : Digest) (found : Option (BitVec 32 × HashOutput)) (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith ((implG S) slot)
      (WPair.exposeReq (found.map Prod.snd) >>= fun _ => finish rho found) s2)
      (fun r => (ΦI S) q r.2) ≤
    (ΦI S) q ⟨s2.allowed,s2.retired,s2.guesses,s2.probes,(s2.memory.1.expose (found.map Prod.snd),
      (ghostStep S) s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold WPair.exposeReq
  rw [(ev_aux_bind S)]
  change expectedValue (pure ((),s2.memory.1.expose (found.map Prod.snd)):PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact hfinish rho found _

noncomputable def searchWithNonce (S : FtsBankSpec P) {β : Type} (m : Message)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β) :
    OracleComp WPair.WSpecL β := do
  let rho ← WPair.nonceReq m
  let found ← (searchL S) rho m 0 (2^21)
  let _ ← WPair.exposeReq (found.map Prod.snd)
  finish rho found

theorem searchWithNonce_ΦI (S : FtsBankSpec P) {β : Type} (slot q : Nat) (m : Message)
    (finish : Digest → Option (BitVec 32 × HashOutput) → OracleComp WPair.WSpecL β)
    (hfinish : ∀ rho found,SuperProg ((implG S) slot) ((ΦI S) q) (finish rho found)) :
    SuperProg ((implG S) slot) ((ΦI S) q) ((searchWithNonce S) m finish) := by
  unfold searchWithNonce
  intro s
  by_cases hinv : (InvM S) s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI S q s = ghostPot S q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      rw [(ev_nonce_cached S) slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine ((ev_expose_finish_le S) slot q finish hfinish rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := (search_support S) slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := (search_frame S) slot rho m (2^21) 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : (InvM S) (r.2.memory.1.expose (r.1.map Prod.snd),
          (ghostStep S) r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      rw [(ev_nonce_fresh S) slot m _ s hn, hΦs]
      refine le_trans ?_ (NearMemory.mem_sign_fresh S q _ _ _ _ _ m hn 0 (2^21) (by decide))
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        (ghostStep S) s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ ((search_law S) slot v m (fun found rows' =>
        NearMemory.nearMemPotential S q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) (2^21) 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine ((ev_expose_finish_le S) slot q finish hfinish v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := (search_support S) slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := (replays_of_search S) v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := (search_frame S) slot v m (2^21) 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (S.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : (InvM S) (r.2.memory.1.expose (r.1.map Prod.snd),
          (ghostStep S) r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, LazyMem.expose]
      rw [hbir1, hnon1]
#print axioms searchWithNonce_ΦI
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (NearGhost projS GState samplerG initG SuperProg)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def nearPayoff (q : Nat) (s : WPair.WStateL) : ENNReal :=
  if s.memory.births.length≤q ∧ s.memory.exposures.length≤2^32 ∧
      ∃ N∈s.memory.births,S.admissible N=true ∧ S.covered s.memory.exposures N then 1 else 0

theorem payoff_le_ΦI
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (q : Nat) (s : GState) : nearPayoff S q (projS s)≤ΦI S q s := by
  unfold ΦI
  split_ifs with hinv
  · unfold nearPayoff
    split_ifs with hp
    · obtain ⟨hb,hl,N,hN,hadm,hcov⟩:=hp
      exact NearMemory.mem_win S q _ _ _ _ _ hb (hinv.2.1.trans hl)
        (Or.inr ⟨N,hN,hadm,hmono _ _ _ hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top

theorem forced_payoff_le {β : Type}
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (hW : SuperProg (implG S slot) (ΦI S q) W) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL)
      (fun r => nearPayoff S q r.2)≤(q:ENNReal)*(rate+S.admBound)/2^128 := by
  change expectedValue (SecretGuessObservation.runWith
    (SecretGuessObservation.forcedWithImpl WPair.envL WPair.samplerL slot) W (projS initG)) _≤_
  rw [expectedValue_project S WPair.envL slot W initG]
  exact (expectedValue_mono _ fun (r : β × GState) => payoff_le_ΦI S hmono q r.2).trans
    ((hW initG).trans (ΦI_initial S rate hrate q))

#print axioms forced_payoff_le
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security.CaseC (SuperProg superProg_pure superProg_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P]
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem nearSearch_eq (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) (rho : Digest) (m : Message) (counter fuel : Nat) :
    NearWorld.searchL S rho m counter fuel=WPair.Paired.searchL rho m counter fuel := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
      simp only [NearWorld.searchL,WPair.Paired.searchL,hproducer]
      apply bind_congr
      intro output
      split <;> first | rfl | exact ih _

section World
variable {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
variable (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat)

theorem finishL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (request : Request) (rho : Digest) (found : Option (BitVec 32×HashOutput)) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.finishL hU omega request rho found) := by
  rcases found with _ | ⟨c,output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.Paired.finishL]
    generalize WPair.Paired.signerLayersW hU omega request output=g
    cases g with
    | none => exact superProg_pure _ _ _
    | some layers =>
        exact superProg_bind _ _ (NearWorld.discloseAll_ΦI S slot q _) fun _ => superProg_pure _ _ _

theorem signL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.signL hU omega published request) := by
  have h:=NearWorld.searchWithNonce_ΦI S slot q request.message
    (WPair.Paired.finishL hU omega request) (finishL_ΦI S hproducer hU omega slot q request)
  unfold NearWorld.searchWithNonce at h
  simp_rw [nearSearch_eq S hproducer] at h
  unfold WPair.Paired.signL
  split
  · exact h
  · exact superProg_pure _ _ _

theorem interactionL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp WPair.Paired.Interaction α) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.interactionL hU omega published program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact superProg_pure _ _ _
  | query_bind input next ih =>
      rcases input with (n|x)|request
      · change SuperProg _ _ (WPair.coinReqL n >>= fun coin => _)
        exact superProg_bind _ _ (NearWorld.coin_ΦI S slot q n) ih
      · change SuperProg _ _ (WPair.hashL hU omega x >>= fun answer => _)
        exact superProg_bind _ _ (NearWorld.hashL_ΦI S hU slot q omega x) fun a =>
          superProg_bind _ _ (ih a) fun _ => superProg_pure _ _ _
      · change SuperProg _ _ (WPair.Paired.signL hU omega published request >>= fun signature => _)
        exact superProg_bind _ _ (signL_ΦI S hproducer hU omega slot q published request) fun a =>
          superProg_bind _ _ (ih a) fun _ => superProg_pure _ _ _

theorem experimentL_ΦI (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat) {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    SuperProg (NearWorld.implG S slot) (NearWorld.ΦI S q)
      (WPair.Paired.experimentL hU omega published program finish) := by
  unfold WPair.Paired.experimentL
  exact superProg_bind _ _ (interactionL_ΦI S hproducer hU omega slot q published program) fun _ =>
    superProg_bind _ _ (CaseC.programL_super hU _ _ omega
      (NearWorld.coin_ΦI S slot q) (NearWorld.hashL_ΦI S hU slot q omega) _) fun _ =>
        superProg_pure _ _ _

theorem forced_experiment_near_le (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted) {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (slot q : Nat)
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot
      (WPair.Paired.experimentL hU omega published program finish) WPair.initL)
      (fun r=>NearWorld.nearPayoff S q r.2)≤(q:ENNReal)*(rate+S.admBound)/2^128 :=
  NearWorld.forced_payoff_le S hmono rate hrate slot q _
    (experimentL_ΦI S hproducer hU omega slot q published program finish)
end World
#print axioms forced_experiment_near_le
end ClaudeWCT.Bank.NearWorld.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nearCovered_mono (X Y : List HashOutput) (N : HashOutput)
    (hsub : ∀ v∈X,v∈Y) (h : NearCovered X N) : NearCovered Y N := by
  obtain ⟨hole,h⟩:=h
  refine ⟨hole,(nearCoveredAtP_source Y N hole).mpr ?_⟩
  intro k t hne
  obtain ⟨output,ho,hrest⟩:=(nearCoveredAtP_source X N hole).mp h k t hne
  exact ⟨output,hsub output ho,hrest⟩

theorem nearLawSpec_producer : nearLawSpec.producer=SigGolfCandidate.Research.SharedForest.digestAccepted := by
  change producer = _
  exact funext producer_source

theorem nearLawSpec_mean : ClaudeWCT.Numerics.Law.lawAvg nearLawSpec.law (2^32) nearLawSpec.price≤350 :=
  law_nearPrice_mean_bound

theorem forced_near_payoff_le {β : Type} (slot q : Nat)
    (W : OracleComp WPair.WSpecL β)
    (hW : CaseC.SuperProg (NearWorld.implG nearLawSpec slot) (NearWorld.ΦI nearLawSpec q) W) :
    expectedValue (SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL)
      (fun r => NearWorld.nearPayoff nearLawSpec q r.2)≤
      (q:ENNReal)*(350+1/1024)/2^128 :=
  NearWorld.forced_payoff_le nearLawSpec nearCovered_mono 350 nearLawSpec_mean slot q W hW

#print axioms forced_near_payoff_le
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem slotCovered_bank (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔ ClaudeWCT.Bank.Paired.SlotCoveredP (X.map ClaudeWCT.Bank.Paired.proposal) N k t :=
  (ClaudeWCT.Bank.Paired.slotCoveredP_source X N k t).symm

theorem covered_bank (X : List HashOutput) (N : HashOutput) :
    (∀ k t,SlotCovered X N k t)↔ClaudeWCT.Bank.Paired.Covered X N := by
  unfold ClaudeWCT.Bank.Paired.Covered ClaudeWCT.Bank.Paired.CoveredP
  exact forall_congr' fun k=>forall_congr' fun t=>slotCovered_bank X N k t

theorem nearCovered_bank (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6)
    (h : ∀ k' t',(k',t')≠(k,t)→SlotCovered X N k' t') : ClaudeWCT.Bank.Paired.NearCovered X N := by
  refine ⟨(k,t),fun k' t' hne=>(slotCovered_bank X N k' t').mp (h k' t' hne)⟩

#print axioms slotCovered_bank
#print axioms covered_bank
#print axioms nearCovered_bank
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.Bank.NearWorld
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3.Security.CaseC (SuperProg)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)

def NearEvent {β : Type} (q : Nat) (r : β×WPair.WStateL) : Prop :=
  r.2.guesses.Nonempty ∧ r.2.probes+r.2.memory.births.length≤q ∧ ¬Guess.Fam.Bad r.2 ∧
    r.2.memory.exposures.length≤2^32 ∧
    ∃ N∈r.2.memory.births,S.admissible N=true ∧ S.covered r.2.memory.exposures N

theorem event_payoff {β : Type} (q : Nat) (r : β×WPair.WStateL) (h : NearEvent S q r)
    (slot : Nat) (hs : slot<r.2.probes) : 1≤nearPayoff S (q-(slot+1)) r.2 := by
  unfold nearPayoff
  rw [if_pos ⟨by have hb:=h.2.1;omega,h.2.2.2⟩]

theorem triangular_sum_twice (q : Nat) :
    ((Finset.range q).sum (fun i => q - (i + 1)))*2=q*(q-1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
      change (((Finset.range q).sum (fun i => q - (i + 1))) + q) * 2 = (q+1)*q
      by_cases hq:q=0
      · subst hq;simp
      · have :q-1+1=q:=by omega
        nlinarith

theorem triangular_sum_ennreal (q : Nat) (c : ENNReal) :
    (∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*c/2^128)=
      ((q*(q-1):Nat):ENNReal)*c/(2*2^128) := by
  have h : (((Finset.range q).sum (fun i => q - (i + 1)) : Nat):ENNReal)*2=
      ((q*(q-1):Nat):ENNReal) := by exact_mod_cast triangular_sum_twice q
  rw [←h]
  simp only [Nat.cast_sum,div_eq_mul_inv,←Finset.sum_mul]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  rw [show (∑ x∈Finset.range q,((q-(x+1):Nat):ENNReal))*2*c*((2:ENNReal)⁻¹*(2^128:ENNReal)⁻¹)=
      (∑ x∈Finset.range q,((q-(x+1):Nat):ENNReal))*c*(2*(2:ENNReal)⁻¹)*(2^128:ENNReal)⁻¹ by ring]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

theorem near_event_lazy_bound {β : Type}
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (q : Nat) (W : OracleComp WPair.WSpecL β)
    (hW : ∀ slot budget,SuperProg (implG S slot) (ΦI S budget) W) :
    Pr[NearEvent S q | SecretGuessObservation.withRun WPair.envL WPair.samplerL W WPair.initL]≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  have hb:=Guess.Fam.fam_event_le_forced_slot WPair.envL W LazyMem.empty q (NearEvent S q)
    (fun slot r=>nearPayoff S (q-(slot+1)) r.2) (fun r _ h=>
      ⟨h.1,by have hc:=h.2.1;omega,h.2.2.1,event_payoff S q r h⟩)
  have hslot (slot : Nat) :
      (∑' r,Pr[=r|SecretGuessObservation.forcedWithRun WPair.envL WPair.samplerL slot W WPair.initL]*
        nearPayoff S (q-(slot+1)) r.2)≤((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 := by
    exact forced_payoff_le S hmono rate hrate slot (q-(slot+1)) W (hW slot _)
  calc
    _≤_:=hb
    _≤((2^128-q:Nat):ENNReal)⁻¹*
        ∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _=>hslot slot)
    _=_:=by rw [triangular_sum_ennreal];simp only [div_eq_mul_inv];ring

#print axioms near_event_lazy_bound
end ClaudeWCT.Bank.NearWorld

namespace ClaudeWCT.Bank.NearWorld.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
open ClaudeWCT.W9.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {P : Type} [Fintype P] [SampleableType P]

theorem experiment_near_bound (S : FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hmono : ∀ X Y N,(∀ v∈X,v∈Y)→S.covered X N→S.covered Y N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    {U : Finset HashInput} (hU : ClaudeWCT.W9.T3.Security.CanonGraph.canonInputs⊆U)
    (omega : ClaudeWCT.W9.CanonTable.Omega U) (q : Nat)
    {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp WPair.Paired.Interaction α)
    (finish : (α × QueryLog WPair.Paired.Requests)→M β) :
    Pr[NearWorld.NearEvent S q | SecretGuessObservation.withRun WPair.envL WPair.samplerL
      (WPair.Paired.experimentL hU omega published program finish) WPair.initL]≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) :=
  NearWorld.near_event_lazy_bound S hmono rate hrate q _
    (fun slot budget=>experimentL_ΦI S hproducer hU omega slot budget published program finish)

#print axioms experiment_near_bound
end ClaudeWCT.Bank.NearWorld.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem experimentL_near_facts (admissible : HashOutput → Bool)
    (covered : List HashOutput → HashOutput → Prop)
    (hmono : ∀ X Y N, (∀ v ∈ X, v ∈ Y) → covered X N → covered Y N)
    (q : Nat) (g : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Interaction α)
    (finish : (α × QueryLog Requests) → M β) (hfinish : ∀ result, PublicVerdict.Only (finish result))
    (r : (β × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL r ≠ 0)
    (hq : r.1.2.2.length ≤ q) (hlog : r.1.2.1.length ≤ 2^32)
    (hno : ¬OverflowIn (wA hU omega g) r.1.2.1)
    (cell : Guess.GCoord) (hguess : GuessedIn (wA hU omega g) r.1.2.1 r.1.2.2 cell)
    (input : HashInput) (output : HashOutput) (hentry : (input,output) ∈ r.1.2.2)
    (hdigest : input ∈ BPair.digestInputs)
    (hfresh : ∀ entry ∈ r.1.2.1, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      SigGolfCandidate.T3M.SecurityExtraction.queried (wA hU omega g) (authenticatedSign published entry.1))
    (hadm : admissible output = true)
    (hcovered : covered (loggedOutputs (wA hU omega g) r.1.2.1) output) :
    r.2.guesses.Nonempty ∧ r.2.probes + r.2.memory.births.length ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧
      r.2.memory.exposures.length ≤ 2^32 ∧
      ∃ output ∈ r.2.memory.births, admissible output = true ∧ covered r.2.memory.exposures output := by
  have hcounts := experimentL_counts hU omega g published program finish r hr
  have hghost := experimentL_ghosts hU omega g published program finish r hr
  have hbirth : output ∈ r.2.memory.births := by
    rcases experimentL_rows_birth_or_trials hU omega g published program finish r hr input output hentry hdigest with hb | ht
    · exact hb
    · obtain ⟨entry, he, hquery⟩ := hcounts.2.1 input ht
      exact False.elim (hfresh entry he hquery)
  refine ⟨experimentL_guesses_nonempty hU omega g published program finish hfinish r hr cell hguess,
    (experimentL_probes_births hU omega g published program finish r hr).trans hq,
    experimentL_noBad hU omega g published program finish hfinish r hr hno,
    hcounts.2.2.trans hlog, output, hbirth, hadm, hmono _ _ output ?_ hcovered⟩
  intro value hv
  obtain ⟨entry, he, signature, hs, hout⟩ := mem_loggedOutputs.mp hv
  exact hghost.1 entry he signature value hs hout

#print axioms experimentL_near_facts
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem sharedDigestSearch_queried (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (q : SigGolfCandidate.T3.Spec.Domain),
      q ∈ queried answers (sharedDigestSearch rho m start fuel) →
      ∃ c, q = .inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) := by
  intro fuel
  induction fuel with
  | zero => intro start q hq; simp [sharedDigestSearch] at hq
  | succ fuel ih =>
      intro start q hq
      rw [sharedDigestSearch, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact ⟨start, List.mem_singleton.mp hq⟩
      · split at hq
        · simp at hq
        · exact ih (start+1) q hq

theorem signer_digest_query (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (rho : Digest) (m : Message) (ctr : BitVec 32)
    (hq : (.inl (.inr (pad64 (digestInput rho m ctr))) : SigGolfCandidate.T3.Spec.Domain) ∈
      queried answers (authenticatedSign published request)) :
    request.cache = published ∧ request.message = m ∧
      rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (.inl (.inr (pad64 (digestInput rho m ctr))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried answers (sharedDigestSearch rho m 0 ClaudeWCT.WCT9.digestAttemptLimit) := by
  unfold authenticatedSign at hq
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  by_cases hc : request.cache = published
  swap
  · rw [if_neg hc] at hq; simp at hq
  rw [if_pos hc, ClaudeWCT.Bank.Paired.signPayload_factor, queried_bind,
    SigGolfCandidate.T3.Security.BPB.queried_privateNonce] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  rw [queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨c, heq⟩ := sharedDigestSearch_queried answers _ _ ClaudeWCT.WCT9.digestAttemptLimit 0 _ hq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    obtain ⟨hrho, hctr, hm⟩ := SigGolfCandidate.T3.Security.BPB.digestInput_injective heq
    subst hrho hm
    exact ⟨hc, rfl, rfl, hq⟩
  · exfalso
    generalize evalWithAnswerFn answers (sharedDigestSearch
      (evalWithAnswerFn answers (privateNonce request.message)) request.message
      0 ClaudeWCT.WCT9.digestAttemptLimit) = found at hq
    rcases found with _ | ⟨_, output⟩
    · simp at hq
    · have hnot := SigGolfCandidate.T3.Security.BPB.allQ_queried answers _ _
        (ClaudeWCT.Bank.Paired.payNotDigest request.cache
          (evalWithAnswerFn answers (privateNonce request.message)) output) _ hq
      exact hnot (SigGolfCandidate.T3.Security.BPB.hdrMarker_digestInput rho m ctr)

#print axioms sharedDigestSearch_queried
#print axioms signer_digest_query
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

def SignedDigest (log : QueryLog Paired.Requests) (message : Message) (rho : Digest) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧ signature.rho = rho

theorem fresh_digest_not_signer_eval (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Paired.Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (authenticatedSign published entry.1))
    (message : Message) (rho : Digest) (counter : BitVec 32)
    (hcomp : ∀ m, ∃ signature,
      evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload published m) = some signature)
    (hfresh : ¬SignedDigest log message rho) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput rho message counter))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried answers (authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨signature, hsignature⟩ := hcomp message
  have hsrho := payload_rho answers published message signature hsignature
  rw [hm] at hrho
  apply hfresh
  refine ⟨entry, he, hm, signature, ?_, hsrho.trans hrho.symm⟩
  rw [hsig entry he, eval_authenticatedSign, if_pos hc, hc, hm]
  exact hsignature

#print axioms payload_rho
#print axioms eval_authenticatedSign
#print axioms fresh_digest_not_signer_eval
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
theorem probeInput_other_new (T : Answers) (a : Guess.ChainAddr) (step : Fin 4) (value : Digest) :
    Wots.PairedReference.OtherInput T (Guess.probeInput a step value) := by
  let pos : Extract.Pos := .wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val step.val
  have hb : pos.Bounded := ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
  -- #866: `posOf_eq` also takes the input length (a chain row is 64 bytes, `Pos.len` of a chain position).
  refine ⟨pos, Extract.posOf_eq hb (Guess.probeInput_length a step value) ?_, hb, ?_, trivial⟩
  · exact Guess.hdrBlock_wctChainInput _ _ _ _ _ _
  · exact ⟨a.1.isLt, a.2.1.isLt, a.2.2.1.isLt, a.2.2.2.isLt, step.isLt⟩
theorem decodeProbe_other_new (T : Answers) {x : HashInput} {probe : Guess.GCoord × Digest}
    (h : Guess.decodeProbe x = some probe) : Wots.PairedReference.OtherInput T x := by
  rw [Guess.eq_of_decodeProbe h]
  exact probeInput_other_new T _ _ _

theorem probeCount_le_other_new (T : Answers) (pk : Digest) (trace : List Wots.Entry) :
    probeCount (trace.map Prod.fst) ≤ Wots.PairedReference.otherCount ⟨T, pk, trace⟩ := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      obtain ⟨x, a⟩ := entry
      cases hd : Guess.decodeProbe x with
      | none =>
          by_cases ho : Wots.PairedReference.OtherQuery T (.inl (.inr x))
          · have h : probeCount (trace.map Prod.fst) ≤ 1 + Wots.PairedReference.otherCount ⟨T, pk, trace⟩ := by omega
            simpa [probeCount, Wots.PairedReference.otherCount, hd, ho, Nat.add_comm] using h
          · simpa [probeCount, Wots.PairedReference.otherCount, hd, ho] using ih
      | some probe =>
          have ho : Wots.PairedReference.OtherQuery T (.inl (.inr x)) := decodeProbe_other_new T hd
          simpa [probeCount, Wots.PairedReference.otherCount, hd, ho] using Nat.add_le_add_left ih 1

#print axioms probeCount_le_other_new
end ClaudeWCT.W9.T3.Security.WPair.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
variable {α β : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
  (finish : (α × QueryLog Paired.Requests) → M β) (budget : Nat)

 theorem public_payment_le_reference_new :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := β)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedProgram (experimentC hU ω published program finish) budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.PairedReference.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := β) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), public_distribution hU ω published program finish budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU ω hidden)]
  exact_mod_cast probeCount_le_other_new (wA hU ω hidden) _ (Wots.traceOf (wA hU ω hidden) run.2)

 theorem event_le_other_new
    (hfinish : ∀ value, PublicVerdict.Only (finish value)) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := β) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU ω hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU ω hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedProgram (experimentC hU ω published program finish) budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | referenceRun (wA hU ω hidden) published program finish budget] *
        (Wots.PairedReference.otherCount ⟨wA hU ω hidden, (evalWithAnswerFn (wA hU ω hidden) keygen).1,
          Wots.traceOf (wA hU ω hidden) run.2⟩ : ENNReal)) :=
  (event_le_external hU ω published program finish hfinish budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (public_payment_le_reference_new hU ω published program finish budget))

#print axioms event_le_other_new
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted


namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def worldGameL {U : Finset HashInput} (hU : CanonGraph.canonInputs⊆U)
    (omega : CanonTable.Omega U) (adversary : AdversaryP) :=
  let generated := evalWithAnswerFn (wA hU omega 0) SigGolfCandidate.T3.keygen
  experimentL hU omega generated.2 (adversary generated.1 generated.2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1)

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs⊆U) (omega : CanonTable.Omega U)

theorem worldGameL_sameRest {omega1 omega2 : CanonTable.Omega U}
    (h : SameRest omega1 omega2) (adversary : AdversaryP) :
    worldGameL hU omega1 adversary=worldGameL hU omega2 adversary := by
  unfold worldGameL
  rw [eval_sameRest hU h _ BPair.keygen_dn]
  exact experimentL_sameRest hU h _ _ _

theorem fixed_experimentL {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Interaction α) (finish : (α × QueryLog Requests)→M β)
    (hfinish : ∀ value,PublicVerdict.Only (finish value)) (g : CanonTable.HiddenF) :
    Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL =
      𝒮[experimentT (wA hU omega g) published program finish] := by
  have h := congrArg (Functor.map Prod.fst)
    (fixed_inline (digestOf omega) (nonceOf omega) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL (BPair.consistent_empty _ _))
  rw [Functor.map_map,forget_initL] at h
  change (Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (experimentL hU omega published program finish) initL) =
    Prod.fst <$> fixedRun env (Guess.Fam.phi g.1 g.2)
      (simulateQ (inlineAux omega) (experimentL hU omega published program finish)) init at h
  rw [inline_experimentL hU omega] at h
  exact h.trans (fixed_experimentW hU omega published program finish hfinish g)

theorem fixed_worldGameL (g : CanonTable.HiddenF) (adversary : AdversaryP) :
    Prod.fst <$> fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL = 𝒮[pairRun (wA hU omega g) adversary] := by
  rw [pairRun_world]
  exact fixed_experimentL hU omega _ _ _ (PairedOuter.PaddedGame.verdict_public _) g

theorem worldGameL_tracking (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL r ≠ 0) :
    r.2.probes ≤ r.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU omega g) r.1.2.1 r.1.2.2 c → Guess.PrefixIn r.2.guesses c.1 c.2.val := by
  have ht := experimentL_tracking hU omega g _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr
  refine ⟨?_,fun c hc => ?_⟩
  · have hp:=ht.probes
    simp only [init,SecretGuessObservation.initialState] at hp
    simpa only [forget,Nat.zero_add] using hp
  · exact ht.guess (by simp [init,SecretGuessObservation.initialState]) c hc.1 hc.2

theorem worldGameL_noBad (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL r ≠ 0)
    (hno : ¬OverflowIn (wA hU omega g) r.1.2.1) : ¬Guess.Fam.Bad r.2 :=
  experimentL_noBad hU omega g _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr hno

attribute [local irreducible] worldGameL experimentT experimentW experimentL SecretGuessObservation.fixedRun

theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : CanonTable.HiddenF → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ g result, fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU omega adversary) initL result ≠ 0 → event g result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU omega adversary] ≤
      Pr[wevent | withRun (envE (digestOf omega) (nonceOf omega)) samplerL
        (worldGameL hU omega adversary) initL] := by
  rw [← Guess.Fam.fam_erasure (envE (digestOf omega) (nonceOf omega)) (worldGameL hU omega adversary) initL
    (Guess.Fam.inv_initial BPair.LazyMem.empty)]
  change _ ≤ Pr[wevent | Guess.Fam.hiddenLaw (fun _ => Finset.univ) >>= fun g =>
    fixedRun (envE (digestOf omega) (nonceOf omega)) g (worldGameL hU omega adversary) initL]
  rw [WPair.hiddenLaw_univ_bind]
  unfold ftsRun tableRun
  simp only [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  simp only [probOutput_evalSPMF,probOutput_uniformSample]
  apply mul_le_mul' le_rfl
  rw [probEvent_map,← pairRun_world hU omega g adversary,←fixed_worldGameL hU omega g adversary,probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff,SPMF.probOutput_eq_apply] using hr) he

#print axioms fixed_worldGameL
#print axioms fts_event_le_worldL
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open ClaudeWCT.W9.T3.Security.CanonGraph
attribute [local instance] instSampleableTypeSecrets instSampleableTypeOtherHalves instSampleableTypeLowLabels instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 CanonTable.instSampleableTypeHidden
noncomputable def ftsPart (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ CanonTable.HiddenF : ProbComp _) >>= fun g =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (wA (canon_subset adversary) ω g, run.2.1, run.2.2)) <$>
      pairRun (wA (canon_subset adversary) ω g) adversary
theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw (Wots.PairedReference.referenceInputs adversary) >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      Pr[fun x => E (wA (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary _ E]
  rfl

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open SigGolfCandidate.T3.Security.BPair (LazyMem)
open ClaudeWCT.W9.T3.Security.CanonGraph
theorem digest_subset (adversary : AdversaryP) : BPair.digestInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
  BPair.digestInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
theorem near_chain_slot_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (hno : ∀ A log entries, P A log entries → ¬OverflowIn A log)
    (payoff : Nat → (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω g r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (wA (canon_subset adversary) ω g) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r) :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
        Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
  refine (shared_budget_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun g run => run.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω g) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ ¬Guess.Fam.Bad r.2 ∧ ∀ slot < r.2.probes, 1 ≤ payoff slot r)
      ?_).trans ?_
    · rintro g r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω g r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω g adversary r hr).1.trans hlen,
        worldGameL_noBad (canon_subset adversary) ω g adversary r hr (hno _ _ _ hP), hp⟩
    · exact Guess.Fam.fam_event_le_forced_slot (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q _ payoff (fun _ _ h => h)
  calc (∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedWithRun (envE (digestOf ω) (nonceOf ω)) samplerL slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff slot r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw (Wots.PairedReference.referenceInputs adversary)])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy (Wots.PairedReference.referenceInputs adversary) (digest_subset adversary)
          (fun omega => worldGameL (canon_subset adversary) omega adversary)
          (fun _ _ h => worldGameL_sameRest (canon_subset adversary) h adversary) slot (payoff slot))

#print axioms near_chain_slot_budget
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun withRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem interactionT_honest (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (oa : OracleComp Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he
theorem entriesOf_honest (T : Correctness.Answers) (qs : List SigGolfCandidate.T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP)
    (r : Bool × QueryLog Requests × List Wots.Entry) (hr : r ∈ support (pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (authenticatedSign
        (evalWithAnswerFn T SigGolfCandidate.T3.keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Every cache with a successful logged signature succeeds on all its logged requests. -/
def CacheCompleteLog (log : QueryLog Requests) : Prop :=
  ∀ prior∈log, (∃ signature,prior.2=some signature) →
    ∀ entry∈log,entry.1.cache=prior.1.cache → ∃ signature,entry.2=some signature

theorem logged_success_cache (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (entry : (request : Requests.Domain) × Requests.Range request)
    (hsig : entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hs : ∃ signature,entry.2=some signature) : entry.1.cache=published := by
  rw [eval_authenticatedSign] at hsig
  by_contra h
  rw [if_neg h] at hsig
  obtain ⟨signature,hs⟩:=hs
  rw [hsig] at hs
  cases hs

theorem cacheCompleteLog_of_complete (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry∈log,entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hcomp : ∀ message,∃ signature,evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload published message)=some signature) :
    CacheCompleteLog log := by
  intro prior hp hs entry he hc
  have hpc:=logged_success_cache A published prior (hsig prior hp) hs
  have hec:=hc.trans hpc
  obtain ⟨signature,hsignature⟩:=hcomp entry.1.message
  refine ⟨signature,?_⟩
  rw [hsig entry he,eval_authenticatedSign,if_pos hec,hec]
  exact hsignature

theorem fresh_digest_not_signer_eval_of_log (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry∈log,entry.2=evalWithAnswerFn A (authenticatedSign published entry.1))
    (hclosed : CacheCompleteLog log)
    (hnonempty : ∃ prior∈log,∃ signature,prior.2=some signature)
    (message : Message) (rho : Digest) (counter : BitVec 32)
    (hfresh : ¬SignedDigest log message rho) :
    ∀ entry∈log,(.inl (.inr (pad64 (digestInput rho message counter))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc,hm,hrho,_⟩:=signer_digest_query A published entry.1 _ _ _ hq
  obtain ⟨prior,hprior,priorSig,hpriorSig⟩:=hnonempty
  have hpc:=logged_success_cache A published prior (hsig prior hprior) ⟨priorSig,hpriorSig⟩
  obtain ⟨signature,hs⟩:=hclosed prior hprior ⟨priorSig,hpriorSig⟩ entry he (hc.trans hpc.symm)
  have hpayload : evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload entry.1.cache entry.1.message)=some signature := by
    rw [hsig entry he,eval_authenticatedSign,if_pos hc] at hs
    exact hs
  have hsrho:=payload_rho A entry.1.cache entry.1.message signature hpayload
  exact hfresh ⟨entry,he,hm,signature,hs,hsrho.trans hrho.symm⟩

def NearCovers (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ (k : Fin 9) (t : Fin 6),∀ k' t',(k',t')≠(k,t) → SlotCovered X N k' t'

theorem nearCovers_mono (X Y : List HashOutput) (N : HashOutput)
    (hsub : ∀ value∈X,value∈Y) (h : NearCovers X N) : NearCovers Y N := by
  obtain ⟨k,t,h⟩:=h
  refine ⟨k,t,fun k' t' hne=>?_⟩
  obtain ⟨output,ho,hrest⟩:=h k' t' hne
  exact ⟨output,hsub _ ho,hrest⟩

theorem nearCovers_success (A : Answers) (log : QueryLog Requests) (N : HashOutput)
    (h : NearCovers (loggedOutputs A log) N) : ∃ prior∈log,∃ signature,prior.2=some signature := by
  obtain ⟨k,t,h⟩:=h
  obtain ⟨t',hne⟩:=exists_ne t
  obtain ⟨output,ho,_⟩:=h k t' (fun he=>hne (congrArg Prod.snd he))
  obtain ⟨entry,he,signature,hs,_⟩:=mem_loggedOutputs.mp ho
  exact ⟨entry,he,signature,hs⟩

def NearIn (A : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  log.length≤2^32 ∧ CacheCompleteLog log ∧
  ∃ (message : Message) (rho : Digest) (counter : BitVec 32) (N : HashOutput) (cell : Guess.GCoord),
    (pad64 (digestInput rho message counter),N)∈entries ∧
    ClaudeWCT.Bank.Paired.admissible N=true ∧ ¬SignedDigest log message rho ∧
    GuessedIn A log entries cell ∧ NearCovers (loggedOutputs A log) N

theorem nearIn_short {A T : Answers} (h : Wots.Ref.ShortAgree A T)
    (log : QueryLog Requests) (entries : List Wots.Entry) (hn : NearIn A log entries) :
    NearIn T log entries := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hn
  refine ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,guessedIn_short h log entries cell hguess,?_⟩
  rw [←loggedOutputs_short h]
  exact hcover

theorem nearIn_mono (A : Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ entry∈entries,entry∈entries') (h : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=h
  exact ⟨hlen,hclosed,message,rho,counter,N,cell,hsub _ he,ha,hfresh,
    guessedIn_mono A log entries entries' hsub cell hguess,hcover⟩

#print axioms fresh_digest_not_signer_eval_of_log
#print axioms nearIn_short
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete
open SecretGuessObservation (fixedRun forcedWithRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P]

theorem fixed_support_pairRun (adversary : AdversaryP)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL (canon_subset adversary) omega adversary) initL r≠0) :
    r.1∈support (pairRun (wA (canon_subset adversary) omega g) adversary) := by
  rw [mem_support_iff,probOutput_def,←fixed_worldGameL (canon_subset adversary) omega g adversary,
    map_eq_bind_pure_comp,RetainedObservation.bind_nonzero]
  refine ⟨r,hr,?_⟩
  simp only [Function.comp_apply,ne_eq,SPMF.pure_apply_eq_zero_iff,not_not]

theorem near_event_facts (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,NearCovers X N → S.covered X N)
    (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary))
    (g : CanonTable.HiddenF) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf omega) (nonceOf omega)) (Guess.Fam.phi g.1 g.2)
      (worldGameL (canon_subset adversary) omega adversary) initL r≠0)
    (hq : r.1.2.2.length≤q)
    (hP : NearIn (wA (canon_subset adversary) omega g) r.1.2.1 r.1.2.2)
    (hno : ¬OverflowIn (wA (canon_subset adversary) omega g) r.1.2.1) :
    ClaudeWCT.Bank.NearWorld.NearEvent S q r := by
  obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hP
  have hlog:=(pairRun_honest _ adversary r.1 (fixed_support_pairRun adversary omega g r hr)).1
  rw [keygen_answers] at hlog
  have hfreshQ:=fresh_digest_not_signer_eval_of_log _ _ _ hlog hclosed
    (nearCovers_success _ _ N hcover) message rho counter hfresh
  exact experimentL_near_facts (canon_subset adversary) omega S.admissible S.covered hmono q g
    _ _ _ (PairedOuter.PaddedGame.verdict_public _) r hr hq hlen hno cell hguess
    (pad64 (digestInput rho message counter)) N he (BPair.mem_digestInputs.mpr ⟨rho,message,counter,rfl⟩) hfreshQ
    (by rw [hadmissible];exact ha) (hcovered _ _ hcover)

theorem near_bound_budget (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => z.1.2.2.base.source.1≤q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        NearIn z.2 interaction.value.2 (BPair.publicEntries checked.events) ∧
          ¬OverflowIn z.2 interaction.value.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  have hchain:=near_chain_slot_budget adversary q hq
    (fun A log entries=>NearIn A log entries ∧ ¬OverflowIn A log)
    (fun A T log entries h hp=>⟨nearIn_short h log entries hp.1,
      fun ho=>hp.2 (overflowIn_short h.symm log ho)⟩)
    (fun A log entries entries' hsub hp=>⟨nearIn_mono A log entries entries' hsub hp.1,hp.2⟩)
    (fun _ _ _ hp=>hp.2)
    (fun slot r=>ClaudeWCT.Bank.NearWorld.nearPayoff S (q-(slot+1)) r.2)
    (fun omega g r hr hlen hp=>by
      have h:=near_event_facts S hadmissible hmono hcovered adversary q omega g r hr hlen hp.1 hp.2
      exact ⟨h.1,fun slot hs=>ClaudeWCT.Bank.NearWorld.event_payoff S q r h slot hs⟩)
  have hslot (slot : Nat) :
      (∑' omega,Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
        ∑' r,Pr[=r|forcedWithRun envL samplerL slot
          (worldGameL (canon_subset adversary) omega adversary) initL] *
            ClaudeWCT.Bank.NearWorld.nearPayoff S (q-(slot+1)) r.2) ≤
      ((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 := by
    apply CaseC.omega_avg_le
    intro omega
    exact ClaudeWCT.Bank.NearWorld.Paired.forced_experiment_near_le S hproducer
      (canon_subset adversary) omega slot (q-(slot+1)) hmono rate hrate _ _ _
  calc
    _≤_:=hchain
    _≤((2^128-q:Nat):ENNReal)⁻¹ *
        ∑ slot∈Finset.range q,((q-(slot+1):Nat):ENNReal)*(rate+S.admBound)/2^128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _=>hslot slot)
    _=_:=by rw [ClaudeWCT.Bank.NearWorld.triangular_sum_ennreal];simp only [div_eq_mul_inv];ring

#print axioms near_event_facts
#print axioms near_bound_budget
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Counted.Generic
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security.Wots.Ref (probEvent_bind_mono)
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
/-- Completed capped executions retain both the return value and their whole query list. -/
theorem cap_recorded_completed_le {ι β : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec β) (budget : Nat) (event : β → List ι → Prop) :
    Pr[fun result => event result.1 result.2 ∧ SphincsSecurity.QueryCap.calls selected result.2 ≤ budget |
      simulateQ impl (SphincsSecurity.QueryCap.recorded computation)] ≤
    Pr[fun result => ∃ value remaining, result.1 = some (value,remaining) ∧ event value result.2 |
      simulateQ impl (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run selected computation budget))] := by
  induction computation using OracleComp.inductionOn generalizing budget event with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryCap.run_pure,
        simulateQ_pure, probEvent_pure]
      split_ifs with h1 h2
      · rfl
      · exact False.elim (h2 ⟨value,budget,rfl,h1.1⟩)
      · exact zero_le
      · rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            refine le_trans (le_of_eq ?_) zero_le
            rw [probEvent_eq_zero_iff]
            intro result hresult hevent
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
              mem_support_pure_iff] at hresult
            obtain ⟨answer,-,tail,-,rfl⟩ := hresult
            have h := hevent.2
            rw [SphincsSecurity.QueryCap.calls_cons,if_pos hs] at h
            omega
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
            intro answer
            simp only [bind_pure_comp,probEvent_map]
            refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer remaining
              (fun value tail => event value (input::tail)))
            intro tail _
            simp only [Function.comp_apply,SphincsSecurity.QueryCap.calls_cons,if_pos hs]
            constructor
            · rintro ⟨he,hc⟩;exact ⟨he,by omega⟩
            · rintro ⟨he,hc⟩;exact ⟨he,by omega⟩
      · rw [if_neg hs,SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure]
        apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
        intro answer
        simp only [bind_pure_comp,probEvent_map]
        refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer budget
          (fun value tail => event value (input::tail)))
        intro tail _
        simp only [Function.comp_apply,SphincsSecurity.QueryCap.calls_cons,if_neg hs,Nat.zero_add]
#print axioms cap_recorded_completed_le
end ClaudeWCT.W9.T3.Security.WPair.Counted.Generic

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 150000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem offlineInteraction_eq (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Paired.Interaction α) :
    offlineInteraction T published program = Wots.PairedReference.offlineInteraction T published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rcases input with input | request
    · rw [offlineInteraction_world, Wots.PairedReference.Ref.offlineInteraction_world]
      exact bind_congr ih
    · rw [offlineInteraction_request, Wots.PairedReference.Ref.offlineInteraction_request]
      have hs : offlineSign T published request = Wots.PairedReference.offlineSign T published request := rfl
      rw [hs]
      apply bind_congr
      intro signature
      rw [ih,bind_pure_comp]

noncomputable def worldC (adversary : AdversaryP) :
    OracleComp CountSpec (Bool × QueryLog Paired.Requests × List Wots.Entry) := do
  clocks (Wots.keygenCharge (wA hU omega 0))
  let generated := evalWithAnswerFn (wA hU omega 0) keygen
  experimentC hU omega generated.2 (adversary generated.1 generated.2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1)
noncomputable def cappedWorld (adversary : AdversaryP) (budget : Nat) :=
  cappedProgram (worldC hU omega adversary) budget
noncomputable def worldRLog (T : Answers) (adversary : AdversaryP) :
    OracleComp RefWorld (Bool × QueryLog Paired.Requests) := do
  ticks (Wots.keygenCharge T)
  let generated := evalWithAnswerFn T keygen
  let interaction ← Wots.PairedReference.offlineInteraction T generated.2
    (adversary generated.1 generated.2)
  let verdict ← simulateQ Wots.verdictImpl
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.1 interaction)
  pure (verdict, interaction.2)

attribute [local irreducible] worldC worldRLog cappedWorld experimentC

theorem worldRLog_fst (T : Answers) (adversary : AdversaryP) :
    Prod.fst <$> worldRLog T adversary = Wots.PairedReference.offlineGame T adversary := by
  simp only [worldRLog, Wots.PairedReference.offlineGame, map_bind, map_pure, bind_pure]

theorem worldC_log_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU omega adversary >>= fun result => pure (result.1, result.2.1)) budget) =
      refObserved (wA hU omega g) (SphincsSecurity.QueryCap.run RefCharged
        (worldRLog (wA hU omega g) adversary) budget) := by
  unfold worldC worldRLog experimentC
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU omega 0 g, keygen_answers hU omega g]
  split_ifs
  · rw [← offlineInteraction_eq]
    refine interactionC_transport hU omega g _ _
      (fun result => WPair.Counted.programC hU omega
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure (checked.1, result.2))
      (fun result => simulateQ Wots.verdictImpl
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure (checked, result.2)) ?_ _
    intro result remaining
    exact WPair.Counted.programC_transport hU omega g _
      (fun value => pure (value,result.2)) (fun value => pure (value,result.2))
      (fun value remaining => rfl) remaining
  · rfl

theorem worldC_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    observed g (SphincsSecurity.QueryCap.run charged
      (worldC hU omega adversary >>= fun result => pure result.1) budget) =
      refObserved (wA hU omega g) (Wots.PairedReference.referenceGame (wA hU omega g) adversary budget) := by
  unfold worldC Wots.PairedReference.referenceGame Wots.PairedReference.offlineGame experimentC
  simp only [bind_assoc, pure_bind]
  rw [observed_run_clocks_bind, refObserved_run_ticks_bind,
    keygenCharge_eq hU omega 0 g, keygen_answers hU omega g]
  split_ifs
  · rw [← offlineInteraction_eq]
    refine interactionC_transport hU omega g _ _
      (fun result => WPair.Counted.programC hU omega
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result) >>= fun checked => pure checked.1)
      (fun result => simulateQ Wots.verdictImpl
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1 result)) ?_ _
    intro result remaining
    have ht := WPair.Counted.programC_transport hU omega g
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1 result)
      (fun value => pure value) (fun value => pure value)
      (fun value remaining => rfl) remaining
    simpa only [bind_pure] using ht
  · rfl

theorem worldC_public_transport (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    (fun result => publicInputs result.2) <$> simulateQ (fixedCount g) (cappedWorld hU omega adversary budget) =
      (fun result => refPublicInputs result.2) <$> Wots.PairedReference.offlineRun (wA hU omega g) adversary budget := by
  have h := congrArg (Functor.map Prod.snd) (worldC_transport hU omega g adversary budget)
  rw [bind_pure_comp, run_map_result, observed_map] at h
  simpa only [observed_recorded, refObserved_recorded, Functor.map_map, cappedWorld, cappedProgram,
    Wots.PairedReference.offlineRun] using h

theorem funded_worldC (adversary : AdversaryP) (credit : Nat) :
    Funded (worldC hU omega adversary) credit := by
  unfold worldC
  apply funded_bind _ _ _ (funded_clocks _ _)
  intro _ remaining
  exact funded_experimentC hU omega _ _ _ remaining

theorem dropClocks_worldC (adversary : AdversaryP) :
    dropClocks (worldC hU omega adversary) =
      Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
        (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1 (evalWithAnswerFn (wA hU omega 0) keygen).2)
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
          (evalWithAnswerFn (wA hU omega 0) keygen).1) := by
  rw [worldC, dropClocks_bind, dropClocks_clocks, pure_bind, dropClocks_experimentC]

set_option backward.isDefEq.respectTransparency true in
theorem world_completed_tracks (hidden : CanonTable.HiddenF) (adversary : AdversaryP)
    (budget remaining : Nat) (value : Bool × QueryLog Paired.Requests × List Wots.Entry)
    (queries : List CountSpec.Domain) (final : CountState)
    (hr : fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
      (cappedWorld hU omega adversary budget) countInit ((some (value, remaining), queries), final) ≠ 0) :
    Paired.Tracks hU omega hidden init final value.2.1 value.2.2 := by
  have hc : cappedWorld hU omega adversary budget = cappedProgram (worldC hU omega adversary) budget := by
    unfold cappedWorld
    rfl
  have hr' := Eq.mp (congrArg (fun program => fixedRun countEnvironment (Guess.Fam.phi hidden.1 hidden.2)
    program countInit ((some (value,remaining),queries),final) ≠ 0) hc) hr
  have hs := fixedRun_recorded_cap_erasure hidden (worldC hU omega adversary)
    (Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
      (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
        (evalWithAnswerFn (wA hU omega 0) keygen).2)
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1))
    (dropClocks_worldC hU omega adversary)
    budget remaining value queries countInit final hr'
  have hi : countInit = init := rfl
  have hs' := Eq.mp (congrArg (fun state => fixedRun env (Guess.Fam.phi hidden.1 hidden.2)
    (Paired.experimentW hU omega (evalWithAnswerFn (wA hU omega 0) keygen).2
      (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
        (evalWithAnswerFn (wA hU omega 0) keygen).2)
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
        (evalWithAnswerFn (wA hU omega 0) keygen).1)) state (value,final) ≠ 0) hi) hs
  exact Paired.experimentW_tracks hU omega hidden
    (evalWithAnswerFn (wA hU omega 0) keygen).2
    (adversary (evalWithAnswerFn (wA hU omega 0) keygen).1
      (evalWithAnswerFn (wA hU omega 0) keygen).2)
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
      (evalWithAnswerFn (wA hU omega 0) keygen).1)
    (PairedOuter.PaddedGame.verdict_public _) init (value,final) hs'

theorem world_event_le_external (adversary : AdversaryP) (budget : Nat) (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := Bool) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU omega hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU omega hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedWorld hU omega adversary budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      ∑' result, Pr[= result | withRun countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU omega adversary budget) countInit] *
        (probeCount (publicInputs result.1.2) : ENNReal) := by
  unfold cappedWorld
  apply (WPair.Counted.Generic.counted_program_event_le_world (cappedProgram (worldC hU omega adversary) budget) event
    (fun result => ¬Guess.Fam.Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) ?_).trans
    (WPair.Counted.Generic.first_probe_le_external (worldC hU omega adversary)
      (funded_worldC hU omega adversary 0) budget hbudget)
  intro hidden result hr he
  obtain ⟨output, remaining, hout, hno, cell, hg⟩ := hevent hidden result.1 he
  rcases result with ⟨⟨out, queries⟩, final⟩
  dsimp only at hout
  subst out
  have ht := world_completed_tracks hU omega hidden adversary budget remaining output queries final (by simpa only [cappedWorld] using hr)
  refine ⟨Paired.tracked_noBad hU omega hidden final _ _ ht hno, ?_,
    Paired.tracked_guessed hU omega hidden final _ _ ht cell hg⟩
  apply WPair.Counted.Generic.capped_probes_le_budget (worldC hU omega adversary) budget
    (funded_worldC hU omega adversary 0) (fixedSampler (Guess.Fam.phi hidden.1 hidden.2)) _
  rwa [withRun_fixedSampler]
#print axioms worldC_log_transport
#print axioms world_event_le_external
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen worldC cappedWorld experimentC
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

def publicEntriesOf (T : Answers) (inputs : List HashInput) : List Wots.Entry :=
  inputs.map (fun x => (x,T (.inl (.inr x))))
theorem publicEntriesOf_append (T : Answers) (xs ys : List HashInput) :
    publicEntriesOf T (xs++ys)=publicEntriesOf T xs++publicEntriesOf T ys := List.map_append

theorem observed_hashC (g : CanonTable.HiddenF) (x : HashInput) :
    observed g (WPair.Counted.hashC hU omega x) = pure (wA hU omega g (.inl (.inr x)),[x]) := by
  rw [WPair.Counted.hashC, observed_bind, observed_clock, pure_bind, observed_liftW, fixed_hashW, map_pure, pure_bind]
  rfl

theorem observed_signC (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    observed g (signC hU omega published request) =
      pure (evalWithAnswerFn (wA hU omega g) (Paired.authenticatedSign published request),[]) := by
  rw [signC, observed_bind, observed_clocks, pure_bind, observed_liftW, Paired.fixed_signW, map_pure, pure_bind]
  rfl

theorem interactionC_entries (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache)
    {α : Type} (program : OracleComp Paired.Interaction α)
    (result : (α × QueryLog Paired.Requests × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (interactionC hU omega published program))) :
    result.1.2.2 = publicEntriesOf (wA hU omega g) result.2 := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [interactionC_pure,observed_pure,mem_support_pure_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rcases input with (n|x)|request
      · rw [interactionC_coin,observed_query_bind] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨coin,-,tail,ht,rfl⟩ := hr
        exact ih coin tail ht
      · rw [interactionC_public,observed_bind,observed_hashC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [publicEntriesOf,List.map_cons,List.append_nil,List.cons_append,List.nil_append]
          using congrArg (List.cons (x,wA hU omega g (.inl (.inr x)))) (ih _ tail ht)
      · rw [interactionC_request,observed_bind,observed_signC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [List.nil_append,List.append_nil] using ih _ tail ht

theorem programC_entries (g : CanonTable.HiddenF) {β : Type} (program : M β)
    (result : (β × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (WPair.Counted.programC hU omega program))) :
    result.1.2 = publicEntriesOf (wA hU omega g) result.2 := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [WPair.Counted.programC_pure,observed_pure,mem_support_pure_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rcases input with (n|x)|coordinate
      · rw [WPair.Counted.programC_coin,observed_query_bind] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨coin,-,tail,ht,rfl⟩ := hr
        exact ih coin tail ht
      · rw [WPair.Counted.programC_public,observed_bind,observed_hashC] at hr
        simp only [pure_bind,observed_bind,observed_pure,bind_assoc,List.append_nil,List.nil_append] at hr
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        simpa only [publicEntriesOf,List.map_cons,List.append_nil,List.cons_append,List.nil_append]
          using congrArg (List.cons (x,wA hU omega g (.inl (.inr x)))) (ih _ tail ht)
      · rw [WPair.Counted.programC_private] at hr
        exact ih _ result hr

theorem worldC_entries (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (result : (Bool × QueryLog Paired.Requests × List Wots.Entry) × List HashInput)
    (hr : result ∈ support (observed g (worldC hU omega adversary))) :
    result.1.2.2=publicEntriesOf (wA hU omega g) result.2 := by
  unfold worldC experimentC at hr
  rw [observed_bind,observed_clocks,pure_bind,observed_bind] at hr
  simp only [observed_bind,observed_pure,pure_bind,bind_assoc,List.append_nil,List.nil_append] at hr
  simp only [mem_support_bind_iff,mem_support_pure_iff] at hr
  obtain ⟨interaction,hi,checked,hc,rfl⟩ := hr
  simp only [List.nil_append,List.append_nil,publicEntriesOf_append]
  rw [interactionC_entries hU omega g _ _ _ hi, programC_entries hU omega g _ _ hc]

/-- This erasure keeps the observed public transcript of every completed run. -/
theorem observed_cap_completed (g : CanonTable.HiddenF) {α : Type}
    (program : OracleComp CountSpec α) (budget remaining : Nat) (value : α) (inputs : List HashInput)
    (hr : (some (value,remaining),inputs) ∈ support
      (observed g (SphincsSecurity.QueryCap.run charged program budget))) :
    (value,inputs) ∈ support (observed g program) := by
  induction program using OracleComp.inductionOn generalizing budget remaining inputs with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.run_pure,observed_pure,mem_support_pure_iff,
        Prod.mk.injEq,Option.some.injEq] at hr
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
      simp only [observed_pure,mem_support_pure_iff]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind] at hr
      by_cases hc : charged input
      · rw [if_pos hc] at hr
        cases budget with
        | zero => simpa [observed_pure] using hr
        | succ budget =>
            rw [observed_query_bind] at hr ⊢
            simp only [mem_support_bind_iff,mem_support_pure_iff] at hr ⊢
            obtain ⟨answer,ha,tail,ht,he⟩ := hr
            obtain ⟨hs,hs'⟩ := Prod.mk.inj he
            refine ⟨answer,ha,(value,tail.2),?_,?_⟩
            · apply ih answer budget remaining tail.2
              simpa only [hs,Prod.mk.eta] using ht
            · exact Prod.ext rfl hs'
      · rw [if_neg hc,observed_query_bind] at hr
        rw [observed_query_bind]
        simp only [mem_support_bind_iff,mem_support_pure_iff] at hr ⊢
        obtain ⟨answer,ha,tail,ht,he⟩ := hr
        obtain ⟨hs,hs'⟩ := Prod.mk.inj he
        refine ⟨answer,ha,(value,tail.2),?_,?_⟩
        · apply ih answer budget remaining tail.2
          simpa only [hs,Prod.mk.eta] using ht
        · exact Prod.ext rfl hs'
#print axioms worldC_entries
#print axioms observed_cap_completed
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen worldC worldRLog cappedWorld
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem publicEntriesOf_ref (T : Answers) (queries : List RefWorld.Domain) :
    publicEntriesOf T (refPublicInputs queries)=Wots.traceOf T queries := by
  induction queries with
  | nil => rfl
  | cons input queries ih =>
    rcases input with (n|x)|tick <;> simpa [publicEntriesOf,refPublicInputs,Wots.traceOf] using ih

theorem cappedWorld_entries (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (budget remaining : Nat) (value : Bool × QueryLog Paired.Requests × List Wots.Entry)
    (queries : List CountSpec.Domain)
    (hr : (some (value,remaining),queries) ∈ support
      (simulateQ (fixedCount g) (cappedWorld hU omega adversary budget))) :
    value.2.2=publicEntriesOf (wA hU omega g) (publicInputs queries) := by
  apply worldC_entries hU omega g adversary (value,publicInputs queries)
  apply observed_cap_completed g (worldC hU omega adversary) budget remaining value (publicInputs queries)
  rw [observed_recorded,support_map]
  exact ⟨(some (value,remaining),queries),by simpa only [cappedWorld,cappedProgram] using hr,rfl⟩

theorem worldC_log_distribution (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat) :
    (fun run : RunResult (β := Bool) =>
      (run.1.map (fun value => ((value.1.1,value.1.2.1),value.2)),publicInputs run.2)) <$>
      simulateQ (fixedCount g) (cappedWorld hU omega adversary budget) =
    (fun run => (run.1,refPublicInputs run.2)) <$>
      simulateQ (Wots.refImpl (wA hU omega g)) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog (wA hU omega g) adversary) budget)) := by
  have ht := worldC_log_transport hU omega g adversary budget
  rw [bind_pure_comp,run_map_result,observed_map] at ht
  simpa only [observed_recorded,refObserved_recorded,Functor.map_map,cappedWorld,cappedProgram] using ht

theorem worldRLog_event_eq (g : CanonTable.HiddenF) (adversary : AdversaryP) (budget : Nat)
    (P : QueryLog Paired.Requests → List Wots.Entry → Prop) :
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧
        P value.2 (Wots.traceOf (wA hU omega g) run.2) |
      simulateQ (Wots.refImpl (wA hU omega g)) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog (wA hU omega g) adversary) budget))] =
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧ P value.2.1 value.2.2 |
      simulateQ (fixedCount g) (cappedWorld hU omega adversary budget)] := by
  have ht := congrArg (fun experiment : ProbComp
      (Option ((Bool × QueryLog Paired.Requests) × Nat) × List HashInput) =>
    Pr[fun run => ∃ value remaining,run.1=some (value,remaining) ∧
      P value.2 (publicEntriesOf (wA hU omega g) run.2) | experiment])
    (worldC_log_distribution hU omega g adversary budget)
  simp only [probEvent_map,Function.comp_def,publicEntriesOf_ref] at ht
  refine ht.symm.trans (probEvent_ext ?_)
  intro run hr
  rcases run with ⟨out,queries⟩
  cases out with
  | none => simp
  | some found =>
    rcases found with ⟨value,remaining⟩
    have he := cappedWorld_entries hU omega g adversary budget remaining value queries hr
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,exists_and_left,
      exists_eq_left,exists_eq_left',he, and_assoc]
#print axioms worldRLog_event_eq
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged ticks)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP ForgeryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
open SigGolfCandidate.T3.Security.Wots.Ref (cap_recorded_le chargeSum chargeSum_append cut pureRecord pureRecord_value
  fixedRecord_counted fixedRecord_hashOnly pureRecord_charge recorded_bind ticks_recorded verdict_recorded_fixed
  traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public embed)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen worldRLog
variable (adversary : AdversaryP) (q : Nat) (T : Answers)
  (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e∈entries,e∈entries') → P A log entries → P A log entries')
include hshort in
theorem fixed_step_full_charge (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Paired.Requests))
    (hi : interaction ∈ support (Wots.PairedReference.Ref.fixedInteraction adversary T))
    (hev : chargeSum (Wots.PairedReference.Ref.combine T interaction).events ≤ q ∧
      ∀ g i c, Wots.PairedReference.GameSplit adversary (Wots.PairedReference.Ref.combine T interaction) g i c →
        P (cut (Wots.PairedReference.Ref.combine T interaction).state T) i.value.2
          (SigGolfCandidate.T3.Security.BPair.publicEntries c.events)) :
    P T interaction.value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value))) ∧
      Wots.keygenCharge T + chargeSum interaction.events +
        Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hp := Paired.fixed_step adversary q T P hshort interaction hi hev
  refine ⟨hp.2,?_⟩
  have hk : chargeSum (pureRecord T keygen (∅,∅)).events = Wots.keygenCharge T :=
    pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅,∅)
  have hv : chargeSum (Wots.PairedReference.Ref.verdictRecord T interaction).events =
      Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
    pureRecord_charge T _ (Wots.PairedReference.Ref.verdict_hashOnly _ _) interaction.state
  have hc : chargeSum (Wots.PairedReference.Ref.combine T interaction).events =
      chargeSum (pureRecord T keygen (∅,∅)).events +
        (chargeSum interaction.events + chargeSum (Wots.PairedReference.Ref.verdictRecord T interaction).events) := by
    simp only [Wots.PairedReference.Ref.combine,chargeSum_append]
  have hb := hev.1
  omega

include hmono in
theorem offline_log_event_le :
    Pr[fun x => P T x.1.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T x.1))) ∧
        Wots.keygenCharge T+x.2+Wots.PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 x.1≤q |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (Wots.PairedReference.offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
    Pr[fun run => ∃ value remaining, run.1=some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2) |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))] := by
  refine le_trans ?_ (WPair.Counted.Generic.cap_recorded_completed_le RefCharged (Wots.refImpl T)
    (worldRLog T adversary) q (fun value queries => P T value.2 (Wots.traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted,simulateQ_map,probEvent_map]
  unfold worldRLog
  rw [recorded_bind,simulateQ_bind,ticks_recorded,pure_bind,recorded_bind,simulateQ_bind]
  simp only [simulateQ_bind,simulateQ_pure,bind_assoc]
  simp only [recorded_bind,simulateQ_bind,verdict_recorded_fixed T _
    (PairedOuter.PaddedGame.verdict_public _ _),pure_bind,SphincsSecurity.QueryCap.recorded_pure,simulateQ_pure]
  rw [bind_pure_comp,probEvent_map]
  apply probEvent_mono
  rintro ⟨result,queries⟩ - ⟨hp,hcharge⟩
  refine ⟨?_,?_⟩
  · change P T result.2 (Wots.traceOf T (List.replicate (Wots.keygenCharge T) (.inr ()) ++ (queries ++
      (List.map embed (SourceReplay.queried T (verdictOn T result)) ++ []))))
    rw [List.append_nil,traceOf_append,traceOf_append,traceOf_replicate_tick,traceOf_map_embed]
    exact hmono _ _ _ _ (fun e he => List.mem_append_right _ (List.mem_append_right _ he)) hp
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (Wots.keygenCharge T) (.inr ()) ++
      (queries ++ (List.map embed (SourceReplay.queried T (verdictOn T result)) ++ []))) ≤ q
    rw [List.append_nil,calls_append,calls_append,calls_replicate_tick,
      calls_map_embed_public T _ (PairedOuter.PaddedGame.verdict_public _ _)]
    simpa only [Wots.PairedReference.Ref.verdictCharge,Nat.add_assoc] using hcharge

include hshort hmono in
theorem fixed_le_worldRLog :
    Pr[fun result => chargeSum result.events≤q ∧
        ∀ g i c,Wots.PairedReference.GameSplit adversary result g i c →
          P (cut result.state T) i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events) |
      Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)] ≤
    Pr[fun run => ∃ value remaining, run.1=some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2) |
      simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))] := by
  rw [Wots.PairedReference.Ref.fixed_game_eq,probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi he =>
    fixed_step_full_charge adversary q T P hshort interaction hi he) ?_
  have hcount := fixedRecord_counted T (PairedOuter.FullGame.loggedWith
    (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅,∅)).state
  rw [Wots.PairedReference.Ref.interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offline_log_event_le adversary q T P hmono)
  rw [← hcount,probEvent_map]
  rfl
#print axioms fixed_le_worldRLog
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open SphincsSecurity.Concrete.SecretGuessObservation
open ClaudeWCT.W9.T3.Security.WPair.Counted
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local instance] ClaudeWCT.W9.T3.Security.WPair.Counted.chargedDecidable
attribute [local irreducible] keygen worldC cappedWorld
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)
variable (adversary : AdversaryP) (budget : Nat)
 theorem world_public_distribution :
    (fun result => publicInputs result.1.2) <$>
      withRun (Result := RunResult (β := Bool)) countEnvironment (Guess.Fam.sampler PUnit)
        (cappedWorld hU omega adversary budget) countInit =
    𝒮[do
      let hidden ← ($ᵗ CanonTable.HiddenF : ProbComp _)
      let result ← Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget
      pure (refPublicInputs result.2)] := by
  rw [WPair.Counted.Generic.public_program_distribution]
  apply congrArg (fun experiment : ProbComp (List HashInput) => 𝒮[experiment])
  apply bind_congr
  intro hidden
  simpa only [bind_pure_comp] using worldC_public_transport hU omega hidden adversary budget

 theorem world_public_payment_le_reference :
    (∑' result, Pr[= result | withRun (Result := RunResult (β := Bool)) countEnvironment (Guess.Fam.sampler PUnit)
      (cappedWorld hU omega adversary budget) countInit] *
      (probeCount (publicInputs result.1.2) : ENNReal)) ≤
    ∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget] *
        (Wots.PairedReference.otherCount ⟨wA hU omega hidden, (evalWithAnswerFn (wA hU omega hidden) keygen).1,
          Wots.traceOf (wA hU omega hidden) run.2⟩ : ENNReal) := by
  rw [← tsum_probOutput_map_mul _ (fun result : RunResult (β := Bool) × CountState => publicInputs result.1.2)
    (fun inputs => (probeCount inputs : ENNReal)), world_public_distribution hU omega adversary budget]
  simp only [bind_pure_comp, evalSPMF_bind, evalSPMF_map]
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro hidden
  simp only [probOutput_evalSPMF]
  apply mul_le_mul' le_rfl
  rw [tsum_probOutput_map_mul]
  simp only [probOutput_evalSPMF]
  apply ENNReal.tsum_le_tsum
  intro run
  apply mul_le_mul' le_rfl
  rw [refPublicInputs_eq_trace (wA hU omega hidden)]
  exact_mod_cast probeCount_le_other_new (wA hU omega hidden) _ (Wots.traceOf (wA hU omega hidden) run.2)

 theorem world_event_le_other
    (hbudget : budget < 2^128)
    (event : CanonTable.HiddenF → RunResult (β := Bool) → Prop)
    (hevent : ∀ hidden result, event hidden result → ∃ output remaining,
      result.1 = some (output, remaining) ∧ ¬Paired.OverflowIn (wA hU omega hidden) output.2.1 ∧
      ∃ cell, Paired.GuessedIn (wA hU omega hidden) output.2.1 output.2.2 cell) :
    Pr[fun result => event result.1 result.2 | WPair.Counted.Generic.countedProgramRun
      (cappedWorld hU omega adversary budget)] ≤
      (((2^128-budget : Nat) : ENNReal))⁻¹ *
      (∑' hidden, Pr[= hidden | ($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' run, Pr[= run | Wots.PairedReference.offlineRun (wA hU omega hidden) adversary budget] *
        (Wots.PairedReference.otherCount ⟨wA hU omega hidden, (evalWithAnswerFn (wA hU omega hidden) keygen).1,
          Wots.traceOf (wA hU omega hidden) run.2⟩ : ENNReal)) :=
  (world_event_le_external hU omega adversary budget hbudget event hevent).trans
    (mul_le_mul' le_rfl (world_public_payment_le_reference hU omega adversary budget))


#print axioms world_event_le_other
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefSample)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
attribute [local irreducible] keygen Wots.PairedReference.referenceInputs Wots.PairedReference.offlineRun Wots.PairedReference.otherCount

noncomputable def tableAverage {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α) : ProbComp α :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      K (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable)

theorem tableAverage_eq {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α) :
    𝒮[tableAverage adversary K] =
    𝒮[omegaLaw (Wots.PairedReference.referenceInputs adversary) >>= fun omega =>
      ($ᵗ CanonTable.HiddenF : ProbComp _) >>= fun g => K (wA (canon_subset adversary) omega g)] := by
  unfold tableAverage
  have h1 : (fun privateTable =>
      ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
        K (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable)) =
      (fun privateTable =>
      ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
        K (CanonGraph.eagerAnswers privateTable (Wots.PairedReference.referenceInputs adversary) publicTable)) := by
    funext privateTable
    apply bind_congr
    intro publicTable
    simp only [eagerAnswers_eq]
  rw [h1,CanonTable.world_tables_bind (canon_subset adversary) K]
  unfold omegaLaw
  simp only [bind_assoc,pure_bind]

noncomputable def referenceOther (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' s, Wots.PairedReference.referenceExperiment adversary q s * (Wots.PairedReference.otherCount s : ENNReal)

noncomputable def worldOther (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) : ENNReal :=
  ∑' g, Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
    ∑' run, Pr[=run|Wots.PairedReference.offlineRun (wA (canon_subset adversary) omega g) adversary q] *
      (Wots.PairedReference.otherCount ⟨wA (canon_subset adversary) omega g,
        (evalWithAnswerFn (wA (canon_subset adversary) omega g) keygen).1,
        Wots.traceOf (wA (canon_subset adversary) omega g) run.2⟩ : ENNReal)

theorem lift_prob_apply {α : Type} (c : ProbComp α) (x : α) : (liftM c : PMF α) x = Pr[=x|c] := by
  rw [← PMF.probOutput_eq_apply]
  have h1 : 𝒮[(liftM c : PMF α)] = 𝒮[c] := by
    rw [evalSPMF_eq_simulateQ, PMF.evalSPMF_eq]
    rfl
  unfold probOutput
  rw [h1]

theorem expectation_congr {α : Type} (c d : ProbComp α) (h : 𝒮[c]=𝒮[d]) (f : α → ENNReal) :
    (∑' x, Pr[=x|c]*f x) = ∑' x, Pr[=x|d]*f x := by
  apply tsum_congr
  intro x
  have hp : Pr[=x|c]=Pr[=x|d] := by
    rw [←probOutput_evalSPMF,h,probOutput_evalSPMF]
  rw [hp]

theorem tableAverage_expect {α : Type} (adversary : AdversaryP) (K : Answers → ProbComp α)
    (f : α → ENNReal) :
    (∑' x, Pr[=x|tableAverage adversary K]*f x) =
      ∑' omega,Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' x,Pr[=x|K (wA (canon_subset adversary) omega g)]*f x := by
  rw [expectation_congr _ _ (tableAverage_eq adversary K),tsum_probOutput_bind_mul]
  apply tsum_congr
  intro omega
  rw [tsum_probOutput_bind_mul]

noncomputable def sampleRun (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T,(evalWithAnswerFn T keygen).1,Wots.traceOf T run.2⟩ : RefSample)) <$>
    Wots.PairedReference.offlineRun T adversary q

theorem referenceComp_tableAverage (adversary : AdversaryP) (q : Nat) :
    𝒮[Wots.PairedReference.referenceComp adversary q] =
    𝒮[tableAverage adversary (sampleRun adversary q)] := by
  unfold Wots.PairedReference.referenceComp tableAverage sampleRun
  rw [SigGolfCandidate.T3.Security.BPair.bind_uniform_congr _ instSampleableTypeFullTable_canonGraph]

theorem lift_expect {α : Type} (c : ProbComp α) (f : α → ENNReal) :
    (∑' x,(liftM c : PMF α) x*f x) = ∑' x,Pr[=x|c]*f x := by
  apply tsum_congr
  intro x
  exact congrArg (fun p => p*f x) (lift_prob_apply c x)

theorem referenceOther_eq (adversary : AdversaryP) (q : Nat) :
    referenceOther adversary q = ∑' s,Pr[=s|Wots.PairedReference.referenceComp adversary q]*
      (Wots.PairedReference.otherCount s : ENNReal) := by
  have hd : Wots.PairedReference.referenceExperiment adversary q =
      (liftM (Wots.PairedReference.referenceComp adversary q) : PMF RefSample) := rfl
  exact (congrArg (fun mu : PMF RefSample => ∑' s,mu s*(Wots.PairedReference.otherCount s : ENNReal)) hd).trans
    (lift_expect (Wots.PairedReference.referenceComp adversary q) (fun s=>(Wots.PairedReference.otherCount s : ENNReal)))
#print axioms referenceOther_eq

theorem worldOther_eq (adversary : AdversaryP) (q : Nat)
    (omega : CanonTable.Omega (Wots.PairedReference.referenceInputs adversary)) :
    worldOther adversary q omega = ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      ∑' s,Pr[=s|sampleRun adversary q (wA (canon_subset adversary) omega g)]*
        (Wots.PairedReference.otherCount s : ENNReal) := by
  unfold worldOther
  apply tsum_congr
  intro g
  unfold sampleRun
  rw [tsum_probOutput_map_mul]
#print axioms worldOther_eq

theorem referenceOther_avg (adversary : AdversaryP) (q : Nat) :
    referenceOther adversary q = ∑' omega,
      Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] * worldOther adversary q omega := by
  rw [referenceOther_eq]
  refine (expectation_congr _ _ (referenceComp_tableAverage adversary q) _).trans ?_
  refine (tableAverage_expect adversary (sampleRun adversary q) _).trans ?_
  apply tsum_congr
  intro omega
  rw [worldOther_eq]
#print axioms referenceComp_tableAverage
#print axioms tableAverage_expect
#print axioms referenceOther_avg
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (RefWorld RefCharged)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
open ClaudeWCT.W9.T3.Security.WPair.Counted
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
attribute [local irreducible] keygen worldRLog cappedWorld

abbrev LogResult := Option ((Bool × QueryLog Paired.Requests) × Nat) × List RefWorld.Domain
noncomputable def logRun (T : Answers) (adversary : AdversaryP) (q : Nat) : ProbComp LogResult :=
  simulateQ (Wots.refImpl T) (SphincsSecurity.QueryCap.recorded
    (SphincsSecurity.QueryCap.run RefCharged (worldRLog T adversary) q))
def logEvent (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
    (T : Answers) (run : LogResult) : Prop :=
  ∃ value remaining, run.1 = some (value,remaining) ∧ P T value.2 (Wots.traceOf T run.2)
def countEvent (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
    (T : Answers) (run : RunResult (β := Bool)) : Prop :=
  ∃ value remaining, run.1 = some (value,remaining) ∧ P T value.2.1 value.2.2
noncomputable def logExperiment (adversary : AdversaryP) (q : Nat) :=
  tableAverage adversary (fun T => (fun run => (T,run)) <$> logRun T adversary q)

theorem countedProgram_prob {α : Type} (program : OracleComp CountSpec α)
    (event : CanonTable.HiddenF × α → Prop) :
    Pr[event | WPair.Counted.Generic.countedProgramRun program] =
    ∑' g,Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)] *
      Pr[fun run=>event (g,run) | simulateQ (fixedCount g) program] := by
  unfold WPair.Counted.Generic.countedProgramRun
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro g
  simp only [bind_pure_comp,probEvent_map,Function.comp_def,probOutput_uniformSample]

variable (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2^127)
  (P : Answers → QueryLog Paired.Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e∈entries,e∈entries') → P A log entries → P A log entries')

include hshort hmono in
theorem shared_le_logExperiment :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun run => logEvent P run.1 run.2 | logExperiment adversary q] := by
  refine (Paired.shared_budget_le_recorded adversary q hq (fun rec A => ∀ g i c,
    Wots.PairedReference.GameSplit adversary rec g i c →
      P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))).trans ?_
  rw [Wots.PairedReference.Ref.recorded_eq_eager adversary (fun rec A => Wots.Ref.chargeSum rec.events≤q ∧
    ∀ g i c,Wots.PairedReference.GameSplit adversary rec g i c →
      P A i.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries c.events))]
  unfold Wots.Ref.eagerSide logExperiment tableAverage
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro privateTable
  apply SigGolfCandidate.T3.Security.BPair.probEvent_bind_mono'
  intro publicTable
  rw [probEvent_map,probEvent_map,Wots.Ref.fillAnswers_empty]
  exact fixed_le_worldRLog adversary q
    (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) privateTable publicTable) P hshort hmono

 theorem logExperiment_avg :
    Pr[fun run => logEvent P run.1 run.2 | logExperiment adversary q] =
    ∑' omega, Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)] *
      Pr[fun run => countEvent P (wA (canon_subset adversary) omega run.1) run.2 |
        WPair.Counted.Generic.countedProgramRun (cappedWorld (canon_subset adversary) omega adversary q)] := by
  unfold logExperiment
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (tableAverage_eq adversary _)]
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro omega
  apply congrArg (fun x => Pr[=omega|omegaLaw (Wots.PairedReference.referenceInputs adversary)]*x)
  rw [countedProgram_prob]
  conv_lhs => rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro g
  apply congrArg (fun x => Pr[=g|($ᵗ CanonTable.HiddenF : ProbComp _)]*x)
  simp only [bind_pure_comp,probEvent_map,Function.comp_def,probOutput_uniformSample]
  exact worldRLog_event_eq (canon_subset adversary) omega g adversary q (P (wA (canon_subset adversary) omega g))

include hshort hmono in
theorem completed_event_le_other
    (hno : ∀ A log entries,P A log entries → ¬Paired.OverflowIn A log)
    (hguess : ∀ A log entries,P A log entries → ∃ cell,Paired.GuessedIn A log entries cell) :
    Pr[fun z => z.1.2.2.base.source.1 ≤ q ∧ ∀ generated interaction checked,
      Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
        P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    (((2^128-q : Nat) : ENNReal))⁻¹ * referenceOther adversary q := by
  refine (shared_le_logExperiment adversary q hq P hshort hmono).trans ?_
  rw [logExperiment_avg,referenceOther_avg,←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro omega
  rw [← mul_assoc, mul_comm (((2^128-q : Nat) : ENNReal))⁻¹, mul_assoc]
  apply mul_le_mul' le_rfl
  have hg : q < 2^128 := lt_of_le_of_lt hq (by norm_num)
  have hw := world_event_le_other (canon_subset adversary) omega adversary q hg
    (fun g result => countEvent P (wA (canon_subset adversary) omega g) result)
    (by
      intro hidden result he
      obtain ⟨value,remaining,hr,hP⟩ := he
      exact ⟨value,remaining,hr,hno _ _ _ hP,hguess _ _ _ hP⟩)
  simpa only [worldOther,probOutput_uniformSample] using hw
#print axioms completed_event_le_other
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.WPair.Paired.Counted
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (RefSample)
open ClaudeWCT.W9.T3M.Final.Paired (AdversaryP)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Wots.PairedReference.referenceExperiment

theorem referenceOther_le (adversary : AdversaryP) (q : Nat) : referenceOther adversary q≤q := by
  unfold referenceOther
  calc
    _ ≤ (∑' s,Wots.PairedReference.referenceExperiment adversary q s*(q:ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro s
      rcases Classical.em (Wots.PairedReference.referenceExperiment adversary q s=0) with hs | hs
      · simp only [hs,zero_mul,le_refl]
      · apply mul_le_mul' le_rfl
        have htrace := Wots.PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
        have hc : Wots.PairedReference.otherCount s ≤ s.trace.length := List.length_filter_le _ _
        exact_mod_cast hc.trans htrace
    _ = q := by rw [ENNReal.tsum_mul_right,PMF.tsum_coe,one_mul]

theorem referenceOther_ne_top (adversary : AdversaryP) (q : Nat) : referenceOther adversary q≠⊤ :=
  ne_top_of_le_ne_top (by simp) (referenceOther_le adversary q)
#print axioms referenceOther_le
end ClaudeWCT.W9.T3.Security.WPair.Paired.Counted

namespace ClaudeWCT.W9.T3.Security.PairedBankLink
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (IsDigestInput countOf lazyOf genRecord genRecord_support Agrees)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
open ClaudeWCT.Bank (Ghost FtsBankSpecL)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section GenericPotential
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option SigGolfCandidate.Research.SharedForest.Signature))
  (hrecord : ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    PairedOuter.FullGame.authenticatedSign published request)
include hrecord

theorem full_potential
    (hhash : ClaudeWCT.Bank.PayHashOnly pay)
    (hrho : ClaudeWCT.Bank.PayRho pay SigGolfCandidate.Research.SharedForest.Signature.rho)
    (hAvoids : ClaudeWCT.Bank.PayAvoids pay)
    (hsearch : ∀ rho message, S.search rho message 0 S.limit =
      SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message 0 WCT9.digestAttemptLimit)
    (hcovered : ∀ X N, (∀ k t, WPair.Paired.SlotCovered X N k t) → S.covered X N)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (b : Bool × PairedBankState) (hb : b ∈ (S.bankExperiment pay (rest adversary) q).support)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (gen' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (int' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests))
    (chk' : FirstHit.Recorded Bool)
    (hsplit : Wots.PairedReference.GameSplit adversary ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ gen' int' chk')
    (hlen : int'.value.2.length ≤ S.horizon)
    (input : HashInput) (N : HashOutput) (hdig : IsDigestInput input)
    (prior : LazyPrivate.State)
    (hev : (⟨prior,.inl (.inr input),N⟩ : FirstHit.QueryEvent) ∈ b.2.2.events)
    (hnot : ∀ entry ∈ int'.value.2, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (PairedOuter.FullGame.authenticatedSign gen'.value.2 entry.1))
    (hadm : S.admissible N=true)
    (hfull : ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs A int'.value.2) N k t) :
    1 ≤ S.potential q b.2 := by
  obtain ⟨generated,hg,int0,hint0,⟨tail,htail⟩,hlog,hinv⟩ :=
    bank_actual S pay SigGolfCandidate.Research.SharedForest.Signature.rho hrecord
      hhash hrho hAvoids adversary q b hb
  obtain ⟨hgen,hint⟩ := split_unique adversary _ (genRecord generated)
    (genRecord_support generated hg) int0 hint0 tail htail gen' int' chk' hsplit
  subst hgen hint
  have halive : b.2.1.dead=false := hinv.alive S pay
    SigGolfCandidate.Research.SharedForest.Signature.rho (by rwa [hlog])
  have hRsupp : (⟨b.1,b.2.2.events,lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)) := by
    have hm : (b.1,b.2.2) ∈ ((fun r : PairedOuter.PaddedGame.TraceResult => (r.1,r.2.2)) <$>
        PairedOuter.PaddedGame.tracedExperiment adversary q hq).support := by
      rw [←bank_traced S pay hrecord adversary q hq,PMF.monad_map_eq_map,PMF.mem_support_map_iff]
      exact ⟨b,hb,rfl⟩
    rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff] at hm
    obtain ⟨r,hr,hre⟩ := hm
    have := traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first,hfirst,hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior input N hev
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅,∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [←hkg]
        exact List.mem_map_of_mem hk
      obtain ⟨rho,message,counter,rfl⟩ := hdig
      exact SigGolfCandidate.T3.Security.CaseC.queried_notDigest_keygen _ _ hmem
        (BPB.hdrMarker_digestInput rho message counter)
    · rcases hp input N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q<countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry,hentry,hquery⟩ := hs
        have hqA := hquery A hA
        rw [bank_source S pay hrecord] at hqA
        change (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          queried A (PairedOuter.FullGame.authenticatedSign generated.1.2 entry.1) at hqA
        rw [hlog] at hentry
        exact hnot entry hentry hqA
  have hcov : S.covered b.2.1.exposures N := by
    apply hcovered
    intro k t
    obtain ⟨out,hout,h1,h2,h3⟩ := hfull k t
    obtain ⟨entry,hentry,signature,hsig,hsigned⟩ := WPair.Paired.mem_loggedOutputs.mp hout
    rw [←hlog] at hentry
    unfold WPair.Paired.signedOutput at hsigned
    cases hs : evalWithAnswerFn A
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch signature.rho entry.1.message 0 WCT9.digestAttemptLimit) with
    | none => rw [hs] at hsigned; cases hsigned
    | some found =>
        rw [hs] at hsigned
        simp only [Option.map_some,Option.some.injEq] at hsigned
        rcases found with ⟨counter,out'⟩
        simp only at hsigned
        subst hsigned
        have hs' : evalWithAnswerFn A (S.search signature.rho entry.1.message 0 S.limit)=some (counter,out') := by
          rw [hsearch]
          exact hs
        exact ⟨out',ClaudeWCT.Bank.FtsBankSpecL.BankInv.logged_exposed S pay
          SigGolfCandidate.Research.SharedForest.Signature.rho hinv halive entry hentry signature hsig A hA counter out' hs',h1,h2,h3⟩
  exact S.potential_win q b.2 halive hcount (Or.inr ⟨N,htarget,hadm,hcov⟩)
end GenericPotential
#print axioms full_potential
end ClaudeWCT.W9.T3.Security.PairedBankLink

namespace ClaudeWCT.W9.T3.Security.PairedBankLink
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (IsDigestInput countOf lazyOf genRecord genRecord_support Agrees)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
open ClaudeWCT.Bank (Ghost FtsBankSpecL)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section GenericPotential
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option SigGolfCandidate.Research.SharedForest.Signature))
  (hrecord : ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    PairedOuter.FullGame.authenticatedSign published request)
include hrecord

theorem full_target_covered
    (hhash : ClaudeWCT.Bank.PayHashOnly pay)
    (hrho : ClaudeWCT.Bank.PayRho pay SigGolfCandidate.Research.SharedForest.Signature.rho)
    (hAvoids : ClaudeWCT.Bank.PayAvoids pay)
    (hsearch : ∀ rho message, S.search rho message 0 S.limit =
      SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message 0 WCT9.digestAttemptLimit)
    (hcovered : ∀ X N, (∀ k t, WPair.Paired.SlotCovered X N k t) → S.covered X N)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (b : Bool × PairedBankState) (hb : b ∈ (S.bankExperiment pay (rest adversary) q).support)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (gen' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (int' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests))
    (chk' : FirstHit.Recorded Bool)
    (hsplit : Wots.PairedReference.GameSplit adversary ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ gen' int' chk')
    (hlen : int'.value.2.length ≤ S.horizon)
    (input : HashInput) (N : HashOutput) (hdig : IsDigestInput input)
    (prior : LazyPrivate.State)
    (hev : (⟨prior,.inl (.inr input),N⟩ : FirstHit.QueryEvent) ∈ b.2.2.events)
    (hnot : ∀ entry ∈ int'.value.2, (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried A (PairedOuter.FullGame.authenticatedSign gen'.value.2 entry.1))
    (hadm : S.admissible N=true)
    (hfull : ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs A int'.value.2) N k t) :
    b.2.1.dead=false ∧ N∈b.2.1.targets ∧ S.covered b.2.1.exposures N := by
  obtain ⟨generated,hg,int0,hint0,⟨tail,htail⟩,hlog,hinv⟩ :=
    bank_actual S pay SigGolfCandidate.Research.SharedForest.Signature.rho hrecord
      hhash hrho hAvoids adversary q b hb
  obtain ⟨hgen,hint⟩ := split_unique adversary _ (genRecord generated)
    (genRecord_support generated hg) int0 hint0 tail htail gen' int' chk' hsplit
  subst hgen hint
  have halive : b.2.1.dead=false := hinv.alive S pay
    SigGolfCandidate.Research.SharedForest.Signature.rho (by rwa [hlog])
  have hRsupp : (⟨b.1,b.2.2.events,lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅,∅)) := by
    have hm : (b.1,b.2.2) ∈ ((fun r : PairedOuter.PaddedGame.TraceResult => (r.1,r.2.2)) <$>
        PairedOuter.PaddedGame.tracedExperiment adversary q hq).support := by
      rw [←bank_traced S pay hrecord adversary q hq,PMF.monad_map_eq_map,PMF.mem_support_map_iff]
      exact ⟨b,hb,rfl⟩
    rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff] at hm
    obtain ⟨r,hr,hre⟩ := hm
    have := traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1,b.2.2.events,lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first,hfirst,hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior input N hev
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅,∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [←hkg]
        exact List.mem_map_of_mem hk
      obtain ⟨rho,message,counter,rfl⟩ := hdig
      exact SigGolfCandidate.T3.Security.CaseC.queried_notDigest_keygen _ _ hmem
        (BPB.hdrMarker_digestInput rho message counter)
    · rcases hp input N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q<countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry,hentry,hquery⟩ := hs
        have hqA := hquery A hA
        rw [bank_source S pay hrecord] at hqA
        change (.inl (.inr input) : SigGolfCandidate.T3.Spec.Domain) ∈
          queried A (PairedOuter.FullGame.authenticatedSign generated.1.2 entry.1) at hqA
        rw [hlog] at hentry
        exact hnot entry hentry hqA
  have hcov : S.covered b.2.1.exposures N := by
    apply hcovered
    intro k t
    obtain ⟨out,hout,h1,h2,h3⟩ := hfull k t
    obtain ⟨entry,hentry,signature,hsig,hsigned⟩ := WPair.Paired.mem_loggedOutputs.mp hout
    rw [←hlog] at hentry
    unfold WPair.Paired.signedOutput at hsigned
    cases hs : evalWithAnswerFn A
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch signature.rho entry.1.message 0 WCT9.digestAttemptLimit) with
    | none => rw [hs] at hsigned; cases hsigned
    | some found =>
        rw [hs] at hsigned
        simp only [Option.map_some,Option.some.injEq] at hsigned
        rcases found with ⟨counter,out'⟩
        simp only at hsigned
        subst hsigned
        have hs' : evalWithAnswerFn A (S.search signature.rho entry.1.message 0 S.limit)=some (counter,out') := by
          rw [hsearch]
          exact hs
        exact ⟨out',ClaudeWCT.Bank.FtsBankSpecL.BankInv.logged_exposed S pay
          SigGolfCandidate.Research.SharedForest.Signature.rho hinv halive entry hentry signature hsig A hA counter out' hs',h1,h2,h3⟩
  exact ⟨halive,htarget,hcov⟩
end GenericPotential
#print axioms full_target_covered
end ClaudeWCT.W9.T3.Security.PairedBankLink
