import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactCertClean
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingContact
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingBankSign
import SigGolfCandidate.ClaudeWCT.W9.New.C2.SignerCompleteBound

section


namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingCertShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem honestNonce_short : honestNonce A = honestNonce T := by
  funext m
  unfold honestNonce
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
  rw [hAT.priv]
end Short
end SigGolfCandidate.T3.Security.LargeCoupling
end

section






section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingCertInteraction : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingCertTable : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section CertChain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem pmf_probEvent_mono_support' {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]
section Lazy
variable {U : Finset HashInput}
theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
end Lazy
end CertChain
end SigGolfCandidate.T3.Security.LargeCoupling
end
end

section












section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem interaction_le' (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
        F (none, ws') ∨ ∀ m s v σ, Final m s v σ → m.contact = false) →
      (∀ m s v σ, Final m s v σ → FamOK s) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rcases input with (n | X) | request
      ·
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop hfin mon st ws _ hrel hmemo
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · by_cases hok : FamOK st
          swap
          · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                  (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                  last.state⟩ : Tagged α)) |
                taggedFixed T published (next (T (.inl (.inr X))))
                  (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
              refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
              intro t ht
              exact hok (famOK_mono (steps_disclosed_mono U T nv published _ _) (hfin _ _ _ _ ht))
            rw [hzero]
            exact zero_le
          rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq hok X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rcases hstop ws1 hcalls with hF | hnc
            · rw [probEvent_pure, if_pos hF]
              exact probEvent_le_one
            · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                    (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                  (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                    last.state⟩ : Tagged α)) |
                  taggedFixed T published (next (T (.inl (.inr X))))
                    (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
                refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
                intro t ht
                simp only [Function.comp_apply, List.foldl_cons] at ht
                have h1 := hnc _ _ _ _ ht
                change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                  = false at h1
                rw [steps_frozen U T q published _ hc] at h1
                rw [hc] at h1
                cases h1
              rw [hzero]
              exact zero_le
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop hfin _ _ ws1 _ hrel1 hmemo1
      ·
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hpub hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        have hstop' : ∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
            F (none, ws') ∨ ∀ m s v σ, Final' m s v σ → m.contact = false := by
          intro ws' hws
          rcases hstop ws' hws with h | h
          · exact Or.inl h
          · exact Or.inr fun m s v σ hf => h _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop' (fun m s v σ hf => hfin _ _ _ _ hf) _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingCertTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def verdictCert (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (st : RouterState) (value : Option ForgeryP × QueryLog Requests) (state : LazyPrivate.State) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker pk value) = true ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = false ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).calls ≤ q ∧
  CertGhost ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (routerEvent U) st)
theorem honestNonce_coherent {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell U → HashOutput} {a : AuxData} (hcoh : Coherent U T vals nv τ a) : nv = honestNonce T := by
  funext m
  exact (hcoh.privateNonce m).symm
theorem table_cert_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : Coherent (Wots.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => CertR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[CertOut |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary := Wots.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  have hnv := honestNonce_coherent hcoh
  rw [hcoh.routerWith, Wots.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le' initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hpub
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictCert (Wots.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon st
      value state ∧ FamOK st)
    (verdictCont (Wots.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) CertOut
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial RouterState.initial
    (keyState (Wots.referenceInputs adversary) q vals nv) _ rel_initial
    (fun _ _ h => by simp [RouterState.initial] at h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    obtain ⟨h1, h2, h3, h4⟩ := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h2 h3 h4
    have hv : (Wots.Ref.verdictRecord T t.untag).value =
        evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) :=
      Wots.Ref.pureRecord_value _ _ _
    refine ⟨⟨hv ▸ h1, h2, h3, ?_⟩, fun f => ?_, fun L => ?_⟩
    · unfold routerFold at h4
      rw [hnv]
      exact h4
    · have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
      have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 hpub _ _ t ht RouterState.initial f
      rw [discSeeds_initial, Finset.empty_union] at hsub
      exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
    · have hsub := discLower_steps (Wots.referenceInputs adversary) T nv (evalWithAnswerFn T keygen).2 t.steps
        RouterState.initial L
      rw [discLower_initial, Finset.empty_union] at hsub
      have := lowerZeros_card T L
      exact (Finset.card_le_card hsub).trans (by omega)
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.referenceInputs adversary) a q
        (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    obtain ⟨⟨hval, hnc, hcalls, hcert⟩, -⟩ := hf
    rcases hph with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · rw [hnc] at h2; cases h2
    · omega
    · rw [if_pos ⟨_, by rw [h1, hval], hcert⟩]
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    have := hf.1.2.2.1
    omega
  · intro ws' _
    right
    intro m s v σ hf
    by_contra hcon
    have hc : m.contact = true := by simpa using hcon
    have h := hf.1.2.1
    rw [events_frozen (Wots.referenceInputs adversary) T q m hc] at h
    rw [hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce honestNonce_short)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem routerStep_world (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (e : FirstHit.QueryEvent) : routerStep U A nv published st (.world e) = routerEvent U st e := rfl
theorem routerStep_sign (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (request : Security.Request) (out : Option Signature) (events : List FirstHit.QueryEvent) :
    routerStep U A nv published st (.sign request out events) = signedState A nv published st request := rfl
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem routeOk_short : RouteOk A = RouteOk T := by
  funext index
  apply propext
  unfold RouteOk
  simp only [Wots.Ref.referenceSearch_short hAT]
theorem signedState_short (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState A nv published st request = signedState T nv published st request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  unfold signedState LargeResidual.signItems
  rw [signDigest_short hAT, hd, routeOk_short hAT]
theorem routerStep_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (st : RouterState) (s : TaggedStep) :
    routerStep U A (honestNonce A) published st s = routerStep U T (honestNonce T) published st s := by
  cases s with
  | world e => rw [routerStep_world, routerStep_world]
  | sign request out events =>
      rw [routerStep_sign, routerStep_sign, honestNonce_short hAT, signedState_short hAT]
theorem steps_router_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ st, steps.foldl (routerStep U A (honestNonce A) published) st =
      steps.foldl (routerStep U T (honestNonce T) published) st := by
  induction steps with
  | nil => intro st; rw [List.foldl_nil, List.foldl_nil]
  | cons s rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, routerStep_short hAT, ih]
theorem routerFold_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    routerFold U A published steps verdict = routerFold U T published steps verdict := by
  unfold routerFold
  rw [steps_router_short hAT]
end Short
theorem certR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : CertR adversary q result A ↔ CertR adversary q result T := by
  unfold CertR
  simp only [monitorRun_short hAT, routerFold_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (pmf_probEvent_mono_support' probEvent_bind_mono_le probEvent_bind_le_of
  weight_self evalSPMF_uniform_inst probEvent_bind_congr_eq completeRows_none)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section CertChain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
def RealCert (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  CertR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem cert_real_side (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] =
      Pr[RealCert adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.completed_eager_cut adversary q hq (fun rec A => CertR adversary q rec A ∧ NoOvR adversary rec A)
  rw [h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => CertR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealCert adversary q := by
    funext x
    exact propext (and_congr (certR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
section Lazy
variable {U : Finset HashInput}
theorem finish_some_le {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U))) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | X >>= finish] ≤ Pr[fun r => ∃ v, r.1 = some v ∧ P v | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish ((none : Option R), st)] = 0 := by
        simp only [finish, probEvent_pure]
        rw [if_neg]
        rintro ⟨v, hv, -⟩
        cases hv
      rw [h0, mul_zero]
      exact zero_le
  | some v =>
      by_cases hP : P v
      · rw [if_pos ⟨v, rfl, hP⟩]
        exact mul_le_of_le_one_right zero_le probEvent_le_one
      · have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish (some v, st)] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro x hx hE
          unfold finish at hx
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hx
          obtain ⟨labels, -, table, -, rfl⟩ := hx
          obtain ⟨v', hv', hP'⟩ := hE
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact hP hP'
        rw [h0, mul_zero]
        exact zero_le
theorem observed_avg_le {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v | 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>=
        fun x => 𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q (view x) τ program LargeResidual.initial] ≤
      Pr[fun r => ∃ v, r.1 = some v ∧ P v | lazyRun aux q program LargeResidual.initial] := by
  rw [← cell_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (by change (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))).Nonempty
        rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]; exact Finset.univ_nonempty)
  refine le_trans (le_of_eq ?_) (finish_some_le (lazyRun aux q program LargeResidual.initial) P)
  rw [← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  apply propext
  rcases r with ⟨_ | v, st⟩
  · simp [retain]
  · simp [retain]
theorem certOut_iff (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    CertOut r ↔ ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st := by
  constructor
  · rintro ⟨st, h1, h2⟩
    exact ⟨_, h1, st, rfl, h2⟩
  · rintro ⟨v, h1, st, rfl, h2⟩
    exact ⟨st, h1, h2⟩
theorem router_side_cert (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ
          (routerWith (Wots.referenceInputs adversary) adversary q ⟨high, rows, priv⟩) LargeResidual.initial] ≤
      Pr[CertOut |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hce : (@CertOut (Wots.referenceInputs adversary)) =
      fun r => ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st :=
    funext fun r => propext (certOut_iff r)
  rw [hce]
  unfold router initReq
  rw [lazy_aux]
  change _ ≤ Pr[_ | (liftM initLaw : SPMF AuxData) >>= _]
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_mono_le
  intro high
  apply probEvent_bind_mono_le
  intro rows
  apply probEvent_bind_mono_le
  intro priv
  exact observed_avg_le (auxLaw initLaw) q _ _
end Lazy
theorem cert_le_lazy (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧ BPB.SignerComplete z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[CertOut | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
        LargeResidual.initial] := by
  have hU : canonInputs ⊆ Wots.referenceInputs adversary :=
    canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  refine le_trans (pmf_probEvent_mono_support' (G := fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
      NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) _ fun z hz h =>
    ⟨cert_of_clean adversary q hq z hz h.1 h.2.1 h.2.2.1, h.2.2.2⟩) ?_
  rw [cert_real_side]
  refine le_trans ?_ (router_side_cert adversary q)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun high => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun x => ?_
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.referenceInputs adversary)
          (programmed (Wots.referenceInputs adversary) hU (secOf x jk)
            (joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.referenceInputs adversary) hE (joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          ⟨high, rows, priv⟩ := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealCert
    rw [probEvent_map]
    have h := table_cert_le adversary q hq initLaw
      (coherent_psi (Wots.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ ⟨high, rows, priv⟩ (seedView_secOf x jk))
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end CertChain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingBankRun : DecidableEq T3.Cache := Classical.decEq _
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open LargeResidual
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingBankRun : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def bankPay {U : Finset HashInput} (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi q st
    | _ => 0) + slackT q r.2
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi q st + slackT q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi q st + slackT q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi q st + slackT q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi q st + slackT q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls
theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [RouterState.initial]),
    fun p hp => absurd hp (by simp [RouterState.initial]), fun X hX => absurd hX (by simp [RouterState.initial])⟩
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay q) ≤
      psi q RouterState.initial + coeffQ q * (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) =
      coeffQ q * (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction (auxLaw initLaw) q hUpub a _ _ _ (bankPay q) ?_ ?_ ?_ RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict (auxLaw initLaw) q a _ (bankPay q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]
end Run
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep TestStep ProbeStep
  continuation hazard terminal expected_stop_le continuation_anti continuation_pay continuation_probe
  initial_potential run_expected_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem message_payment_54 (space probes remaining : ℝ) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : 128 * (probes + remaining + 1) ≤ space) :
    (127 / 64) / space + PrimitiveMessagePotential.value space probes remaining ≤
      PrimitiveMessagePotential.value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : (127 / 64) * space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : (127 / 64) / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      (127 / 64) / space = ((127 / 64) * space) / space ^ 2 := by field_simp
      _ ≤ ((127 / 64) * space) / (space - probes) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← PrimitiveMessagePotential.message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith

theorem continuation_pay_54 (space q calls probes : Nat) (hspace : 0 < space) (hq : 128 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + (127 / 64 : ENNReal) / space ≤ continuation space q calls probes := by
  have hs : (0 : ℝ) < space := by exact_mod_cast hspace
  have hb : 128 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have hp : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := message_payment_54 space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs
    (by positivity) (by push_cast; linarith) (by push_cast; linarith)
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  have hof54 : ENNReal.ofReal ((127 / 64 : ℝ) / space) = (127 / 64 : ENNReal) / space := by
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (by positivity) hv, hof54] at hfinal
  rw [add_comm]
  exact hfinal

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
  [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

noncomputable def potential54 {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space
noncomputable def stopValue54 {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space
noncomputable def doneValue54 {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space

theorem terminal54_le_of_over {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue54 ch space q) (potential54 ch space q) result ≤
      (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (127 / 64 : ENNReal) * (ch.mass result.2 : ENNReal) / space ≤
      (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue54, hnot] using hm
  · simpa [terminal, potential54, continuation, hnot] using hm

theorem payment54_of_stepBound {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (input : spec.Domain) (state : σ) (h : StepBound step ch space q input state)
    (hspace : 0 < space) (hq8 : 128 * q ≤ space) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue54 ch space q) (potential54 ch space q)) ≤
      potential54 ch space q state := by
  have hq : 2 * q ≤ space := by omega
  rcases h with h | h | h | h
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential54]
    exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
      (ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _)
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    by_cases hc : ch.calls state + 1 ≤ q
    · rw [if_pos hc] at hmass
      have hsome : answer ≠ none := by
        have := (probEvent_eq_zero_iff.mp h.2) _ hresult
        simpa using this
      obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
      simp only [terminal, Option.elim_some, potential54]
      have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
        (ch.probes after) hspace hq (by omega) hcalls hp
      have hpay := continuation_pay_54 space q (ch.calls state) (ch.probes state) hspace hq8 hprobes hc
      have hm : (127 / 64 : ENNReal) * (ch.mass after : ENNReal) / space ≤
          (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space + (127 / 64 : ENNReal) / space := by
        rw [← ENNReal.add_div]
        apply ENNReal.div_le_div_right
        calc
          (127 / 64 : ENNReal) * (ch.mass after : ENNReal) ≤
              (127 / 64 : ENNReal) * ((ch.mass state + 1 : Nat) : ENNReal) :=
            mul_le_mul' le_rfl (by exact_mod_cast hmass)
          _ = (127 / 64 : ENNReal) * (ch.mass state : ENNReal) + (127 / 64 : ENNReal) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      calc
        _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
            ((127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space + (127 / 64 : ENNReal) / space) :=
          add_le_add hcont hm
        _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (127 / 64 : ENNReal) / space) +
            (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space := by ring
        _ ≤ _ := add_le_add hpay le_rfl
    · rw [if_neg hc, add_zero] at hmass
      exact (terminal54_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue54 ch space q) (potential54 ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (127 / 64 : ENNReal) * (ch.mass after : ENNReal) / space ≤
            (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue54, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential54, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
            (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space := by
          refine add_le_add (add_le_add h.2 ?_) le_rfl
          exact mul_le_of_le_one_left' tsub_le_self
        _ ≤ _ := by
          rw [add_comm ((space : ENNReal)⁻¹)]
          exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal54_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue54 ch space q) (potential54 ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (127 / 64 : ENNReal) * (ch.mass after : ENNReal) / space ≤
            (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue54, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential54, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state + 1) +
              (127 / 64 : ENNReal) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal54_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

theorem stop_add_mass_eq_54 {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (127 / 64 : ENNReal) * (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue54 ch space q) (doneValue54 ch space)) := by
  have hfun : terminal (stopValue54 ch space q) (doneValue54 ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) +
        (127 / 64 : ENNReal) * (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue54]
    · simp [terminal, doneValue54]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro result
  ring

theorem run_potential_initial_54 {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq8 : q ≤ 2 ^ 121) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (127 / 64 : ENNReal) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h : Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (127 / 64 : ENNReal) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / ((2 ^ 128 : Nat) : ENNReal) ≤
      potential54 ch (2 ^ 128) q init := by
    rw [stop_add_mass_eq_54]
    refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
      (potential54 ch (2 ^ 128) q) (stopValue54 ch (2 ^ 128) q) (doneValue54 ch (2 ^ 128))
      ?_ ?_ ?_ program init ⟨hinit, by omega⟩
    · intro state _
      exact le_add_self
    · rintro input state ⟨hi, hp⟩ answer after hmem
      exact ⟨hpreserve input state hi hp answer after hmem,
        (hbound input state hi hp).probes_le hp _ hmem⟩
    · rintro input state ⟨hi, hp⟩
      exact payment54_of_stepBound step ch (2 ^ 128) q input state (hbound input state hi hp) (by positivity) (by omega) hp
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans ?_
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls init) (ch.probes init) (by positivity)
    (by omega) (by omega) (Nat.zero_le _) (by omega)
  unfold potential54
  rw [hmass, Nat.cast_zero, mul_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q

theorem residual_potential_54F {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    [ClaudeWCT.W9.T3.Security.FamResidual.Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell]
    [DecidableEq Cell] {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 121) (program : OracleComp (SigGolfCandidate.T3.Security.LargeResidual.World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q |
        ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] +
      (127 / 64 : ENNReal) * (∑' result,
        Pr[= result | ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] *
          (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_initial_54 (ClaudeWCT.W9.T3.Security.FamResidual.residualStep aux q)
    SigGolfCandidate.T3.Security.LargeResidual.charges q hq
    ClaudeWCT.W9.T3.Security.FamResidual.Inv
    (fun input state hinv _ answer after hafter =>
      ClaudeWCT.W9.T3.Security.FamResidual.residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => ClaudeWCT.W9.T3.Security.FamResidual.residual_step_bound aux q input state hinv)
    program SigGolfCandidate.T3.Security.LargeResidual.initial
    ClaudeWCT.W9.T3.Security.FamResidual.initial_inv rfl rfl
  rw [ClaudeWCT.W9.T3.Security.FamResidual.run_residual] at h
  exact h
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3.Security.LargeResidual
open ClaudeWCT.W9.T3.Security.FamResidual (residual_potential lazyRun)
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (largeBound excessRate excessRate54 cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
noncomputable abbrev lazyRouter (adversary : AdversaryP) (q : Nat) :=
  lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial
noncomputable def routerMass (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' r, Pr[= r | lazyRouter adversary q] * (r.2.counters.mass : ENNReal)
/-- The certificate branch of the large route, together with the FTS overflow term `2^-137` (A6, A5). -/
def LargeCertBound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : Prop :=
  Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧
      NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] +
      ((2 : ENNReal) ^ 137)⁻¹ ≤
    (if q ≤ 2 ^ 121 then 127 / 64 else 1) * routerMass adversary q / 2 ^ 128 +
      (q : ENNReal) * (if q ≤ 2 ^ 121 then excessRate54 else excessRate) / 2 ^ 128 +
      (q : ENNReal) * cacheRate / 2 ^ 128 +
      (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute
theorem large_route_of_cert (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcert : LargeCertBound adversary q hq) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  apply ClaudeWCT.W9.T3.Security.SeccClosingW9.largeBound_of_parts q _
    (Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q]) _ (routerMass adversary q)
  · have hno := ClaudeWCT.W9.T3.Security.cleanWin_logOverflow_le adversary q hq
    have h1 : Pr[fun z => QueryRecorded.CleanWin q z.1 | SeccLaw.completedExperiment adversary q hq] ≤
        Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
          SeccLaw.completedExperiment adversary q hq] +
        Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
          SeccLaw.completedExperiment adversary q hq] := by
      refine le_trans (Wots.Ref.pmf_probEvent_mono _ fun z _ h => ?_) (probEvent_or_le _ _ _)
      by_cases hn : NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
      · exact Or.inl ⟨h, hn⟩
      · exact Or.inr ⟨h, hn⟩
    have h2 := ClaudeWCT.W9.T3.Security.SeccClosingW9.probEvent_le_contact_add (SeccLaw.completedExperiment adversary q hq)
      (fun z => QueryRecorded.CleanWin q z.1 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2)
      (Contact adversary q) (fun z => NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) (fun _ h => h.2)
    have h3 : Pr[fun z => NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 ∧ Contact adversary q z |
        SeccLaw.completedExperiment adversary q hq] ≤
        Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q] :=
      le_trans (probEvent_mono'' fun z hz => ⟨hz.2, hz.1⟩) (contact_le_lazy adversary q hq)
    have h4 : Pr[fun z => (QueryRecorded.CleanWin q z.1 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) ∧
        ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
        Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧
          NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] :=
      probEvent_mono'' fun z hz => ⟨hz.1.1, hz.2, hz.1.2⟩
    have h5 : Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] ≤ ((2 : ENNReal) ^ 137)⁻¹ := hno
    calc _ ≤ _ := h1
      _ ≤ (Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧
            NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq]) +
          ((2 : ENNReal) ^ 137)⁻¹ := add_le_add (h2.trans (add_le_add h3 h4)) h5
      _ = _ := by rw [add_assoc]
  · by_cases h125 : q ≤ 2 ^ 121
    · rw [if_pos h125]
      exact residual_potential_54F (auxLaw initLaw) q h125 _
    · rw [if_neg h125, one_mul]
      exact residual_potential (auxLaw initLaw) q hq _
  · exact hcert
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_noFail)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (largeBound excessRate excessRate54 cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Bank
variable {U : Finset HashInput}
noncomputable def psiOut (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi q st
  | _ => 0
theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert q st hc
  · exact zero_le
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * (if q ≤ 2 ^ 121 then 23 / 100000 else 247 / 100000) / 2 ^ 128 +
        coeffQ q * (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut q r + slackT q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi q)
  set S := expectedValue L (fun r => slackT q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : coeffQ q * (q : ENNReal) / 2 ^ 128 ≤ S + coeffQ q * Mass / 2 ^ 128 := by
    have hMass' : coeffQ q * Mass / 2 ^ 128 =
        expectedValue L (fun r => coeffQ q * (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      rw [expectedValue_def]
      apply tsum_congr
      intro r
      ring
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail (coeffQ q * (q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div, ← mul_add, ← Nat.cast_add]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' le_rfl
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hcoeff_fin : coeffQ q ≠ ⊤ := by unfold coeffQ; split_ifs <;> finiteness
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := coeffQ q * (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top hcoeff_fin (ENNReal.natCast_ne_top q)) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      apply mul_le_mul' le_rfl
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut q) + S ≤ (psi q RouterState.initial + coeffQ q * Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi q RouterState.initial + coeffQ q * (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi q RouterState.initial + (S + coeffQ q * Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut q) := hcert
    _ ≤ psi q RouterState.initial + coeffQ q * Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial q) le_rfl
end Bank
theorem large_cert_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : LargeCertBound adversary q hq := by
  unfold LargeCertBound
  have hsplit : Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧
      NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z ∧ BPB.SignerComplete z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] := by
    refine le_trans (Wots.Ref.pmf_probEvent_mono _ fun z _ h => ?_) (probEvent_or_le _ _ _)
    by_cases hcomp : BPB.SignerComplete z.2
    · exact Or.inl ⟨h.1, h.2.1, hcomp, h.2.2⟩
    · exact Or.inr hcomp
  have hsi : Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      ((2 : ENNReal) ^ 137)⁻¹ :=
    (BPB.signerIncomplete_le adversary q hq).trans
      (by rw [one_div]; exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by norm_num)))
  have habs : ((2 : ENNReal) ^ 137)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹ ≤ largeReserveAbsolute := by
    rw [ClaudeWCT.W9.T3.Security.SeccClosingW9.largeReserveAbsolute_def]
    calc ((2 : ENNReal) ^ 137)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹ = ((2 : ENNReal) ^ 136)⁻¹ := by
          rw [← two_mul, show (2 : ENNReal) ^ 137 = 2 * 2 ^ 136 by rw [← pow_succ']]
          rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by norm_num))
  have hmain := add_le_add (hsplit.trans (add_le_add ((cert_le_lazy adversary q hq).trans
    (bank_cert_le (Wots.Ref.referenceInputs_universe adversary) initLaw adversary q)) hsi))
    (le_refl (((2 : ENNReal) ^ 137)⁻¹))
  refine (hmain.trans (le_of_eq (add_assoc _ _ _))).trans ((add_le_add le_rfl habs).trans ?_)
  have hrm : (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
      LargeResidual.initial] * (r.2.counters.mass : ENNReal)) = routerMass adversary q := rfl
  have hexc_eq : (if q ≤ 2 ^ 121 then (23 / 100000 : ENNReal) else 247 / 100000) =
      (if q ≤ 2 ^ 121 then excessRate54 else excessRate) := by
    rw [ClaudeWCT.W9.T3.Security.SeccClosingW9.excessRate54_def,
      ClaudeWCT.W9.T3.Security.SeccClosingW9.excessRate_def]
  rw [hrm, hexc_eq]
  unfold coeffQ
  calc
    _ = (if q ≤ 2 ^ 121 then 127 / 64 else 1) * routerMass adversary q / 2 ^ 128 +
        (q : ENNReal) * (if q ≤ 2 ^ 121 then excessRate54 else excessRate) / 2 ^ 128 + largeReserveAbsolute := by
      rw [add_comm ((q : ENNReal) * (if q ≤ 2 ^ 121 then excessRate54 else excessRate) / 2 ^ 128)]
    _ ≤ _ := add_le_add (le_add_right (le_add_right le_rfl)) le_rfl
theorem large_route (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  large_route_of_cert adversary q hq (large_cert_bound adversary q hq)
theorem large_route_hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), ClaudeWCT.W9.T3.Security.SeccClosingW9.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  fun adversary q hq _ => large_route adversary q hq
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

/-!
A variable charge for fresh message opportunities.  The existing fixed-rate
security closure above is preserved; these lemmas expose the full payment
available from the same primitive-message potential.
-/
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Flexible
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep TestStep ProbeStep
  continuation hazard terminal expected_stop_le continuation_anti continuation_pay continuation_probe
  initial_potential run_expected_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem message_payment_rate (ρ space budget probes remaining : ℝ) (hspace : 0 < space)
    (hρ0 : 0 ≤ ρ) (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : probes + remaining + 1 ≤ budget) (hhalf : 2 * budget ≤ space)
    (hrate : ρ * space ≤ 2 * (space - budget)) :
    ρ / space + PrimitiveMessagePotential.value space probes remaining ≤
      PrimitiveMessagePotential.value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : ρ * space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : ρ / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      ρ / space = (ρ * space) / space ^ 2 := by field_simp
      _ ≤ (ρ * space) / (space - probes) ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hρ0 hspace.le) (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← PrimitiveMessagePotential.message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith

theorem continuation_pay_rate (ρ : ℝ) (space q calls probes : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (space : ℝ) ≤ 2 * ((space : ℝ) - q))
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + ENNReal.ofReal ρ / space ≤
      continuation space q calls probes := by
  have hs : (0 : ℝ) < space := by exact_mod_cast hspace
  have hb : 2 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have hp : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := message_payment_rate ρ space q probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs hρ0
    (by positivity) (by push_cast; linarith) (by push_cast; linarith) hb hρ
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  have hof : ENNReal.ofReal (ρ / space) = ENNReal.ofReal ρ / space := by
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (div_nonneg hρ0 hs.le) hv, hof] at hfinal
  rw [add_comm]
  exact hfinal

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
  [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

noncomputable def potential (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space
noncomputable def stopValue (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space
noncomputable def doneValue (ρ : ℝ) {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space

theorem terminal_le_of_over (ρ : ℝ) {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
      (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (ENNReal.ofReal ρ) * (ch.mass result.2 : ENNReal) / space ≤
      (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue, hnot] using hm
  · simpa [terminal, potential, continuation, hnot] using hm

theorem payment_of_stepBound (ρ : ℝ) {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (input : spec.Domain) (state : σ) (h : StepBound step ch space q input state)
    (hspace : 0 < space) (hq2 : 2 * q ≤ space) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (space : ℝ) ≤ 2 * ((space : ℝ) - q)) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ρ ch space q) (potential ρ ch space q)) ≤
      potential ρ ch space q state := by
  have hq : 2 * q ≤ space := hq2
  rcases h with h | h | h | h
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential]
    exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
      (ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _)
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    by_cases hc : ch.calls state + 1 ≤ q
    · rw [if_pos hc] at hmass
      have hsome : answer ≠ none := by
        have := (probEvent_eq_zero_iff.mp h.2) _ hresult
        simpa using this
      obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
      simp only [terminal, Option.elim_some, potential]
      have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
        (ch.probes after) hspace hq (by omega) hcalls hp
      have hpay := continuation_pay_rate ρ space q (ch.calls state) (ch.probes state) hspace hq2 hρ0 hρ hprobes hc
      have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
          (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space + (ENNReal.ofReal ρ) / space := by
        rw [← ENNReal.add_div]
        apply ENNReal.div_le_div_right
        calc
          (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) ≤
              (ENNReal.ofReal ρ) * ((ch.mass state + 1 : Nat) : ENNReal) :=
            mul_le_mul' le_rfl (by exact_mod_cast hmass)
          _ = (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) + (ENNReal.ofReal ρ) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      calc
        _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
            ((ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space + (ENNReal.ofReal ρ) / space) :=
          add_le_add hcont hm
        _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (ENNReal.ofReal ρ) / space) +
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by ring
        _ ≤ _ := add_le_add hpay le_rfl
    · rw [if_neg hc, add_zero] at hmass
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
          refine add_le_add (add_le_add h.2 ?_) le_rfl
          exact mul_le_of_le_one_left' tsub_le_self
        _ ≤ _ := by
          rw [add_comm ((space : ENNReal)⁻¹)]
          exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue ρ ch space q) (potential ρ ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (ENNReal.ofReal ρ) * (ch.mass after : ENNReal) / space ≤
            (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state + 1) +
              (ENNReal.ofReal ρ) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal_le_of_over ρ ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

theorem stop_add_mass_eq (ρ : ℝ) {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue ρ ch space q) (doneValue ρ ch space)) := by
  have hfun : terminal (stopValue ρ ch space q) (doneValue ρ ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) +
        (ENNReal.ofReal ρ) * (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue]
    · simp [terminal, doneValue]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro result
  ring

theorem run_potential_initial (ρ : ℝ) {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq2 : q ≤ 2 ^ 127) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (2 ^ 128 : ℝ) ≤ 2 * ((2 ^ 128 : ℝ) - q)) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h : Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (ENNReal.ofReal ρ) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / ((2 ^ 128 : Nat) : ENNReal) ≤
      potential ρ ch (2 ^ 128) q init := by
    rw [stop_add_mass_eq ρ]
    refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
      (potential ρ ch (2 ^ 128) q) (stopValue ρ ch (2 ^ 128) q) (doneValue ρ ch (2 ^ 128))
      ?_ ?_ ?_ program init ⟨hinit, by omega⟩
    · intro state _
      exact le_add_self
    · rintro input state ⟨hi, hp⟩ answer after hmem
      exact ⟨hpreserve input state hi hp answer after hmem,
        (hbound input state hi hp).probes_le hp _ hmem⟩
    · rintro input state ⟨hi, hp⟩
      exact payment_of_stepBound ρ step ch (2 ^ 128) q input state (hbound input state hi hp) (by positivity) (by omega) hρ0 (by convert hρ using 1 <;> norm_num) hp
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans ?_
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls init) (ch.probes init) (by positivity)
    (by omega) (by omega) (Nat.zero_le _) (by omega)
  unfold potential
  rw [hmass, Nat.cast_zero, mul_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q

theorem residual_potential_rate (ρ : ℝ) {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    [ClaudeWCT.W9.T3.Security.FamResidual.Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell]
    [DecidableEq Cell] {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 127) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (2 ^ 128 : ℝ) ≤ 2 * ((2 ^ 128 : ℝ) - q)) (program : OracleComp (SigGolfCandidate.T3.Security.LargeResidual.World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q |
        ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] +
      ENNReal.ofReal ρ * (∑' result,
        Pr[= result | ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] *
          (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_initial ρ (ClaudeWCT.W9.T3.Security.FamResidual.residualStep aux q)
    SigGolfCandidate.T3.Security.LargeResidual.charges q hq hρ0 hρ
    ClaudeWCT.W9.T3.Security.FamResidual.Inv
    (fun input state hinv _ answer after hafter =>
      ClaudeWCT.W9.T3.Security.FamResidual.residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => ClaudeWCT.W9.T3.Security.FamResidual.residual_step_bound aux q input state hinv)
    program SigGolfCandidate.T3.Security.LargeResidual.initial
    ClaudeWCT.W9.T3.Security.FamResidual.initial_inv rfl rfl
  rw [ClaudeWCT.W9.T3.Security.FamResidual.run_residual] at h
  exact h
/-- The maximal convenient linear payment used by the continuous schedule. -/
noncomputable def budgetRate (q : Nat) : ℝ := 2 - 2 * (q : ℝ) / 2 ^ 128

theorem budgetRate_nonneg (q : Nat) (hq : q ≤ 2 ^ 127) : 0 ≤ budgetRate q := by
  have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  unfold budgetRate
  have hdiv : 2 * (q : ℝ) / 2 ^ 128 ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ 128)).mpr
    calc
      (2:ℝ)*(q:ℝ) ≤ 2*(2^127) := mul_le_mul_of_nonneg_left hq' (by norm_num)
      _ = 2^128 := by norm_num
  linarith

theorem budgetRate_mul (q : Nat) :
    budgetRate q * (2 ^ 128 : ℝ) = 2 * ((2 ^ 128 : ℝ) - q) := by
  unfold budgetRate
  field_simp <;> ring

end ClaudeWCT.W9.T3.Security.LargeCoupling.Flexible
end

/-! Bank forecasts with an arbitrary stop-loss threshold. -/
section
namespace ClaudeWCT.Bank.WCT.Flexible
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.Bank.WCT
open CaseC (BankCore BankCore.expose)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable (θ : ENNReal) (horizon : Nat)
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ W) - θ)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue (S0 horizon).accepted (fun A => excessForecast θ horizon R (X ++ [A])) =
      excessForecast θ horizon (R + 1) X := by
  unfold excessForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
      (fun W => (S0 horizon).price ((S0 horizon).proposals (X ++ [A]) ++ W) - θ) =
      (fun p : WProposal => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
        (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - θ))
        ((S0 horizon).proposal A) := by
    simp [FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact (S0 horizon).expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
    (fun W => (S0 horizon).price ((S0 horizon).proposals X ++ p :: W) - θ))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => (S0 horizon).forecast R X N) ≤
      (θ + excessForecast θ horizon R X) / 2 ^ 128 := by
  rw [(S0 horizon).average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ ClaudeWCT.Numerics.Law.lawAvg (S0 horizon).law R
          (fun W => θ + ((S0 horizon).price ((S0 horizon).proposals X ++ W) - θ)) :=
      ClaudeWCT.Numerics.Law.lawAvg_mono (S0 horizon).law R fun W => le_add_tsub
    _ = _ := by
      rw [ClaudeWCT.Numerics.Law.lawAvg_add, ClaudeWCT.Numerics.Law.lawAvg_const (S0 horizon).law (S0 horizon).law_sum]
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => (S0 horizon).forecast R X N).sum + (slack : ENNReal) * excessForecast θ horizon R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    ledger θ horizon R targets X (slack + 1) =
      ledger θ horizon R targets X slack + excessForecast θ horizon R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => ledger θ horizon R (targets ++ [a]) X slack) ≤
      ledger θ horizon R targets X (slack + 1) + θ / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => (S0 horizon).forecast R X a) ≤
      (θ + excessForecast θ horizon R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_forecast_le θ horizon R X
  have hsplit : ∀ a, ledger θ horizon R (targets ++ [a]) X slack =
      ledger θ horizon R targets X slack + (S0 horizon).forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ θ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (S0 horizon).accepted (fun A => ledger θ horizon R targets (X ++ [A]) slack) =
      ledger θ horizon (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  refine congrArg₂ (· + ·) (congrArg List.sum ?_) ?_
  · apply List.map_congr_left
    intro N _
    exact (S0 horizon).forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * excessForecast θ horizon R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * excessForecast θ horizon R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, excessForecast_step θ]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    (S0 horizon).freshPrice (fun A => ledger θ horizon R targets (X ++ [A]) slack) =
      ledger θ horizon (R + 1) targets X slack := by
  rw [← (S0 horizon).expected_accepted, ledger_expose θ]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) (S0 horizon).decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret ((S0 horizon).search rho message 0 fuel) cache)
      (fun result => result.1.elim (ledger θ horizon (R + 1) targets X slack)
        (fun found => ledger θ horizon R targets (X ++ [found.2]) slack)) ≤
      ledger θ horizon (R + 1) targets X slack :=
  (S0 horizon).search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (ledger_freshPrice θ horizon R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Covered X N) :
    1 ≤ ledger θ horizon R targets X slack :=
  calc
    (1 : ENNReal) ≤ (S0 horizon).score X N := (S0 horizon).one_le_score X N hadm hcov
    _ ≤ (S0 horizon).forecast R X N := (S0 horizon).score_le_forecast R X N
    _ ≤ (targets.map fun N => (S0 horizon).forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger θ horizon (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + (S0 horizon).admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => corePotential θ horizon { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      corePotential θ horizon b + (θ + (S0 horizon).admBound) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => (S0 horizon).admInd N / 2 ^ 128) ≤
      (S0 horizon).admBound / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using (S0 horizon).expected_admInd_tight) le_rfl
  have h54_adm : (S0 horizon).admBound ≤ θ + (S0 horizon).admBound := le_add_self
  have h54_sum : θ + (S0 horizon).admBound ≤ θ + (S0 horizon).admBound := le_rfl
  unfold corePotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun N => (S0 horizon).admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (S0 horizon).admBound / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_adm _)
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (ledger θ horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => ledger θ horizon R (b.targets ++ [N]) b.exposures s + (S0 horizon).admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (ledger θ horizon R b.targets b.exposures (s + 1) + θ / 2 ^ 128 +
            (S0 horizon).admBound / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (ledger_birth θ horizon R b.targets b.exposures s) hadm) le_rfl
      _ ≤ _ := by
        rw [← hs, add_assoc (ledger θ _ _ _ _ _), ← ENNReal.add_div,
          show ledger θ horizon R b.targets b.exposures b.slack +
            (θ + (S0 horizon).admBound) / 2 ^ 128 + b.reuse =
            (ledger θ horizon R b.targets b.exposures b.slack + b.reuse) +
            (θ + (S0 horizon).admBound) / 2 ^ 128 by ring]
        exact add_le_add le_rfl (ENNReal.div_le_div_right h54_sum _)
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + (S0 horizon).reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then
        corePotential θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (WCT9.digestSearch rho m 0 fuel) cache)
        (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential θ horizon b := by
  have h : expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if (S0 horizon).Reuse cache rho m then corePotential θ horizon { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
        (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd)))) ≤
      corePotential θ horizon b := by
    have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
      intro o; simp
    by_cases hd : horizon < b.exposures.length
    · apply expectedValue_le_of_le
      intro rho
      have h0 : ∀ (o : Option HashOutput), corePotential θ horizon (b.expose C' o) = 0 := by
        intro o
        unfold corePotential BankCore.expose
        simp only
        rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
      split_ifs
      · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
      · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
    by_cases hr : b.reused = true
    · have hb : corePotential θ horizon b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
      rw [hb]
      apply expectedValue_le_of_le
      intro rho
      have hle : ∀ (o : Option HashOutput), corePotential θ horizon (b.expose C' o) ≤ 1 + b.reuse := by
        intro o
        unfold corePotential BankCore.expose
        simp only [hr, if_true]
        split_ifs
        · exact bot_le
        · exact add_le_add le_rfl (le_of_add_le_left hC)
      split_ifs
      · unfold corePotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
      · exact expectedValue_le_of_le _ fun result => hle _
    have hr' : b.reused = false := by simpa using hr
    set R0 := horizon - b.exposures.length with hR0
    have hb : corePotential θ horizon b = ledger θ horizon R0 b.targets b.exposures b.slack + b.reuse := by
      unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
    have hsearch : ∀ rho, ¬(S0 horizon).Reuse cache rho m →
        expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
          (fun result => corePotential θ horizon (b.expose C' (result.1.map Prod.snd))) ≤
            ledger θ horizon R0 b.targets b.exposures b.slack + C' := by
      intro rho hnr
      have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) (S0 horizon).decode 0 (2 ^ 32) cache := by
        unfold FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
      by_cases hlen : b.exposures.length < horizon
      · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
        calc
          _ ≤ expectedValue (Sampling.roRun secret ((S0 horizon).search rho m 0 fuel) cache)
              (fun result => result.1.elim (ledger θ horizon (R + 1) b.targets b.exposures b.slack)
                (fun found => ledger θ horizon R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
            apply expectedValue_mono
            intro result
            rcases result with ⟨_ | found, cache'⟩
            · unfold corePotential BankCore.expose
              simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
                Bool.false_eq_true, Option.elim_none]
              rw [← hR]
            · unfold corePotential BankCore.expose
              have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
              have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by omega
              simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
                Option.elim_some]
              rw [show horizon - (b.exposures ++ [found.2]).length = R by omega]
          _ ≤ ledger θ horizon (R + 1) b.targets b.exposures b.slack + C' :=
            (CaseC.expectedValue_add_const_le _ _ _).trans
              (add_le_add (ledger_search θ horizon secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
          _ = _ := by rw [hR]
      · apply expectedValue_le_of_le
        intro result
        rcases result with ⟨_ | found, cache'⟩
        · unfold corePotential BankCore.expose
          simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
          exact le_rfl
        · unfold corePotential BankCore.expose
          have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
          simp only [Option.map_some, Option.toList_some, hnd, if_true]
          exact bot_le
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
          (fun rho => (if (S0 horizon).Reuse cache rho m then 1 else 0) +
            (ledger θ horizon R0 b.targets b.exposures b.slack + C')) := by
        apply expectedValue_mono
        intro rho
        by_cases hre : (S0 horizon).Reuse cache rho m
        · rw [if_pos hre, if_pos hre]
          unfold corePotential
          simp only [hd, if_false, if_true]
          exact add_le_add le_rfl le_add_self
        · rw [if_neg hre, if_neg hre, zero_add]
          exact hsearch rho hre
      _ ≤ (S0 horizon).reuseMass cache m + (ledger θ horizon R0 b.targets b.exposures b.slack + C') :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add ((S0 horizon).reuse_probability_le cache m) le_rfl)
      _ ≤ _ := by
        rw [add_comm (ledger θ _ _ _ _ _), ← add_assoc, add_comm ((S0 horizon).reuseMass cache m),
          add_comm _ (ledger θ _ _ _ _ _)]
        exact add_le_add le_rfl hC
  simp only [← wct_digestSearch_public (S0 horizon) rfl] at h
  exact h
theorem core_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Covered b.exposures N) :
    1 ≤ corePotential θ horizon b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (ledger_win θ horizon _ _ _ _ N hN hadm hcov).trans le_self_add
theorem core_initial (rate : ENNReal) (hexc : ExcessBoundAt (2 ^ 32) θ rate) (budget : Nat) :
    corePotential θ (2 ^ 32) ⟨[], [], false, 0, budget⟩ ≤
      (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold corePotential ledger excessForecast
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero,
    List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact hexc
end ClaudeWCT.Bank.WCT.Flexible
end


namespace ClaudeWCT.Bank.FlexibleGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open CaseC (IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P) (θ : ENNReal)
variable {Sig : Type}

noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => S.price (S.proposals X ++ W)-θ)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue S.accepted (fun A => excessForecast S θ R (X ++ [A])) =
      excessForecast S θ (R+1) X :=
  Flexible.excessForecast_step S.toFtsBankSpec θ S.horizon R X
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) ≤
      (θ+excessForecast S θ R X)/2^128 :=
  Flexible.average_forecast_le S.toFtsBankSpec θ S.horizon R X

noncomputable def birthCharge (budget : Nat) : (Interaction' Sig).Domain → BankState Sig → ENNReal
  | .inl (.inr x), st => if Birth budget x st.2 then (θ+S.admBound)/2^128 else 0
  | _, _ => 0
theorem birthCharge_eq (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    birthCharge S θ budget input st = (θ+S.admBound)/2^128*birthWeight budget input st.2 := by
  rcases input with (n|x)|request
  · simp [birthCharge,birthWeight]
  · simp only [birthCharge,birthWeight]
    split_ifs <;> simp
  · simp [birthCharge,birthWeight]
noncomputable def excessTerm (budget count : Nat) (g : Ghost Sig) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * (excessForecast S θ) (S.horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + S.reusePotential lazy
  else S.bankValue g + S.reusePotential lazy + (excessTerm S θ) budget count g
noncomputable def potential (budget : Nat) (st : BankState Sig) : ENNReal :=
  (livePotential S θ) budget (countOf st.2) st.1 (lazyOf st.2)
theorem livePotential_count_anti (budget : Nat) {count count' : Nat} (h : count ≤ count') (g : Ghost Sig)
    (lazy : LazyPrivate.State) : (livePotential S θ) budget count' g lazy ≤ (livePotential S θ) budget count g lazy := by
  unfold livePotential
  by_cases hd : g.dead = true
  · simp [hd]
  by_cases hb : budget < count'
  · simp [hd, hb]
  have hb0 : ¬budget < count := by omega
  have hd' : g.dead = false := by simpa using hd
  simp only [hd', hb, hb0, Bool.false_eq_true, false_or, if_false]
  by_cases hr : g.reused = true
  · simp only [hr, if_true, le_refl]
  · simp only [hr]
    apply add_le_add le_rfl
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast Nat.sub_le_sub_left h budget
theorem livePotential_alive (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = false) :
    (livePotential S θ) budget count g lazy = S.bankValue g + S.reusePotential lazy + (excessTerm S θ) budget count g := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reused (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = true) :
    (livePotential S θ) budget count g lazy = 1 + S.reusePotential lazy := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reuse_mono (budget count : Nat) (g : Ghost Sig) {lazy lazy' : LazyPrivate.State}
    (h : S.reusePotential lazy' ≤ S.reusePotential lazy) :
    (livePotential S θ) budget count g lazy' ≤ (livePotential S θ) budget count g lazy := by
  unfold livePotential
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h
  · exact add_le_add (add_le_add le_rfl h) le_rfl
theorem excessTerm_succ (budget count : Nat) (g : Ghost Sig) (hc : count < budget) :
    (excessTerm S θ) budget count g = (excessTerm S θ) budget (count + 1) g +
      (excessForecast S θ) (S.horizon - g.exposures.length) g.exposures / 2 ^ 128 := by
  unfold excessTerm
  have hn : budget - count = (budget - (count + 1)) + 1 := by omega
  rw [hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]
theorem livePotential_log (budget count : Nat) (g : Ghost Sig) (l : QueryLog (Requests' Sig))
    (lazy : LazyPrivate.State) :
    (livePotential S θ) budget count { g with log := l } lazy = (livePotential S θ) budget count g lazy := rfl
noncomputable def signWeight (budget count : Nat) (g : Ghost Sig) (A : HashOutput) : ENNReal :=
  S.bankValue { g with exposures := g.exposures ++ [A] } +
    (excessTerm S θ) budget count { g with exposures := g.exposures ++ [A] }
theorem freshPrice_signWeight (budget count : Nat) (g : Ghost Sig) (hlen : g.exposures.length < S.horizon) :
    S.freshPrice ((signWeight S θ) budget count g) = S.bankValue g + (excessTerm S θ) budget count g := by
  rw [← S.expected_accepted]
  have hR' : ∀ A : HashOutput, S.horizon - (g.exposures ++ [A]).length = S.horizon - g.exposures.length - 1 := by
    intro A
    simp only [List.length_append, List.length_singleton]
    omega
  have hRR : S.horizon - g.exposures.length - 1 + 1 = S.horizon - g.exposures.length := by omega
  unfold signWeight FtsBankSpec.bankValue excessTerm
  rw [expectedValue_add]
  simp only [hR']
  rw [CaseC.expectedValue_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    rw [S.forecast_step, hRR]
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => ((budget - count : Nat) : ENNReal) *
        (excessForecast S θ) (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => ((budget - count : Nat) : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ *
          (excessForecast S θ) (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, (excessForecast_step S θ), hRR]
    ring
theorem potential_initial_le_rate (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    (potential S θ) budget ((Ghost.empty : Ghost Sig), generated.2) ≤ (budget : ENNReal) * rate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [FtsBankSpec.bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he : (excessForecast S θ) S.horizon [] ≤ rate := by
        unfold excessForecast
        simpa [FtsBankSpec.proposals] using hrate
      simpa [Ghost.empty] using he

variable (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + (birthCharge S θ) budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st ((potential S θ) budget)]
  cases input with
  | inl n =>
      have hb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change (livePotential S θ) budget (countOf r.2) st.1 (lazyOf r.2) ≤
        (livePotential S θ) budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact (livePotential_count_anti S θ) budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change (livePotential S θ) budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => (livePotential S θ) budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact (livePotential_count_anti S θ) budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = (θ + S.admBound) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : (potential S θ) budget st = 1 + S.reusePotential lz :=
                (livePotential_reused S θ) budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [(livePotential_reused S θ) budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + S.admBound / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : (potential S θ) budget st = S.bankValue g + S.reusePotential lz + (excessTerm S θ) budget c g :=
                (livePotential_alive S θ) budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (θ + (excessForecast S θ) R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact (average_forecast_le S θ) R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      (excessTerm S θ) budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [(livePotential_alive S θ) budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    (excessTerm S θ) budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (θ + (excessForecast S θ) R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + S.admBound / 2 ^ 128) + (excessTerm S θ) budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    ((excessTerm S θ) budget (c + 1) g + (excessForecast S θ) R g.exposures / 2 ^ 128) +
                    (θ + S.admBound) / 2 ^ 128 := by
                  rw [ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← (excessTerm_succ S θ) budget c g hlt]
          · have hcb : (birthCharge (Sig := Sig) S θ) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ (livePotential S θ) budget (c + 1) g lz :=
                  (livePotential_reuse_mono S θ) budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ (livePotential S θ) budget c g lz := (livePotential_count_anti S θ) budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [livePotential, hover]
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => (potential S θ) budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => (potential S θ) budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change (livePotential S θ) budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact (livePotential_count_anti S θ) budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => (livePotential S θ) budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ (potential S θ) budget st := ?_
  change _ ≤ (livePotential S θ) budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [FtsBankSpec.ghostSign, hfresh, if_false, livePotential_log]
    apply (livePotential_reuse_mono S θ)
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [(livePotential_reused S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      (livePotential_reused S θ) budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + (excessTerm S θ) budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' ((signWeight S θ) budget c g)
  have hpoint : ∀ r, (livePotential S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [(livePotential_reused S θ) budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [(livePotential_alive S θ) budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.bankValue; rw [htar r, hexp r]
      have het : (excessTerm S θ) budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          (excessTerm S θ) budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain ((signWeight S θ) budget c g) P'
        (le_of_eq ((freshPrice_signWeight S θ) budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = (livePotential S θ) budget c g lz := by
      rw [(livePotential_alive S θ) budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + (birthCharge S θ) budget input st := by
  cases input with
  | inl input => exact (world_step S θ) pay published budget input st
  | inr request => exact ((sign_step S θ) pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => (potential S θ) budget r.2) ≤
      (potential S θ) budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        ((birthCharge S θ) budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            (potential S θ) budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              ((birthCharge S θ) budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => (potential S θ) budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                ((birthCharge S θ) budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ ((potential S θ) budget st + (birthCharge S θ) budget input st) + _ :=
          add_le_add ((potential_step S θ) pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) ((birthCharge S θ) budget) program (g, s) =
      (θ + S.admBound) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) ((birthCharge S θ) budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (θ + S.admBound) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact (birthCharge_eq S θ) budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
theorem potential_win (budget : Nat) (st : BankState Sig) (halive : st.1.dead = false)
    (hcount : countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, S.admissible N = true ∧ S.covered st.1.exposures N) :
    1 ≤ (potential S θ) budget st := by
  have hnot : ¬budget < countOf st.2 := by omega
  unfold potential
  by_cases hr : st.1.reused = true
  · rw [(livePotential_reused S θ) budget _ st.1 _ halive hnot hr]
    exact le_add_right le_rfl
  · have hr' : st.1.reused = false := by simpa using hr
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    rw [(livePotential_alive S θ) budget _ st.1 _ halive hnot hr']
    calc
      (1 : ENNReal) ≤ S.score st.1.exposures N := S.one_le_score _ N hadm hcov
      _ ≤ S.forecast (S.horizon - st.1.exposures.length) st.1.exposures N := S.score_le_forecast _ _ _
      _ ≤ S.bankValue st.1 := List.le_sum_of_mem (List.mem_map_of_mem hN)
      _ ≤ _ := le_self_add.trans le_self_add
theorem bank_potential_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => (potential S θ) budget r.2) ≤
      (θ + S.admBound) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold FtsBankSpecL.bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * rate / 2 ^ 128 +
          (θ + S.admBound) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine ((potential_run S θ) pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [(bank_charges_eq_births S θ) pay generated.1.2 budget]
      exact add_le_add ((potential_initial_le_rate S θ) budget rate hrate generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold FtsBankSpecL.expectedBirths
      ring
theorem bank_event_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - θ) ≤ rate)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ (potential S θ) budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (θ + S.admBound) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ ((bank_potential_le_rate S θ) pay hNotDigest hAvoids rest budget rate hrate)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)

#print axioms bank_event_le_rate
#print axioms potential_win
end ClaudeWCT.Bank.FlexibleGame

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

noncomputable def flexiblePotential (θ : ENNReal) (budget : Nat)
    (state : BankState SharedForest.Signature) : ENNReal :=
  FlexibleGame.potential bankSpec θ budget state

theorem flexible_event_le (θ rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg honestLaw (2^32) (fun W => price W-θ)≤rate)
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool)
    (budget : Nat) (weight : Bool × QueryRecorded.State → ENNReal)
    (hw : ∀ y,weight y≤1)
    (hwin : ∀ b∈(bankSpec.bankExperiment payAfterDigest rest budget).support,
      weight (b.1,b.2.2)≠0 → 1≤flexiblePotential θ budget b.2) :
    expectedValue (bankSpec.recordedExperiment payAfterDigest rest) weight ≤
      (θ+1/1024)/2^128*bankSpec.expectedBirths payAfterDigest rest budget+
      (budget:ENNReal)*rate/2^128 :=
  FlexibleGame.bank_event_le_rate bankSpec θ payAfterDigest payNotDigest payAvoids
    rest budget rate hexc weight hw hwin

theorem flexible_potential_win (θ : ENNReal) (budget : Nat) (state : BankState SharedForest.Signature)
    (halive : state.1.dead=false) (hcount : CaseC.countOf state.2≤budget)
    (h : state.1.reused=true ∨ ∃ N∈state.1.targets,admissible N=true ∧ Covered state.1.exposures N) :
    1≤flexiblePotential θ budget state :=
  FlexibleGame.potential_win bankSpec θ budget state halive hcount h

theorem bankInv_experiment
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool)
    (budget : Nat) (b : Bool × BankState SharedForest.Signature)
    (hb : b∈(bankSpec.bankExperiment payAfterDigest rest budget).support) :
    ∃ generated∈support (QueryRecorded.run keygen QueryRecorded.initial),
      bankSpec.BankInv payAfterDigest SharedForest.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  bankSpec.bankInv_experiment payAfterDigest SharedForest.Signature.rho payHashOnly payRho payAvoids
    rest budget b hb

#print axioms flexible_event_le
#print axioms flexible_potential_win
#print axioms bankInv_experiment
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.NearMemory
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le DigestRowOf
  digestRowOf_unique tsum_indicator_le_of_subsingleton)
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable abbrev nearPotential : BankCore → ENNReal := Flexible.corePotential S 0 (2^32)
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack=s+1) (C' : HashOutput → ENNReal)
    (hC : ∀ N,C' N≤b.reuse+S.admInd N/2^128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun N => nearPotential S {b with targets:=b.targets++[N],slack:=s,reuse:=C' N}) ≤
      nearPotential S b+S.admBound/2^128 := by
  simpa only [zero_add] using Flexible.core_birth S 0 (2^32) b s hs C' hC

theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C'+S.reuseMass cache m≤b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel≤2^32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then nearPotential S {b with reused:=true,reuse:=C'}
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun r => nearPotential S (b.expose C' (r.1.map Prod.snd)))) ≤ nearPotential S b :=
  Flexible.core_sign S 0 (2^32) b cache m C' hC secret fuel hfuel

theorem near_win (b : BankCore) (halive : ¬(2^32)<b.exposures.length)
    (h : b.reused=true ∨ ∃ N∈b.targets,S.admissible N=true ∧ S.covered b.exposures N) :
    1≤nearPotential S b := Flexible.core_win S 0 (2^32) b halive h

theorem near_initial (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate) (q : Nat) :
    nearPotential S ⟨[],[],false,0,q⟩≤(q:ENNReal)*rate/2^128 := by
  apply Flexible.core_initial S 0 rate
  simpa only [tsub_zero] using hrate
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then S.reuseMass rows m else 0
theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : (reuseC S) (rows.cacheQuery x a) nonces ≤ (reuseC S) rows nonces + S.admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then S.reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then S.reuseMass rows m else 0) +
          (if DigestRowOf x m then S.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using S.reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using S.reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → S.reuseMass rows' m' = S.reuseMass rows m') :
    (reuseC S) rows' (Function.update nonces m (some v)) + S.reuseMass rows m ≤ (reuseC S) rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then S.reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → S.reuseMass rows' m' = S.reuseMass rows m') :
    (reuseC S) rows' nonces = (reuseC S) rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]
theorem search_cache_frame {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      ∀ y, (∀ k, y ≠ inputs k) → r.2 y = cache y := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr y _
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | succ fuel ih =>
      intro counter cache r hr y hy
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfc : first.2 y = cache y := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            rw [hfirst]
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            rw [hfa]
            exact QueryCache.cacheQuery_of_ne cache a (hy counter)
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          exact (ih (counter + 1) first.2 r hr y hy).trans hfc
      | some value =>
          rw [hd] at hr
          change r ∈ support (Sampling.roRun secret (pure _) first.2) at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hfc
theorem digestSearch_cache_frame (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (S.search rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) S.decode _ fuel 0 cache r hr
theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m :=
    ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (S.search rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → S.reuseMass r.2 m' = S.reuseMass cache m' := by
  intro m' hm
  unfold ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [(digestSearch_cache_frame S) secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else (nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * (S.admBound / 2 ^ 128)
theorem mem_birth (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (x : HashInput) (hx : rows x = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun a : HashOutput => (nearMemPotential S) q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces) ≤
      (nearMemPotential S) q births exposures reused rows nonces := by
  by_cases hq : births.length < q
  · obtain ⟨s, hs⟩ : ∃ s, q - births.length = s + 1 := ⟨q - births.length - 1, by omega⟩
    have hb : (nearMemPotential S) q births exposures reused rows nonces =
        (nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ + ((s + 1 : Nat) : ENNReal) *
          (S.admBound / 2 ^ 128) := by
      unfold nearMemPotential
      rw [if_neg (by omega), hs]
    have ha : ∀ a : HashOutput, (nearMemPotential S) q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces =
        (nearPotential S) { (⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ : BankCore) with
          targets := births ++ [a], slack := s, reuse := (reuseC S) (rows.cacheQuery x a) nonces } +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := by
      intro a
      unfold nearMemPotential
      have hl : (births ++ [a]).length = births.length + 1 := by simp
      rw [if_neg (by omega), show q - (births ++ [a]).length = s by omega]
    simp_rw [ha]
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
            (nearPotential S) { (⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ : BankCore) with
              targets := births ++ [a], slack := s, reuse := (reuseC S) (rows.cacheQuery x a) nonces }) +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := expectedValue_add_const_le _ _ _
      _ ≤ ((nearPotential S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ + S.admBound / 2 ^ 128) +
          (s : ENNReal) * (S.admBound / 2 ^ 128) := by
        apply add_le_add _ le_rfl
        exact (near_birth S) ⟨births, exposures, reused, (reuseC S) rows nonces, s + 1⟩ s rfl _
          (fun a => (reuseC_birth_le S) rows nonces x a hx)
      _ = _ := by
        push_cast
        ring
  · apply expectedValue_le_of_le
    intro a
    unfold nearMemPotential
    rw [if_pos (by simp; omega)]
    exact bot_le
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
        (nearMemPotential S) q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (S.Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      (nearMemPotential S) q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · apply expectedValue_le_of_le
    intro v
    apply expectedValue_le_of_le
    intro r
    unfold nearMemPotential
    rw [if_pos hq]
    exact bot_le
  push Not at hq
  set C0 := (reuseC S) rows (Function.update nonces m (some 0)) with hC0
  have hupd : ∀ v : Digest, (reuseC S) rows (Function.update nonces m (some v)) = C0 := by
    intro v
    unfold reuseC
    apply tsum_congr
    intro m'
    by_cases he : m' = m
    · subst he; simp
    · simp only [Function.update_of_ne he]
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (S.search v m 0 fuel) rows) →
      (reuseC S) r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [(reuseC_signed_eq S) rows r.2 _ m (by simp) ((digestSearch_reuseMass S) secret v m fuel rows r hr), hupd]
  have hC : C0 + S.reuseMass rows m ≤ (reuseC S) rows nonces := by
    rw [← hupd 0]
    exact (reuseC_sign_le S) rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * (S.admBound / 2 ^ 128) with hextra
  have hbefore : (nearMemPotential S) q births exposures reused rows nonces = (nearPotential S) b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (S.search v m 0 fuel) rows) →
      (nearMemPotential S) q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (S.Reuse rows v m)) r.2 (Function.update nonces m (some v)) =
        (nearPotential S) ⟨births, exposures ++ (r.1.map Prod.snd).toList,
          reused || decide (S.Reuse rows v m), C0, q - births.length⟩ + extra := by
    intro v r hr
    unfold nearMemPotential
    rw [if_neg (by omega), hafter v r hr]
  have hreuse : ∀ (o : Option HashOutput), (nearPotential S) ⟨births, exposures ++ o.toList, true, C0,
      q - births.length⟩ ≤ (nearPotential S) { b with reused := true, reuse := C0 } := by
    intro o
    have hl : exposures.length ≤ (exposures ++ o.toList).length := by simp
    unfold nearPotential Flexible.corePotential
    rw [hb]
    simp only [if_true]
    by_cases h2 : (2^32) < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : (2^32) < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows)
            (fun r => (nearPotential S) (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
            (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
              else (nearPotential S) (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : S.Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows) (fun r =>
            (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
              else (nearPotential S) (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : S.Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if S.Reuse rows v m then (nearPotential S) { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (S.search v m 0 fuel) rows)
            (fun r => (nearPotential S) (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add ((near_sign S) b rows m C0 hC secret fuel hfuel) le_rfl
theorem mem_initial (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate) (q : Nat) :
    (nearMemPotential S) q [] [] false ∅ (fun _ => none) ≤ (q:ENNReal)*(rate+S.admBound)/2^128 := by
  unfold nearMemPotential
  simp only [List.length_nil,Nat.not_lt_zero,if_false,Nat.sub_zero]
  have hC : (reuseC S) ∅ (fun _ => none)=0 := by
    unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
    simp
  have hn := (near_initial S) rate hrate q
  rw [show (⟨[],[],false,(reuseC S) ∅ (fun _ => none),q⟩:BankCore)=⟨[],[],false,0,q⟩ by rw [hC]]
  calc
    _ ≤ (q:ENNReal)*rate/2^128+(q:ENNReal)*(S.admBound/2^128) := add_le_add hn le_rfl
    _ = _ := by simp only [div_eq_mul_inv];ring
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q) (hlen : exposures.length ≤ (2^32))
    (h : reused = true ∨ ∃ N ∈ births, S.admissible N = true ∧ S.covered exposures N) :
    1 ≤ (nearMemPotential S) q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact ((near_win S) ⟨births, exposures, reused, (reuseC S) rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add
#print axioms mem_birth
#print axioms mem_sign_fresh
#print axioms mem_initial
#print axioms mem_win
end ClaudeWCT.Bank.NearMemory

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
open ClaudeWCT.W9.T3.Security
open SigGolfCandidate.T3.Security.CaseC (Agrees lazyOf countOf IsDigestInput eventPublic)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem bank_alive {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hlen : state.1.log.length≤2^32) : state.1.dead=false := by
  cases hd:state.1.dead
  · rfl
  · have h:=hinv.dead hd
    change 2^32<state.1.log.length at h
    omega

theorem loggedOutputs_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (halive : state.1.dead=false) (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2)) :
    ∀ out∈WPair.Paired.loggedOutputs A state.1.log,out∈state.1.exposures := by
  intro out ho
  obtain ⟨entry,he,signature,hsig,hs⟩:=WPair.Paired.mem_loggedOutputs.mp ho
  unfold WPair.Paired.signedOutput at hs
  cases hsearch:evalWithAnswerFn A
      (SharedForest.sharedDigestSearch signature.rho entry.1.message 0 ClaudeWCT.WCT9.digestAttemptLimit) with
  | none => rw [hsearch] at hs;cases hs
  | some found =>
      rcases found with ⟨counter,value⟩
      rw [hsearch] at hs
      simp only [Option.map_some,Option.some.injEq] at hs
      subst out
      apply FtsBankSpecL.BankInv.logged_exposed bankSpec payAfterDigest SharedForest.Signature.rho
        hinv halive entry he signature hsig A hA counter value
      change evalWithAnswerFn A (lawSpec.search signature.rho entry.1.message 0 ClaudeWCT.WCT9.digestAttemptLimit)=_
      rw [←digestSearch_public]
      exact hsearch

theorem bank_covered_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (halive : state.1.dead=false) (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2))
    (N : HashOutput) (hcovered : Covered (WPair.Paired.loggedOutputs A state.1.log) N) :
    Covered state.1.exposures N := by
  intro k t
  obtain ⟨p,hp,hi,hc,hd⟩:=hcovered k t
  obtain ⟨out,ho,rfl⟩:=List.mem_map.mp hp
  exact ⟨proposal out,List.mem_map_of_mem (loggedOutputs_exposed hinv halive A hA out ho),hi,hc,hd⟩

theorem bank_target_of_fresh {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hcount : countOf state.2≤budget)
    (e : FirstHit.QueryEvent) (he : e∈state.2.events) (hkg : e∉kg)
    (x : HashInput) (N : HashOutput) (hpub : eventPublic e=some (x,N))
    (hd : IsDigestInput x) (hf : e.before.2 x=none)
    (hnot : ¬bankSpec.SignerQueried payAfterDigest published state.1.log (lazyOf state.2) x) :
    N∈state.1.targets := by
  rcases hinv.events e he with hk|ht
  · exact (hkg hk).elim
  · rcases ht x N hpub hd hf with h|hb|hs
    · exact h
    · omega
    · exact (hnot hs).elim

theorem flexible_potential_source_covered (θ : ENNReal)
    {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {state : BankState SharedForest.Signature}
    (hinv : bankSpec.BankInv payAfterDigest SharedForest.Signature.rho published budget kg state)
    (hlen : state.1.log.length≤2^32) (hcount : countOf state.2≤budget)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf state.2)) (N : HashOutput)
    (hN : N∈state.1.targets) (hadm : admissible N=true)
    (hcovered : Covered (WPair.Paired.loggedOutputs A state.1.log) N) :
    1≤flexiblePotential θ budget state :=
  flexible_potential_win θ budget state (bank_alive hinv hlen) hcount
    (Or.inr ⟨N,hN,hadm,bank_covered_exposed hinv (bank_alive hinv hlen) A hA N hcovered⟩)

#print axioms loggedOutputs_exposed
#print axioms bank_target_of_fresh
#print axioms flexible_potential_source_covered
end ClaudeWCT.Bank.Paired

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem interaction_le' (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message))
    {α : Type} (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
        F (none, ws') ∨ ∀ m s v σ, Final m s v σ → m.contact = false) →
      (∀ m s v σ, Final m s v σ → FamOK s) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop hfin mon st ws state hrel hmemo
      rcases input with (n | X) | request
      ·
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop hfin mon st ws _ hrel hmemo
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · by_cases hok : FamOK st
          swap
          · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                  (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                  last.state⟩ : Tagged α)) |
                taggedFixed T published (next (T (.inl (.inr X))))
                  (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
              refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
              intro t ht
              exact hok (famOK_mono (steps_disclosed_mono U T nv published _ _) (hfin _ _ _ _ ht))
            rw [hzero]
            exact zero_le
          rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq hok X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rcases hstop ws1 hcalls with hF | hnc
            · rw [probEvent_pure, if_pos hF]
              exact probEvent_le_one
            · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                    (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                  (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                    last.state⟩ : Tagged α)) |
                  taggedFixed T published (next (T (.inl (.inr X))))
                    (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
                refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
                intro t ht
                simp only [Function.comp_apply, List.foldl_cons] at ht
                have h1 := hnc _ _ _ _ ht
                change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                  = false at h1
                rw [steps_frozen U T q published _ hc] at h1
                rw [hc] at h1
                cases h1
              rw [hzero]
              exact zero_le
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold LargeResidual.RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop hfin _ _ ws1 _ hrel1 hmemo1
      ·
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hsource hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (PairedOuter.FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        have hstop' : ∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
            F (none, ws') ∨ ∀ m s v σ, Final' m s v σ → m.contact = false := by
          intro ws' hws
          rcases hstop ws' hws with h | h
          · exact Or.inl h
          · exact Or.inr fun m s v σ hf => h _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop' (fun m s v σ hf => hfin _ _ _ _ hf) _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def verdictCert (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (st : RouterState) (value : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (state : LazyPrivate.State) : Prop :=
  evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) = true ∧
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = false ∧
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).calls ≤ q ∧
  CertGhost ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (routerEvent U) st)
theorem honestNonce_coherent {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell U → HashOutput} {a : AuxData} (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) : nv = honestNonce T := by
  funext m
  exact (hcoh.privateNonce m).symm
theorem table_cert_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.PairedReference.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : LargeResidual.Paired.Coherent (Wots.PairedReference.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => CertR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[CertOut |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.PairedReference.referenceInputs adversary := Wots.PairedReference.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  have hnv := honestNonce_coherent hcoh
  rw [hcoh.routerWith, Wots.PairedReference.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.PairedReference.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le' initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 (hcoh.source _ hpub)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictCert (Wots.PairedReference.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon st
      value state ∧ FamOK st)
    (verdictCont (Wots.PairedReference.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) CertOut
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial LargeResidual.RouterState.initial
    (keyState (Wots.PairedReference.referenceInputs adversary) q vals nv) _ rel_initial
    (fun _ _ h => by simp [LargeResidual.RouterState.initial] at h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    obtain ⟨h1, h2, h3, h4⟩ := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h2 h3 h4
    have hv : (Wots.PairedReference.Ref.verdictRecord T t.untag).value =
        evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) :=
      Wots.Ref.pureRecord_value _ _ _
    refine ⟨⟨hv ▸ h1, h2, h3, ?_⟩, fun f => ?_, fun L => ?_⟩
    · unfold routerFold at h4
      rw [hnv]
      exact h4
    · have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
      have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 (hcoh.source _ hpub) _ _ t ht LargeResidual.RouterState.initial f
      rw [discSeeds_initial, Finset.empty_union] at hsub
      exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
    · have hsub := discLower_steps (Wots.PairedReference.referenceInputs adversary) T nv (evalWithAnswerFn T keygen).2 t.steps
        LargeResidual.RouterState.initial L
      rw [discLower_initial, Finset.empty_union] at hsub
      have := lowerZeros_card T L
      exact (Finset.card_le_card hsub).trans (by omega)
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PairedOuter.PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.PairedReference.referenceInputs adversary) a q
        (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    obtain ⟨⟨hval, hnc, hcalls, hcert⟩, -⟩ := hf
    rcases hph with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · rw [hnc] at h2; cases h2
    · omega
    · rw [if_pos ⟨_, by rw [h1, hval], hcert⟩]
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.PairedReference.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    have := hf.1.2.2.1
    omega
  · intro ws' _
    right
    intro m s v σ hf
    by_contra hcon
    have hc : m.contact = true := by simpa using hcon
    have h := hf.1.2.1
    rw [events_frozen (Wots.PairedReference.referenceInputs adversary) T q m hc] at h
    rw [hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCert_pairedShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem routerStep_world (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (e : FirstHit.QueryEvent) : routerStep U A nv published st (.world e) = routerEvent U st e := rfl
theorem routerStep_sign (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (request : Security.Request) (out : Option SigGolfCandidate.Research.SharedForest.Signature) (events : List FirstHit.QueryEvent) :
    routerStep U A nv published st (.sign request out events) = signedState A nv published st request := rfl
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem honestNonce_short : honestNonce A=honestNonce T := by
  funext m
  unfold honestNonce
  simp only [SigGolfCandidate.T3.privateNonce,privateHash,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  change (A (.inr (.inr (.inl m)))).extractLsb' 0 128=(T (.inr (.inr (.inl m)))).extractLsb' 0 128
  rw [hAT.priv]
theorem routeOk_short : RouteOk A = RouteOk T := by
  funext index
  apply propext
  unfold RouteOk
  simp only [Wots.CanonicalRef.referenceSearch_short hAT]
theorem signedState_short (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState A nv published st request = signedState T nv published st request := by
  have hd : Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) = Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) := funext (Wots.CanonicalRef.referenceDigits_short hAT)
  unfold signedState LargeResidual.Paired.signItems
  rw [signDigest_short hAT, hd, routeOk_short hAT]
theorem routerStep_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (st : RouterState) (s : TaggedStep) :
    routerStep U A (honestNonce A) published st s = routerStep U T (honestNonce T) published st s := by
  cases s with
  | world e => rw [routerStep_world, routerStep_world]
  | sign request out events =>
      rw [routerStep_sign, routerStep_sign, honestNonce_short hAT, signedState_short hAT]
theorem steps_router_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ st, steps.foldl (routerStep U A (honestNonce A) published) st =
      steps.foldl (routerStep U T (honestNonce T) published) st := by
  induction steps with
  | nil => intro st; rw [List.foldl_nil, List.foldl_nil]
  | cons s rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, routerStep_short hAT, ih]
theorem routerFold_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    routerFold U A published steps verdict = routerFold U T published steps verdict := by
  unfold routerFold
  rw [steps_router_short hAT]
end Short
theorem certR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : CertR adversary q result A ↔ CertR adversary q result T := by
  unfold CertR
  simp only [monitorRun_short hAT, routerFold_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of
  weight_self evalSPMF_uniform_inst probEvent_bind_congr_eq completeRows_none)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
section CertChain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
def RealCert (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  CertR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem cert_real_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] =
      Pr[RealCert adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.PairedReference.completed_eager_cut adversary q hq (fun rec A => CertR adversary q rec A ∧ NoOvR adversary rec A)
  rw [h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => CertR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealCert adversary q := by
    funext x
    exact propext (and_congr (certR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.PairedReference.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
section Lazy
variable {U : Finset HashInput}
theorem finish_some_le {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U))) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | X >>= finish] ≤ Pr[fun r => ∃ v, r.1 = some v ∧ P v | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish ((none : Option R), st)] = 0 := by
        simp only [finish, probEvent_pure]
        rw [if_neg]
        rintro ⟨v, hv, -⟩
        cases hv
      rw [h0, mul_zero]
      exact zero_le
  | some v =>
      by_cases hP : P v
      · rw [if_pos ⟨v, rfl, hP⟩]
        exact mul_le_of_le_one_right zero_le probEvent_le_one
      · have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish (some v, st)] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro x hx hE
          unfold finish at hx
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hx
          obtain ⟨labels, -, table, -, rfl⟩ := hx
          obtain ⟨v', hv', hP'⟩ := hE
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact hP hP'
        rw [h0, mul_zero]
        exact zero_le
theorem observed_avg_le {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v | 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>=
        fun x => 𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q (view x) τ program LargeResidual.initial] ≤
      Pr[fun r => ∃ v, r.1 = some v ∧ P v | lazyRun aux q program LargeResidual.initial] := by
  rw [← cell_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (by change (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))).Nonempty
        rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]; exact Finset.univ_nonempty)
  refine le_trans (le_of_eq ?_) (finish_some_le (lazyRun aux q program LargeResidual.initial) P)
  rw [← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  apply propext
  rcases r with ⟨_ | v, st⟩
  · simp [retain]
  · simp [retain]
theorem certOut_iff (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    CertOut r ↔ ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st := by
  constructor
  · rintro ⟨st, h1, h2⟩
    exact ⟨_, h1, st, rfl, h2⟩
  · rintro ⟨v, h1, st, rfl, h2⟩
    exact ⟨st, h1, h2⟩
theorem router_side_cert (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[CertOut |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.PairedReference.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ
          (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q (auxOf high rows priv)) LargeResidual.initial] ≤
      Pr[CertOut |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hce : (@CertOut (Wots.PairedReference.referenceInputs adversary)) =
      fun r => ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st :=
    funext fun r => propext (certOut_iff r)
  rw [hce]
  unfold router initReq
  rw [lazy_aux]
  change _ ≤ Pr[_ | (liftM initLaw : SPMF AuxData) >>= _]
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_mono_le
  intro high
  apply probEvent_bind_mono_le
  intro rows
  apply probEvent_bind_mono_le
  intro priv
  exact observed_avg_le (auxLaw initLaw) q _ _
end Lazy
theorem cert_le_lazy (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[CertOut | lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q)
        LargeResidual.initial] := by
  have hU : CanonGraph.Paired.canonInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.Paired.canonInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  rw [cert_real_side]
  refine le_trans ?_ (router_side_cert adversary q)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.PairedReference.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun high => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun x => ?_
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.PairedReference.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.PairedReference.referenceInputs adversary)
          (CanonGraph.Paired.Filtered.programmed (Wots.PairedReference.referenceInputs adversary) hU (secOf x jk)
            (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.PairedReference.referenceInputs adversary) hE (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          (auxOf high rows priv) := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealCert
    rw [probEvent_map]
    have h := table_cert_le adversary q hq initLaw
      (coherent_psi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ (auxOf high rows priv) (auxOf_consistent _ _ _) (seedView_secOf x jk))
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end CertChain
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
end
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable (θ : ENNReal)
noncomputable def bankPay {U : Finset HashInput} (θ : ENNReal) (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi θ q st
    | _ => 0) + slackT θ q r.2
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Final.Paired.Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT θ q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi θ q st + slackT θ q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT θ q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi θ q st + slackT θ q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuerySelected θ aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign θ aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT θ q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi θ q st + slackT θ q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT θ q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi θ q st + slackT θ q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuerySelected θ aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls
theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s LargeResidual.RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [LargeResidual.RouterState.initial]),
    fun p hp => absurd hp (by simp [LargeResidual.RouterState.initial]), fun X hX => absurd hX (by simp [LargeResidual.RouterState.initial])⟩
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : Final.Paired.AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay θ q) ≤
      psi θ q LargeResidual.RouterState.initial + coeffQ θ q * (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT θ q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) =
      coeffQ θ q * (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction θ (auxLaw initLaw) q hUpub a _ _ _ (bankPay θ q) ?_ ?_ ?_ LargeResidual.RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict θ (auxLaw initLaw) q a _ (bankPay θ q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass θ q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]
end Run

#print axioms bank_router
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open SigGolfCandidate.T3.Security.LargeResidual (State Cell)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun lazy_pure lazy_noFail)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable (θ : ENNReal)
variable {U : Finset HashInput}
noncomputable def psiOut (θ : ENNReal) (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi θ q st
  | _ => 0
theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut θ q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert θ q st hc
  · exact zero_le
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : Final.Paired.AdversaryP) (q : Nat) (htheta : θ≠⊤) (rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.lawSpec.law (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.lawSpec.price W-θ)≤rate) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * rate / 2 ^ 128 +
        coeffQ θ q * (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router θ q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay θ q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut θ q r + slackT θ q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut θ q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi θ q)
  set S := expectedValue L (fun r => slackT θ q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : coeffQ θ q * (q : ENNReal) / 2 ^ 128 ≤ S + coeffQ θ q * Mass / 2 ^ 128 := by
    have hMass' : coeffQ θ q * Mass / 2 ^ 128 =
        expectedValue L (fun r => coeffQ θ q * (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv, ← mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      rw [expectedValue_def]
      apply tsum_congr
      intro r
      ring
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail (coeffQ θ q * (q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div, ← mul_add, ← Nat.cast_add]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' le_rfl
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hcoeff_fin : coeffQ θ q ≠ ⊤ := by unfold coeffQ; exact ENNReal.add_ne_top.mpr ⟨htheta,by change (1/1024:ENNReal)≠⊤; finiteness⟩
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := coeffQ θ q * (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top hcoeff_fin (ENNReal.natCast_ne_top q)) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      apply mul_le_mul' le_rfl
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut θ q) + S ≤ (psi θ q LargeResidual.RouterState.initial + coeffQ θ q * Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi θ q LargeResidual.RouterState.initial + coeffQ θ q * (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi θ q LargeResidual.RouterState.initial + (S + coeffQ θ q * Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut θ q) := hcert
    _ ≤ psi θ q LargeResidual.RouterState.initial + coeffQ θ q * Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial θ q rate hexc) le_rfl

#print axioms bank_cert_le
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable

theorem budgetRate_ge_one (q : Nat) (hq : q≤2^127) : 1≤Flexible.budgetRate q := by
  have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
  have hm : 2*(q:ℝ)≤(2:ℝ)^128 := calc
    _ ≤ 2*2^127 := mul_le_mul_of_nonneg_left hqr (by norm_num)
    _ = _ := by norm_num
  have hdiv := (div_le_one (by positivity : (0:ℝ)<2^128)).2 hm
  unfold Flexible.budgetRate
  linarith

theorem coeffQ_budgetRate (q : Nat) (hq:q≤2^127) :
    coeffQ (ENNReal.ofReal (Flexible.budgetRate q-1/1024)) q = ENNReal.ofReal (Flexible.budgetRate q) := by
  have h:=budgetRate_ge_one q hq
  unfold coeffQ
  change ENNReal.ofReal (Flexible.budgetRate q-1/1024)+(1/1024:ENNReal)=_
  rw [show (1/1024:ENNReal)=ENNReal.ofReal (1/1024:ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
    ←ENNReal.ofReal_add (by linarith : 0≤Flexible.budgetRate q-1/1024) (by positivity)]
  congr 1
  ring

theorem contact_cert_bound_of_excess (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (rate : ENNReal)
    (hexc : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-ENNReal.ofReal (Flexible.budgetRate q-1/1024))≤rate) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z=>CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
        PairedSeccLaw.completedExperiment adversary q hq] ≤
      ENNReal.ofReal (2*((q:ℝ)/2^128)-((q:ℝ)/2^128)^2)+(q:ENNReal)*rate/2^128 := by
  have hb := bank_cert_le (ENNReal.ofReal (Flexible.budgetRate q-1/1024))
    (Wots.PairedReference.Ref.referenceInputs_universe adversary) initLaw adversary q (by finiteness) rate hexc
  rw [coeffQ_budgetRate q hq] at hb
  have hp := Flexible.residual_potential_rate (Flexible.budgetRate q) (auxLaw initLaw) q hq
    (Flexible.budgetRate_nonneg q hq) (Flexible.budgetRate_mul q).le
    (router (Wots.PairedReference.referenceInputs adversary) adversary q)
  have h:=add_le_add (contact_le_lazy adversary q hq) ((cert_le_lazy adversary q hq).trans hb)
  have hsum : ∀a b c : ENNReal,a+(b+c)=(a+c)+b := by intros;ring
  rw [hsum] at h
  exact h.trans (add_le_add hp le_rfl)

#print axioms contact_cert_bound_of_excess
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
