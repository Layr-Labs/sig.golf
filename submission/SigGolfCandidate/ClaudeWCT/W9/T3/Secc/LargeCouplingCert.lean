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
    (hbudget : 32 * (probes + remaining + 1) ≤ space) :
    (15 / 8) / space + PrimitiveMessagePotential.value space probes remaining ≤
      PrimitiveMessagePotential.value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : (15 / 8) * space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : (15 / 8) / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      (15 / 8) / space = ((15 / 8) * space) / space ^ 2 := by field_simp
      _ ≤ ((15 / 8) * space) / (space - probes) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← PrimitiveMessagePotential.message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith

theorem continuation_pay_54 (space q calls probes : Nat) (hspace : 0 < space) (hq : 32 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + (15 / 8 : ENNReal) / space ≤ continuation space q calls probes := by
  have hs : (0 : ℝ) < space := by exact_mod_cast hspace
  have hb : 32 * (q : ℝ) ≤ space := by exact_mod_cast hq
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
  have hof54 : ENNReal.ofReal ((15 / 8 : ℝ) / space) = (15 / 8 : ENNReal) / space := by
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (by positivity) hv, hof54] at hfinal
  rw [add_comm]
  exact hfinal

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
  [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]

noncomputable def potential54 {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space
noncomputable def stopValue54 {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space
noncomputable def doneValue54 {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space

theorem terminal54_le_of_over {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue54 ch space q) (potential54 ch space q) result ≤
      (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (15 / 8 : ENNReal) * (ch.mass result.2 : ENNReal) / space ≤
      (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue54, hnot] using hm
  · simpa [terminal, potential54, continuation, hnot] using hm

theorem payment54_of_stepBound {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (input : spec.Domain) (state : σ) (h : StepBound step ch space q input state)
    (hspace : 0 < space) (hq8 : 32 * q ≤ space) (hprobes : ch.probes state ≤ ch.calls state) :
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
      have hm : (15 / 8 : ENNReal) * (ch.mass after : ENNReal) / space ≤
          (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space + (15 / 8 : ENNReal) / space := by
        rw [← ENNReal.add_div]
        apply ENNReal.div_le_div_right
        calc
          (15 / 8 : ENNReal) * (ch.mass after : ENNReal) ≤
              (15 / 8 : ENNReal) * ((ch.mass state + 1 : Nat) : ENNReal) :=
            mul_le_mul' le_rfl (by exact_mod_cast hmass)
          _ = (15 / 8 : ENNReal) * (ch.mass state : ENNReal) + (15 / 8 : ENNReal) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      calc
        _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
            ((15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space + (15 / 8 : ENNReal) / space) :=
          add_le_add hcont hm
        _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (15 / 8 : ENNReal) / space) +
            (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space := by ring
        _ ≤ _ := add_le_add hpay le_rfl
    · rw [if_neg hc, add_zero] at hmass
      exact (terminal54_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
  · by_cases hc : ch.calls state + 1 ≤ q
    · have hpoint : ∀ result ∈ support (step input state),
          terminal (stopValue54 ch space q) (potential54 ch space q) result ≤
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (15 / 8 : ENNReal) * (ch.mass after : ENNReal) / space ≤
            (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue54, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential54, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state) +
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
            (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space := by
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
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space := by
        rintro ⟨answer, after⟩ hresult
        obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
        have hm : (15 / 8 : ENNReal) * (ch.mass after : ENNReal) / space ≤
            (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space :=
          ENNReal.div_le_div_right (mul_le_mul' le_rfl (by exact_mod_cast hmass)) _
        rcases answer with _ | answer
        · simp only [terminal, Option.elim_none, stopValue54, if_true]
          exact add_le_add (by split <;> simp) hm
        · simp only [terminal, Option.elim_some, potential54, reduceCtorEq, if_false]
          exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
      calc
        _ ≤ expectedValue (step input state) (fun result =>
            (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
        _ ≤ Pr[fun result => result.1 = none | step input state] +
            (1 - Pr[fun result => result.1 = none | step input state]) *
              continuation space q (ch.calls state + 1) (ch.probes state + 1) +
              (15 / 8 : ENNReal) * (ch.mass state : ENNReal) / space :=
          expected_stop_le _ _ _
        _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
    · apply expectedValue_le_of_support
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      exact (terminal54_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self

theorem stop_add_mass_eq_54 {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (15 / 8 : ENNReal) * (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue54 ch space q) (doneValue54 ch space)) := by
  have hfun : terminal (stopValue54 ch space q) (doneValue54 ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) +
        (15 / 8 : ENNReal) * (ch.mass result.2 : ENNReal) / space := by
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
    (hq8 : q ≤ 2 ^ 123) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (15 / 8 : ENNReal) * (∑' result, Pr[= result | LargePotential.run step program init] *
        (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h : Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | LargePotential.run step program init] +
      (15 / 8 : ENNReal) * (∑' result, Pr[= result | LargePotential.run step program init] *
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
    (hq : q ≤ 2 ^ 123) (program : OracleComp (SigGolfCandidate.T3.Security.LargeResidual.World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q |
        ClaudeWCT.W9.T3.Security.FamResidual.lazyRun aux q program
          SigGolfCandidate.T3.Security.LargeResidual.initial] +
      (15 / 8 : ENNReal) * (∑' result,
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
    (if q ≤ 2 ^ 123 then 15 / 8 else 1) * routerMass adversary q / 2 ^ 128 +
      (q : ENNReal) * (if q ≤ 2 ^ 123 then excessRate54 else excessRate) / 2 ^ 128 +
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
  · by_cases h125 : q ≤ 2 ^ 123
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
      (q : ENNReal) * (if q ≤ 2 ^ 123 then 6441 / 10000000 else 451 / 200000) / 2 ^ 128 +
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
  have hexc_eq : (if q ≤ 2 ^ 123 then (6441 / 10000000 : ENNReal) else 451 / 200000) =
      (if q ≤ 2 ^ 123 then excessRate54 else excessRate) := by
    rw [ClaudeWCT.W9.T3.Security.SeccClosingW9.excessRate54_def,
      ClaudeWCT.W9.T3.Security.SeccClosingW9.excessRate_def]
  rw [hrm, hexc_eq]
  unfold coeffQ
  calc
    _ = (if q ≤ 2 ^ 123 then 15 / 8 else 1) * routerMass adversary q / 2 ^ 128 +
        (q : ENNReal) * (if q ≤ 2 ^ 123 then excessRate54 else excessRate) / 2 ^ 128 + largeReserveAbsolute := by
      rw [add_comm ((q : ENNReal) * (if q ≤ 2 ^ 123 then excessRate54 else excessRate) / 2 ^ 128)]
    _ ≤ _ := add_le_add (le_add_right (le_add_right le_rfl)) le_rfl
theorem large_route (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  large_route_of_cert adversary q hq (large_cert_bound adversary q hq)
theorem large_route_hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), ClaudeWCT.W9.T3.Security.SeccClosingW9.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  fun adversary q hq _ => large_route adversary q hq
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
