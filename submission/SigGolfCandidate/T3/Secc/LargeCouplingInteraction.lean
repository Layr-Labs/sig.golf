import SigGolfCandidate.T3.Secc.LargeCouplingVerdict

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
noncomputable def taggedFixed {α : Type} (F : Answers) (published : T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) : LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let answer ← Wots.Ref.fixedWorld F (.inl world)
          (fun last => (⟨last.value, .world ⟨state, .inl world, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next answer (FirstHit.advance state (.inl world) answer)
      | .inr request, next => do
          let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
section Fixed
variable {α : Type} (F : Answers) (published : T3.Cache)
theorem taggedFixed_pure (value : α) (state : LazyPrivate.State) :
    taggedFixed F published (pure value : OracleComp LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedFixed_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let answer ← Wots.Ref.fixedWorld F (.inl input)
      (fun last => (⟨last.value, .world ⟨state, .inl input, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next answer) (FirstHit.advance state (.inl input) answer)) := rfl
theorem taggedFixed_request (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedFixed F published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← Wots.Ref.fixedRecord F (FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next block.value) block.state) := rfl
theorem taggedFixed_support (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State)
    (hF : Wots.Ref.Agrees F state) (tagged : Tagged α) (h : tagged ∈ support (taggedFixed F published program state)) :
    tagged ∈ support (taggedRecord published program state) ∧ Wots.Ref.Agrees F tagged.state := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedFixed_pure, mem_support_pure_iff] at h
      subst h
      exact ⟨by rw [taggedRecord_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, mem_support_bind_iff] at h
          obtain ⟨answer, ha, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hcons : ∀ cached, SourceReplay.known state (.inl input) = some cached → cached = answer := by
            intro cached hc
            rcases input with n | x
            · cases hc
            · have h1 := hF _ _ hc
              rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              rw [ha, ← h1]
          have hadv : Wots.Ref.Agrees F (FirstHit.advance state (.inl input) answer) := by
            rcases input with n | x
            · exact hF
            · rw [Wots.Ref.fixedWorld_public, mem_support_pure_iff] at ha
              subst ha
              exact Wots.Ref.agrees_advance hF _
          obtain ⟨h1, h2⟩ := ih answer _ hadv last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_world, mem_support_bind_iff]
          refine ⟨(answer, FirstHit.advance state (.inl input) answer),
            Wots.Ref.lazy_query_mem state (.inl input) answer hcons, ?_⟩
          rw [support_map]
          exact ⟨last, h1, rfl⟩
      | inr request =>
          rw [taggedFixed_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          obtain ⟨hb1, hb2⟩ := Wots.Ref.fixedRecord_mem_record F _ state hF block hb
          obtain ⟨h1, h2⟩ := ih block.value block.state hb2 last hl
          refine ⟨?_, h2⟩
          rw [taggedRecord_request, mem_support_bind_iff]
          exact ⟨block, hb1, by rw [support_map]; exact ⟨last, h1, rfl⟩⟩
theorem taggedFixed_untag (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    Tagged.untag <$> taggedFixed F published program state =
      Wots.Ref.fixedRecord F (FullGame.loggedWith (FullGame.authenticatedSign published) program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [taggedFixed_pure, map_pure, FullGame.loggedWith_pure, Wots.Ref.fixedRecord_pure]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, FullGame.loggedWith_world]
          change _ = Wots.Ref.fixedRecord F (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state
          rw [Wots.Ref.fixedRecord_query_bind, map_bind]
          apply bind_congr
          intro answer
          rw [Functor.map_map, ← ih answer]
          simp only [Functor.map_map]
          rfl
      | inr request =>
          rw [taggedFixed_request, FullGame.loggedWith_request, Wots.Ref.fixedRecord_bind, map_bind]
          apply bind_congr
          intro block
          rw [Wots.Ref.fixedRecord_map, ← ih block.value, Functor.map_map, Functor.map_map,
            map_eq_bind_pure_comp]
          simp only [Function.comp_def, bind_pure_comp, Functor.map_map]
          rfl
end Fixed
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
noncomputable local instance instDecidableEqCache_largeCouplingInteraction : DecidableEq T3.Cache := Classical.decEq _
noncomputable def routerStep (U : Finset HashInput) (T : Answers) (nv : Message → Digest) (published : T3.Cache)
    (st : RouterState) : TaggedStep → RouterState
  | .world e => routerEvent U st e
  | .sign request _ _ => signedState T nv published st request
section Steps
variable (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)
theorem steps_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (steps : List TaggedStep) :
    (steps.foldl (Monitor.step U A q published) mon).contact = false ∧
      q < (steps.foldl (Monitor.step U A q published) mon).calls := by
  induction steps generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).1
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            rfl
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).2
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            exact hq
theorem steps_frozen (mon : Monitor) (hc : mon.contact = true) (steps : List TaggedStep) :
    steps.foldl (Monitor.step U A q published) mon = mon := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = mon := by
        cases s with
        | world e => exact event_frozen U A q mon hc e
        | sign request out events => simp only [Monitor.step, Monitor.sign, hc, if_true]
      rw [h1, ih]
end Steps
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem routeInteraction_pure {α : Type} (published : T3.Cache) (v : α) (st : RouterState) :
    routeInteraction U a published q (pure v : OracleComp LazyPrivate.Interaction α) st = pure (some ((v, []), st)) :=
  rfl
theorem routeInteraction_coin {α : Type} (published : T3.Cache) (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) st =
      (coinReq U n >>= fun c => routeInteraction U a published q (next c) st) := rfl
theorem routeInteraction_hash {α : Type} (published : T3.Cache) (X : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else
        (routeQuery U a st X >>= fun r => routeInteraction U a published q (next r.1) r.2) := rfl
theorem routeInteraction_request {α : Type} (published : T3.Cache) (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) st =
      (routeSign U a published st request >>= fun s =>
        routeInteraction U a published q (next s.1) s.2 >>= fun rest =>
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2))) := rfl
end Interaction
end SigGolfCandidate.T3.Security.LargeCoupling
end
