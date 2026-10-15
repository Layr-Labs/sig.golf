import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingSplit
import SigGolfCandidate.T3.Secc.LargeContactMonitor

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (slotValue IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def Clear (A : Answers) (K : Coord → Prop) (X : HashInput) (y : HashOutput) : Prop :=
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos →
      ¬(X ≠ Extract.honestInput A N.toPos ∧ N.toPos.proj y = honestValue A (.inl N))) ∧
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos → ∀ c b, childSlots N = [(c, b)] →
      slotValue X b = honestValue A c → K c) ∧
  (∀ (L : CanonEncoding.EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad),
      Extract.msgFits L.1.lay m → X = Wots.encRow L.toWots m ctr pad →
      ¬(Wots.referenceInput A L.toWots ≠ some X ∧
        decode L.1.lay (WCT9.encodingAnswer L.1.lay y) = some (Wots.referenceDigits A L.toWots)))
theorem firstUnknown_single (K : Coord → Prop) (N : CanonGraph.Node) (c : Coord) (b : Nat)
    (h : childSlots N = [(c, b)]) (hk : ¬K c) : firstUnknown K N = some (c, b) := by
  unfold firstUnknown
  rw [h]
  simp [hk]
theorem clear_of_not_contact {A : Answers} {K : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : ¬ContactTest A K X y) : Clear A K X y := by
  refine ⟨fun N hpos hhit => h (Or.inl ⟨N, hpos, Or.inr hhit⟩), fun N hpos c b hs hv => ?_,
    fun L m ctr pad hfit hX hhit => h (Or.inr ⟨L, m, ctr, pad, hfit, hX, Or.inr hhit⟩)⟩
  by_contra hk
  exact h (Or.inl ⟨N, hpos, Or.inl ⟨(c, b), firstUnknown_single K N c b hs hk, hv⟩⟩)
theorem Clear.mono {A : Answers} {K K' : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : Clear A K X y) (hK : ∀ c, K c → K' c) : Clear A K' X y :=
  ⟨h.1, fun N hpos c b hs hv => hK c (h.2.1 N hpos c b hs hv), h.2.2⟩
def MonitorOK (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) : Prop :=
  monitor.contact = false → monitor.calls ≤ q → ∀ X ∈ monitor.seen, X ∈ U →
    Clear A monitor.known X (A (.inl (.inr X)))
theorem monitorOK_initial (U : Finset HashInput) (A : Answers) (q : Nat) : MonitorOK U A q Monitor.initial := by
  intro _ _ X hX
  simp [Monitor.initial] at hX
theorem monitorOK_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.query U A q X (A (.inl (.inr X)))) := by
  unfold Monitor.query
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  by_cases ht : X ∉ monitor.seen ∧ X ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known X (A (.inl (.inr X)))
  · rw [if_pos ht]
    intro hfalse
    simp at hfalse
  · rw [if_neg ht]
    intro _ hq Y hY hYU
    change monitor.calls + 1 ≤ q at hq
    have hcf : monitor.contact = false := by simpa using hc
    have hq' : monitor.calls ≤ q := by omega
    simp only [List.mem_cons] at hY
    change Clear A monitor.known Y (A (.inl (.inr Y)))
    rcases hY with rfl | hY
    · by_cases hs : Y ∈ monitor.seen
      · exact h hcf hq' Y hs hYU
      · exact clear_of_not_contact (fun hct => ht ⟨hs, hYU, hq, hct⟩)
    · exact h hcf hq' Y hY hYU
theorem monitorOK_sign (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor) (request : Security.Request)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.sign A published request) := by
  unfold Monitor.sign
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  intro _ hq Y hY hYU
  have hcf : monitor.contact = false := by simpa using hc
  refine (h hcf hq Y hY hYU).mono fun c hk => Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (List.mem_append_left _ hd)
theorem monitorOK_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (hagree : SourceReplay.IsHash event.input → A event.input = event.answer) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (monitor.event U A q event) := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · have hagree' : A (.inl (.inr X)) = answer := hagree trivial
    subst hagree'
    exact monitorOK_query U A q monitor X h
  · exact h
theorem monitorOK_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (hagree : EventsAgree A events)
    (monitor : Monitor) (h : MonitorOK U A q monitor) : MonitorOK U A q (events.foldl (Monitor.event U A q) monitor) := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact ih (fun e he => hagree e (List.mem_cons_of_mem _ he)) _
        (monitorOK_event U A q monitor event (hagree event List.mem_cons_self) h)
def StepsAgree (A : Answers) (steps : List TaggedStep) : Prop :=
  ∀ step ∈ steps, ∀ event, step = .world event → SourceReplay.IsHash event.input → A event.input = event.answer
theorem monitorOK_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (hagree : StepsAgree A steps) (monitor : Monitor) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (steps.foldl (Monitor.step U A q published) monitor) := by
  induction steps generalizing monitor with
  | nil => exact h
  | cons step rest ih =>
      rw [List.foldl_cons]
      apply ih (fun s hs e he => hagree s (List.mem_cons_of_mem _ hs) e he)
      cases step with
      | world event => exact monitorOK_event U A q monitor event (hagree _ List.mem_cons_self event rfl) h
      | sign request output events => exact monitorOK_sign U A q published monitor request h
theorem monitorRun_clear (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (hsteps : StepsAgree A steps) (hverdict : EventsAgree A verdict)
    (hno : (monitorRun U A q published steps verdict).contact = false)
    (hcalls : (monitorRun U A q published steps verdict).calls ≤ q) :
    ∀ X ∈ (monitorRun U A q published steps verdict).seen, X ∈ U →
      Clear A (monitorRun U A q published steps verdict).known X (A (.inl (.inr X))) :=
  monitorOK_events U A q verdict hverdict _
    (monitorOK_steps U A q published steps hsteps _ (monitorOK_initial U A q)) hno hcalls
theorem contact_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput)
    (h : monitor.contact = true) : (monitor.query U A q X y).contact = true := by
  unfold Monitor.query; rw [if_pos h]; exact h
theorem contact_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (h : monitor.contact = true) : (monitor.event U A q event).contact = true := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact contact_query_mono U A q monitor X answer h
  · exact h
theorem contact_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (h : monitor.contact = true) : (events.foldl (Monitor.event U A q) monitor).contact = true := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (contact_event_mono U A q monitor event h)
theorem seen_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X Y : HashInput) (y : HashOutput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.query U A q X y).seen := by
  unfold Monitor.query
  split_ifs <;> simp [h]
theorem seen_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) (Y : HashInput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.event U A q event).seen := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact seen_query_mono U A q monitor X Y answer h
  · exact h
theorem seen_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (Y : HashInput) (h : Y ∈ monitor.seen) : Y ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (seen_event_mono U A q monitor event Y h)
theorem events_seen (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (hno : (events.foldl (Monitor.event U A q) monitor).contact = false) :
    ∀ event ∈ events, ∀ X, event.input = .inl (.inr X) → X ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => intro event he; cases he
  | cons event rest ih =>
      intro e he X hX
      rw [List.foldl_cons] at hno ⊢
      rcases List.mem_cons.mp he with rfl | he
      · apply seen_events_mono
        rcases e with ⟨before, (n | Y) | c, answer⟩
        · cases hX
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hX
          subst hX
          change Y ∈ (monitor.query U A q Y answer).seen
          by_cases hc : monitor.contact = true
          · exfalso
            have := contact_events_mono U A q rest _ (contact_event_mono U A q monitor ⟨before, .inl (.inr Y), answer⟩ hc)
            rw [hno] at this
            exact Bool.false_ne_true this
          · unfold Monitor.query
            rw [if_neg hc]
            split_ifs <;> exact List.mem_cons_self
        · cases hX
      · exact ih _ hno e he X hX
theorem disclosed_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).disclosed = monitor.disclosed := by
  unfold Monitor.query
  split_ifs <;> rfl
theorem disclosed_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).disclosed = monitor.disclosed := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact disclosed_query U A q monitor X answer
  · rfl
theorem disclosed_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).disclosed = monitor.disclosed := by
  induction events generalizing monitor with
  | nil => rfl
  | cons event rest ih => rw [List.foldl_cons, ih, disclosed_event]
theorem disclosed_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (monitor : Monitor) (c : Coord) (hc : c ∈ (steps.foldl (Monitor.step U A q published) monitor).disclosed) :
    c ∈ monitor.disclosed ∨ ∃ request, c ∈ signDisclosed A published request := by
  induction steps generalizing monitor with
  | nil => exact Or.inl hc
  | cons step rest ih =>
      rw [List.foldl_cons] at hc
      rcases ih _ hc with h | h
      · cases step with
        | world event =>
            change c ∈ (monitor.event U A q event).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request output events =>
            change c ∈ (monitor.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, h⟩
      · exact Or.inr h
theorem monitorRun_known (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (c : Coord) (hk : (monitorRun U A q published steps verdict).known c) :
    Known (fun d => d ∈ keygenDisclosed ∨ ∃ request, d ∈ signDisclosed A published request) c := by
  refine Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · unfold monitorRun at hd
    rw [disclosed_events] at hd
    rcases disclosed_steps U A q published steps Monitor.initial d hd with h | h
    · simp [Monitor.initial] at h
    · exact Or.inr h
theorem calls_query_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).calls ≤ monitor.calls + 1 := by
  unfold Monitor.query
  split_ifs <;> simp
theorem calls_event_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).calls ≤ monitor.calls + FullGame.queryCharge event.input := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact Nat.le_add_right _ _
  · have h1 : FullGame.queryCharge (.inl (.inr X)) = 1 := by
      simp [FullGame.queryCharge, Derivation.charged]
    rw [h1]
    exact calls_query_le U A q monitor X answer
  · exact Nat.le_add_right _ _
theorem calls_events_le (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).calls ≤ monitor.calls + chargeOf events := by
  induction events generalizing monitor with
  | nil => simp [chargeOf]
  | cons event rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.event U A q event)
      have h2 := calls_event_le U A q monitor event
      simp only [chargeOf, List.map_cons, List.sum_cons] at h1 ⊢
      omega
theorem calls_steps_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (monitor : Monitor) :
    (steps.foldl (Monitor.step U A q published) monitor).calls ≤ monitor.calls + chargeOf (steps.flatMap TaggedStep.events) := by
  induction steps generalizing monitor with
  | nil => simp [chargeOf]
  | cons step rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.step U A q published step)
      have h2 : (monitor.step U A q published step).calls ≤ monitor.calls + chargeOf step.events := by
        cases step with
        | world event =>
            have := calls_event_le U A q monitor event
            simp only [Monitor.step, TaggedStep.events, chargeOf, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this ⊢
            omega
        | sign request output events =>
            simp only [Monitor.step, Monitor.sign]
            split_ifs <;> simp
      simp only [chargeOf, List.flatMap_cons, List.map_append, List.sum_append] at h1 h2 ⊢
      omega
theorem monitorRun_calls_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    (monitorRun U A q published steps verdict).calls ≤ chargeOf (steps.flatMap TaggedStep.events ++ verdict) := by
  unfold monitorRun
  have h1 := calls_events_le U A q verdict (steps.foldl (Monitor.step U A q published) Monitor.initial)
  have h2 := calls_steps_le U A q published steps Monitor.initial
  have h0 : Monitor.initial.calls = 0 := rfl
  simp only [chargeOf, List.map_append, List.sum_append] at h1 h2 ⊢
  omega
end ClaudeWCT.W9.T3.Security.LargeCoupling

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (chargeOf EventsAgree)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
 | world (event : FirstHit.QueryEvent)
 | sign (request : Security.Request) (output : Option SigGolfCandidate.Research.SharedForest.Signature)
     (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
 | .world event => [event]
 | .sign _ _ events => events
structure Monitor where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  digests : Nat
  contact : Bool
def Monitor.initial : Monitor := ⟨[], [], 0, 0, false⟩
def Monitor.known (monitor : Monitor) : Coord → Prop :=
  LargeResidual.Paired.Known fun c => c ∈ keygenDisclosed ∨ c ∈ monitor.disclosed
noncomputable def Monitor.query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (input : HashInput) (answer : HashOutput) : Monitor :=
  if monitor.contact then monitor
  else if input ∉ monitor.seen ∧ input ∈ U ∧ monitor.calls + 1 ≤ q ∧ LargeResidual.Paired.ContactTest A monitor.known input answer then
    ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1, monitor.digests, true⟩
  else ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1,
    monitor.digests + (if input ∈ U ∧ IsDigestRow input ∧ monitor.calls + 1 ≤ q then 1 else 0), false⟩
noncomputable def Monitor.event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (event : FirstHit.QueryEvent) : Monitor :=
  match event with
  | ⟨_, .inl (.inr input), answer⟩ => monitor.query U A q input answer
  | _ => monitor
noncomputable def Monitor.sign (A : Answers) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor)
    (request : Security.Request) : Monitor :=
  if monitor.contact then monitor
  else ⟨monitor.disclosed ++ LargeResidual.Paired.signDisclosed A published request, monitor.seen, monitor.calls, monitor.digests, false⟩
noncomputable def Monitor.step (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (monitor : Monitor) : TaggedStep → Monitor
  | .world event => monitor.event U A q event
  | .sign request _ _ => monitor.sign A published request
noncomputable def monitorRun (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : Monitor :=
  verdict.foldl (Monitor.event U A q) (steps.foldl (Monitor.step U A q published) Monitor.initial)

def MonitorOK (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) : Prop :=
  monitor.contact = false → monitor.calls ≤ q → ∀ X ∈ monitor.seen, X ∈ U →
    LargeResidual.Paired.Clear A monitor.known X (A (.inl (.inr X)))
theorem monitorOK_initial (U : Finset HashInput) (A : Answers) (q : Nat) : MonitorOK U A q Monitor.initial := by
  intro _ _ X hX
  simp [Monitor.initial] at hX
theorem monitorOK_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.query U A q X (A (.inl (.inr X)))) := by
  unfold Monitor.query
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  by_cases ht : X ∉ monitor.seen ∧ X ∈ U ∧ monitor.calls + 1 ≤ q ∧ LargeResidual.Paired.ContactTest A monitor.known X (A (.inl (.inr X)))
  · rw [if_pos ht]
    intro hfalse
    simp at hfalse
  · rw [if_neg ht]
    intro _ hq Y hY hYU
    change monitor.calls + 1 ≤ q at hq
    have hcf : monitor.contact = false := by simpa using hc
    have hq' : monitor.calls ≤ q := by omega
    simp only [List.mem_cons] at hY
    change LargeResidual.Paired.Clear A monitor.known Y (A (.inl (.inr Y)))
    rcases hY with rfl | hY
    · by_cases hs : Y ∈ monitor.seen
      · exact h hcf hq' Y hs hYU
      · exact LargeResidual.Paired.clear_of_not_contact (fun hct => ht ⟨hs, hYU, hq, hct⟩)
    · exact h hcf hq' Y hY hYU
theorem monitorOK_sign (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor) (request : Security.Request)
    (h : MonitorOK U A q monitor) : MonitorOK U A q (monitor.sign A published request) := by
  unfold Monitor.sign
  by_cases hc : monitor.contact = true
  · rw [if_pos hc]; exact h
  rw [if_neg hc]
  intro _ hq Y hY hYU
  have hcf : monitor.contact = false := by simpa using hc
  refine (h hcf hq Y hY hYU).mono fun c hk => LargeResidual.Paired.Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (List.mem_append_left _ hd)
theorem monitorOK_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (hagree : SourceReplay.IsHash event.input → A event.input = event.answer) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (monitor.event U A q event) := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · have hagree' : A (.inl (.inr X)) = answer := hagree trivial
    subst hagree'
    exact monitorOK_query U A q monitor X h
  · exact h
theorem monitorOK_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (hagree : EventsAgree A events)
    (monitor : Monitor) (h : MonitorOK U A q monitor) : MonitorOK U A q (events.foldl (Monitor.event U A q) monitor) := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih =>
      rw [List.foldl_cons]
      exact ih (fun e he => hagree e (List.mem_cons_of_mem _ he)) _
        (monitorOK_event U A q monitor event (hagree event List.mem_cons_self) h)
def StepsAgree (A : Answers) (steps : List TaggedStep) : Prop :=
  ∀ step ∈ steps, ∀ event, step = .world event → SourceReplay.IsHash event.input → A event.input = event.answer
theorem monitorOK_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (hagree : StepsAgree A steps) (monitor : Monitor) (h : MonitorOK U A q monitor) :
    MonitorOK U A q (steps.foldl (Monitor.step U A q published) monitor) := by
  induction steps generalizing monitor with
  | nil => exact h
  | cons step rest ih =>
      rw [List.foldl_cons]
      apply ih (fun s hs e he => hagree s (List.mem_cons_of_mem _ hs) e he)
      cases step with
      | world event => exact monitorOK_event U A q monitor event (hagree _ List.mem_cons_self event rfl) h
      | sign request output events => exact monitorOK_sign U A q published monitor request h
theorem monitorRun_clear (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (hsteps : StepsAgree A steps) (hverdict : EventsAgree A verdict)
    (hno : (monitorRun U A q published steps verdict).contact = false)
    (hcalls : (monitorRun U A q published steps verdict).calls ≤ q) :
    ∀ X ∈ (monitorRun U A q published steps verdict).seen, X ∈ U →
      LargeResidual.Paired.Clear A (monitorRun U A q published steps verdict).known X (A (.inl (.inr X))) :=
  monitorOK_events U A q verdict hverdict _
    (monitorOK_steps U A q published steps hsteps _ (monitorOK_initial U A q)) hno hcalls
theorem contact_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput)
    (h : monitor.contact = true) : (monitor.query U A q X y).contact = true := by
  unfold Monitor.query; rw [if_pos h]; exact h
theorem contact_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent)
    (h : monitor.contact = true) : (monitor.event U A q event).contact = true := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact contact_query_mono U A q monitor X answer h
  · exact h
theorem contact_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (h : monitor.contact = true) : (events.foldl (Monitor.event U A q) monitor).contact = true := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (contact_event_mono U A q monitor event h)
theorem seen_query_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X Y : HashInput) (y : HashOutput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.query U A q X y).seen := by
  unfold Monitor.query
  split_ifs <;> simp [h]
theorem seen_event_mono (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) (Y : HashInput)
    (h : Y ∈ monitor.seen) : Y ∈ (monitor.event U A q event).seen := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact h
  · exact seen_query_mono U A q monitor X Y answer h
  · exact h
theorem seen_events_mono (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (Y : HashInput) (h : Y ∈ monitor.seen) : Y ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => exact h
  | cons event rest ih => exact ih _ (seen_event_mono U A q monitor event Y h)
theorem events_seen (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor)
    (hno : (events.foldl (Monitor.event U A q) monitor).contact = false) :
    ∀ event ∈ events, ∀ X, event.input = .inl (.inr X) → X ∈ (events.foldl (Monitor.event U A q) monitor).seen := by
  induction events generalizing monitor with
  | nil => intro event he; cases he
  | cons event rest ih =>
      intro e he X hX
      rw [List.foldl_cons] at hno ⊢
      rcases List.mem_cons.mp he with rfl | he
      · apply seen_events_mono
        rcases e with ⟨before, (n | Y) | c, answer⟩
        · cases hX
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hX
          subst hX
          change Y ∈ (monitor.query U A q Y answer).seen
          by_cases hc : monitor.contact = true
          · exfalso
            have := contact_events_mono U A q rest _ (contact_event_mono U A q monitor ⟨before, .inl (.inr Y), answer⟩ hc)
            rw [hno] at this
            exact Bool.false_ne_true this
          · unfold Monitor.query
            rw [if_neg hc]
            split_ifs <;> exact List.mem_cons_self
        · cases hX
      · exact ih _ hno e he X hX
theorem disclosed_query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).disclosed = monitor.disclosed := by
  unfold Monitor.query
  split_ifs <;> rfl
theorem disclosed_event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).disclosed = monitor.disclosed := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact disclosed_query U A q monitor X answer
  · rfl
theorem disclosed_events (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).disclosed = monitor.disclosed := by
  induction events generalizing monitor with
  | nil => rfl
  | cons event rest ih => rw [List.foldl_cons, ih, disclosed_event]
theorem disclosed_steps (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (monitor : Monitor) (c : Coord) (hc : c ∈ (steps.foldl (Monitor.step U A q published) monitor).disclosed) :
    c ∈ monitor.disclosed ∨ ∃ request, c ∈ LargeResidual.Paired.signDisclosed A published request := by
  induction steps generalizing monitor with
  | nil => exact Or.inl hc
  | cons step rest ih =>
      rw [List.foldl_cons] at hc
      rcases ih _ hc with h | h
      · cases step with
        | world event =>
            change c ∈ (monitor.event U A q event).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request output events =>
            change c ∈ (monitor.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, h⟩
      · exact Or.inr h
theorem monitorRun_known (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) (c : Coord) (hk : (monitorRun U A q published steps verdict).known c) :
    LargeResidual.Paired.Known (fun d => d ∈ keygenDisclosed ∨ ∃ request, d ∈ LargeResidual.Paired.signDisclosed A published request) c := by
  refine LargeResidual.Paired.Known.mono (fun d hd => ?_) hk
  rcases hd with hd | hd
  · exact Or.inl hd
  · unfold monitorRun at hd
    rw [disclosed_events] at hd
    rcases disclosed_steps U A q published steps Monitor.initial d hd with h | h
    · simp [Monitor.initial] at h
    · exact Or.inr h
theorem calls_query_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (X : HashInput) (y : HashOutput) :
    (monitor.query U A q X y).calls ≤ monitor.calls + 1 := by
  unfold Monitor.query
  split_ifs <;> simp
theorem calls_event_le (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor) (event : FirstHit.QueryEvent) :
    (monitor.event U A q event).calls ≤ monitor.calls + FullGame.queryCharge event.input := by
  rcases event with ⟨before, (n | X) | c, answer⟩
  · exact Nat.le_add_right _ _
  · have h1 : FullGame.queryCharge (.inl (.inr X)) = 1 := by
      simp [FullGame.queryCharge, Derivation.charged]
    rw [h1]
    exact calls_query_le U A q monitor X answer
  · exact Nat.le_add_right _ _
theorem calls_events_le (U : Finset HashInput) (A : Answers) (q : Nat) (events : List FirstHit.QueryEvent) (monitor : Monitor) :
    (events.foldl (Monitor.event U A q) monitor).calls ≤ monitor.calls + chargeOf events := by
  induction events generalizing monitor with
  | nil => simp [chargeOf]
  | cons event rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.event U A q event)
      have h2 := calls_event_le U A q monitor event
      simp only [chargeOf, List.map_cons, List.sum_cons] at h1 ⊢
      omega
theorem calls_steps_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) (monitor : Monitor) :
    (steps.foldl (Monitor.step U A q published) monitor).calls ≤ monitor.calls + chargeOf (steps.flatMap TaggedStep.events) := by
  induction steps generalizing monitor with
  | nil => simp [chargeOf]
  | cons step rest ih =>
      rw [List.foldl_cons]
      have h1 := ih (monitor.step U A q published step)
      have h2 : (monitor.step U A q published step).calls ≤ monitor.calls + chargeOf step.events := by
        cases step with
        | world event =>
            have := calls_event_le U A q monitor event
            simp only [Monitor.step, TaggedStep.events, chargeOf, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] at this ⊢
            omega
        | sign request output events =>
            simp only [Monitor.step, Monitor.sign]
            split_ifs <;> simp
      simp only [chargeOf, List.flatMap_cons, List.map_append, List.sum_append] at h1 h2 ⊢
      omega
theorem monitorRun_calls_le (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    (monitorRun U A q published steps verdict).calls ≤ chargeOf (steps.flatMap TaggedStep.events ++ verdict) := by
  unfold monitorRun
  have h1 := calls_events_le U A q verdict (steps.foldl (Monitor.step U A q published) Monitor.initial)
  have h2 := calls_steps_le U A q published steps Monitor.initial
  have h0 : Monitor.initial.calls = 0 := rfl
  simp only [chargeOf, List.map_append, List.sum_append] at h1 h2 ⊢
  omega

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_prefix_unique queryEvent_answer_eq)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure Tagged (α : Type) where
  value : α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (PairedOuter.FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)) (tagged : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
theorem taggedRecord_pure {α : Type} (published : SigGolfCandidate.T3.Cache) (value : α) (state : LazyPrivate.State) :
    taggedRecord published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedRecord_world {α : Type} (published : SigGolfCandidate.T3.Cache) (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedRecord published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl input))) state
      (fun last => (⟨last.value, .world ⟨state, .inl input, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next middle.1) middle.2) := rfl
theorem taggedRecord_request {α : Type} (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedRecord published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← FirstHit.record (PairedOuter.FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedRecord published (next block.value) block.state) := rfl
def Tagged.untag {α : Type} (tagged : Tagged α) : FirstHit.Recorded (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :=
  ⟨tagged.value, tagged.events, tagged.state⟩
theorem taggedRecord_untag {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (tagged : Tagged α) (h : tagged ∈ support (taggedRecord published program state)) :
    tagged.untag ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)
      state) := by
  induction program using OracleComp.inductionOn generalizing state tagged with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h
      subst h
      rw [PairedOuter.FullGame.loggedWith_pure, FirstHit.record_pure, mem_support_pure_iff]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h
          obtain ⟨middle, hm, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih middle.1 middle.2 last hl
          rw [PairedOuter.FullGame.loggedWith_world]
          change _ ∈ support (FirstHit.record (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) state)
          rw [FirstHit.record_query_bind, mem_support_bind_iff]
          refine ⟨middle, hm, ?_⟩
          rw [support_map]
          exact ⟨last.untag, hu, rfl⟩
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h
          obtain ⟨block, hb, h⟩ := h
          rw [support_map] at h
          obtain ⟨last, hl, rfl⟩ := h
          have hu := ih block.value block.state last hl
          rw [PairedOuter.FullGame.loggedWith_request, FirstHit.record_bind, mem_support_bind_iff]
          refine ⟨block, hb, ?_⟩
          rw [mem_support_bind_iff]
          rw [FirstHit.record_map, support_map] at *
          refine ⟨⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2), last.events, last.state⟩,
            ⟨last.untag, hu, rfl⟩, ?_⟩
          rw [mem_support_pure_iff]
          simp only [Tagged.untag, Tagged.events, List.flatMap_cons, TaggedStep.events]
theorem TaggedSplit.untag {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {tagged : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP)}
    {checked : FirstHit.Recorded Bool} (h : TaggedSplit adversary result generated tagged checked) :
    generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
    tagged.untag ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
    checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 tagged.untag.value)
      tagged.untag.state) ∧
    result = ⟨checked.value, generated.events ++ (tagged.untag.events ++ checked.events), checked.state⟩ := by
  obtain ⟨hg, ht, hc, hr⟩ := h
  exact ⟨hg, taggedRecord_untag _ _ _ _ ht, hc, hr⟩
theorem taggedRecord_prefix_unique {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) (t1 t2 : Tagged α) (h1 : t1 ∈ support (taggedRecord published program state))
    (h2 : t2 ∈ support (taggedRecord published program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : t1.events ++ rest1 = t2.events ++ rest2) : t1 = t2 := by
  induction program using OracleComp.inductionOn generalizing state t1 t2 rest1 rest2 with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at h1 h2
          obtain ⟨m1, hm1, h1⟩ := h1
          obtain ⟨m2, hm2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events,
            List.cons_append, List.cons.injEq] at heq
          have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
          have hs1 := FirstHit.query_advance state (.inl input) m1 hm1
          have hs2 := FirstHit.query_advance state (.inl input) m2 hm2
          have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
          subst hm
          have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
          rw [hl]
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at h1 h2
          obtain ⟨b1, hb1, h1⟩ := h1
          obtain ⟨b2, hb2, h2⟩ := h2
          rw [support_map] at h1 h2
          obtain ⟨l1, hl1, rfl⟩ := h1
          obtain ⟨l2, hl2, rfl⟩ := h2
          simp only [Tagged.events, List.flatMap_cons, TaggedStep.events, List.append_assoc] at heq
          have hb := record_prefix_unique _ state b1 b2 hb1 hb2 _ _ heq
          subst hb
          have heq' := List.append_cancel_left heq
          have hl := ih b1.value b1.state l1 l2 hl1 hl2 rest1 rest2 heq'
          rw [hl]
theorem taggedSplit_unique {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} {result : FirstHit.Recorded Bool}
    {g1 g2 : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)} {t1 t2 : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP)}
    {c1 c2 : FirstHit.Recorded Bool}
    (h1 : TaggedSplit adversary result g1 t1 c1) (h2 : TaggedSplit adversary result g2 t2 c2) :
    g1 = g2 ∧ t1 = t2 ∧ c1 = c2 := by
  obtain ⟨hg1, ht1, hc1, hr1⟩ := h1
  obtain ⟨hg2, ht2, hc2, hr2⟩ := h2
  have hevents : g1.events ++ (t1.events ++ c1.events) = g2.events ++ (t2.events ++ c2.events) := by
    have := congrArg FirstHit.Recorded.events (hr1.symm.trans hr2)
    simpa using this
  have hg := record_prefix_unique keygen (∅, ∅) g1 g2 hg1 hg2 _ _ hevents
  subst hg
  have hevents' := List.append_cancel_left hevents
  have ht := taggedRecord_prefix_unique _ _ _ t1 t2 ht1 ht2 _ _ hevents'
  subst ht
  have hevents'' := List.append_cancel_left hevents'
  have hc := record_prefix_unique _ _ c1 c2 hc1 hc2 [] [] (by simpa using hevents'')
  exact ⟨rfl, rfl, hc⟩

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_prefix_unique queryEvent_answer_eq)
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def taggedFixed {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) : LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let answer ← Wots.Ref.fixedWorld F (.inl world)
          (fun last => (⟨last.value, .world ⟨state, .inl world, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next answer (FirstHit.advance state (.inl world) answer)
      | .inr request, next => do
          let block ← Wots.Ref.fixedRecord F (PairedOuter.FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
section Fixed
variable {α : Type} (F : Answers) (published : SigGolfCandidate.T3.Cache)
theorem taggedFixed_pure (value : α) (state : LazyPrivate.State) :
    taggedFixed F published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) state =
      pure ⟨(value, []), [], state⟩ := rfl
theorem taggedFixed_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α)
    (state : LazyPrivate.State) :
    taggedFixed F published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) state = (do
      let answer ← Wots.Ref.fixedWorld F (.inl input)
      (fun last => (⟨last.value, .world ⟨state, .inl input, answer⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next answer) (FirstHit.advance state (.inl input) answer)) := rfl
theorem taggedFixed_request (request : Security.Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    taggedFixed F published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) state = (do
      let block ← Wots.Ref.fixedRecord F (PairedOuter.FullGame.authenticatedSign published request) state
      (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
          .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
        taggedFixed F published (next block.value) block.state) := rfl
theorem taggedFixed_support (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State)
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
theorem taggedFixed_untag (program : OracleComp PairedOuter.LazyPrivate.Interaction α) (state : LazyPrivate.State) :
    Tagged.untag <$> taggedFixed F published program state =
      Wots.Ref.fixedRecord F (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [taggedFixed_pure, map_pure, PairedOuter.FullGame.loggedWith_pure, Wots.Ref.fixedRecord_pure]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedFixed_world, PairedOuter.FullGame.loggedWith_world]
          change _ = Wots.Ref.fixedRecord F (liftM (SigGolfCandidate.T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer)) state
          rw [Wots.Ref.fixedRecord_query_bind, map_bind]
          apply bind_congr
          intro answer
          rw [Functor.map_map, ← ih answer]
          simp only [Functor.map_map]
          rfl
      | inr request =>
          rw [taggedFixed_request, PairedOuter.FullGame.loggedWith_request, Wots.Ref.fixedRecord_bind, map_bind]
          apply bind_congr
          intro block
          rw [Wots.Ref.fixedRecord_map, ← ih block.value, Functor.map_map, Functor.map_map,
            map_eq_bind_pure_comp]
          simp only [Function.comp_def, bind_pure_comp, Functor.map_map]
          rfl
end Fixed
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
def Contact (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked →
    (monitorRun (Wots.PairedReference.referenceInputs adversary) z.2 q generated.value.2 tagged.steps checked.events).contact = true
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
