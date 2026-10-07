import SigGolfCandidate.T3.Secc.LargeCouplingSigning

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
noncomputable local instance instDecidableEqCache_largeCouplingVerdict : DecidableEq T3.Cache := Classical.decEq _
section Monitor
variable (U : Finset HashInput) (A : Answers) (q : Nat)
theorem query_frozen (mon : Monitor) (h : mon.contact = true) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon := by
  unfold Monitor.query; rw [if_pos h]
theorem event_frozen (mon : Monitor) (h : mon.contact = true) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_frozen U A q mon h X answer
  · rfl
theorem events_frozen (mon : Monitor) (h : mon.contact = true) (events : List FirstHit.QueryEvent) :
    events.foldl (Monitor.event U A q) mon = mon := by
  induction events with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, event_frozen U A q mon h e, ih]
theorem query_over (mon : Monitor) (hc : mon.contact = false) (hq : q ≤ mon.calls) (X : HashInput)
    (y : HashOutput) : (mon.query U A q X y).contact = false ∧ q < (mon.query U A q X y).calls := by
  unfold Monitor.query
  rw [if_neg (by rw [hc]; decide), if_neg (fun h => by omega)]
  exact ⟨rfl, show q < mon.calls + 1 by omega⟩
theorem event_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (e : FirstHit.QueryEvent) :
    (mon.event U A q e).contact = false ∧ q < (mon.event U A q e).calls := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · exact ⟨hc, hq⟩
  · exact query_over U A q mon hc (by omega) X answer
  · exact ⟨hc, hq⟩
theorem events_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (events : List FirstHit.QueryEvent) :
    (events.foldl (Monitor.event U A q) mon).contact = false ∧ q < (events.foldl (Monitor.event U A q) mon).calls := by
  induction events generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := event_over U A q mon hc hq e
      exact ih _ h1 h2
end Monitor
noncomputable def routerEvent (U : Finset HashInput) (st : RouterState) (e : FirstHit.QueryEvent) : RouterState :=
  match e with
  | ⟨_, .inl (.inr X), y⟩ => st.next U X y
  | _ => st
def PhaseOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) {β : Type} (monF : Monitor) (value : β) (stF : RouterState)
    (out : Option (Option (β × RouterState))) (ws' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (out = none ∧ monF.contact = true ∧ ws'.counters.calls ≤ q) ∨
    (out = some none ∧ monF.contact = false ∧ q < monF.calls) ∨
    (out = some (some (value, stF)) ∧ Rel U T vals nv τ a q monF stF ws')
section Verdict
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem routeVerdict_pure {β : Type} (v : β) (st : RouterState) :
    routeVerdict U a q (pure v : M β) st = pure (some (v, st)) := rfl
theorem routeVerdict_public {β : Type} (X : HashInput) (next : HashOutput → M β) (st : RouterState) :
    routeVerdict U a q (liftM (T3.Spec.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else (routeQuery U a st X >>= fun r => routeVerdict U a q (next r.1) r.2) := rfl
end Verdict
end SigGolfCandidate.T3.Security.LargeCoupling
