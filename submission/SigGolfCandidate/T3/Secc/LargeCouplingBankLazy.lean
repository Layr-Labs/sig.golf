import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs

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
section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
theorem ev_runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) (pay : Option β × State Coord Cell → ENNReal) :
    expectedValue (runWith impl (comp >>= k) s) pay =
      expectedValue (runWith impl comp s) (fun r => r.1.elim (pay (none, r.2))
        (fun v => expectedValue (runWith impl (k v) r.2) pay)) := by
  rw [runWith_bind, expectedValue_bind]
  congr 1
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => simp only [Option.elim_none, expectedValue_pure]
  | some v => rfl
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
theorem ev_observe_le {Answer Result : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (g : Result → ENNReal) (B : ENNReal)
    (hs : expectedValue stopped g ≤ B) (hn : ∀ y, expectedValue (next y) g ≤ B) :
    expectedValue (observe response stopped next) g ≤ B := by
  unfold observe
  rw [expectedValue_bind]
  apply expectedValue_le_of_le
  intro o
  cases o with
  | none => exact hs
  | some y => exact hn y
theorem ev_bind_le {α β : Type} (mx : SPMF α) (f : α → SPMF β) (g : β → ENNReal) (B : ENNReal)
    (h : ∀ x, expectedValue (f x) g ≤ B) : expectedValue (mx >>= f) g ≤ B := by
  rw [expectedValue_bind]
  exact expectedValue_le_of_le _ h
end Generic
section Router
end Router
end SigGolfCandidate.T3.Security.LargeCoupling
