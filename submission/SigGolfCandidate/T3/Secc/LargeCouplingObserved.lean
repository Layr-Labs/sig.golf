import SigGolfCandidate.T3.Secc.LargeResidualRouter

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
theorem runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    runWith impl (comp >>= k) s =
      (runWith impl comp s >>= fun r => r.1.elim (pure (none, r.2)) (fun v => runWith impl (k v) r.2)) := by
  simp only [runWith, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (simulateQ impl comp).run.run s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v <;> rfl
theorem runWith_map {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (f : α → β) (comp : OracleComp (World auxSpec Coord Cell) α) (s : State Coord Cell) :
    runWith impl (f <$> comp) s = (fun r => (r.1.map f, r.2)) <$> runWith impl comp s := by
  rw [map_eq_bind_pure_comp, runWith_bind, map_eq_bind_pure_comp]
  apply congrArg (fun continuation => runWith impl comp s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => rfl
  | some v => simp only [Option.elim_some, Function.comp_def, runWith_pure, Option.map_some]
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
  (labels : Coord → Digest) (table : Cell → HashOutput)
end Generic
end SigGolfCandidate.T3.Security.LargeResidual
