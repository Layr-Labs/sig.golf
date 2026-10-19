import SigGolfCandidate.T3_Secc_LargeCouplingSplit

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def EventsAgree (A : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∀ event ∈ events, SourceReplay.IsHash event.input → A event.input = event.answer
def chargeOf (events : List FirstHit.QueryEvent) : Nat := (events.map fun event => FullGame.queryCharge event.input).sum
end SigGolfCandidate.T3.Security.LargeCoupling
