import SigGolfCandidate.T3.Secc.CaseCFull
import SigGolfCandidate.T3.Secc.LargeContactWalk
import SigGolfCandidate.T3.Secc.PairGuessFinal

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem mem_publicEntries {events : List FirstHit.QueryEvent} {prior : LazyPrivate.State} {input : HashInput}
    {answer : HashOutput} (h : (⟨prior, .inl (.inr input), answer⟩ : FirstHit.QueryEvent) ∈ events) :
    (input, answer) ∈ BPair.publicEntries events := by
  unfold BPair.publicEntries
  rw [List.mem_filterMap]
  exact ⟨_, h, rfl⟩
end SigGolfCandidate.T3.Security.CaseC
