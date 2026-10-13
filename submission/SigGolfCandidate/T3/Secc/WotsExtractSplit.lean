import SigGolfCandidate.T3.Secc.WotsExtractVerify
import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
def recordedEntries (answers : Answers) (events : List FirstHit.QueryEvent) : List Entry :=
  entriesOf answers (events.map FirstHit.QueryEvent.input)
theorem entries_recorded {answers : Answers} {qs : List Spec.Domain} {events : List FirstHit.QueryEvent}
    (hrec : ∀ input, (.inl (.inr input) : Spec.Domain) ∈ qs →
      ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈ events) :
    ∀ e ∈ entriesOf answers qs, e ∈ recordedEntries answers events := by
  rintro ⟨input, answer⟩ he
  obtain ⟨hq, ha⟩ := mem_entriesOf_iff.mp he
  obtain ⟨prior, hev⟩ := hrec input hq
  exact mem_entriesOf_iff.mpr ⟨List.mem_map.mpr ⟨_, hev, rfl⟩, ha⟩
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen verifyP expandB
end SigGolfCandidate.T3.Security.Wots
