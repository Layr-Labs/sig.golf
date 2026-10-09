import SigGolfCandidate.T3.Secc.WotsRestartBase

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
variable {adversary : AdversaryP}
theorem first_stop_iff {trace memory : List Entry} (S C : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) (hC : ∀ j k, j ≤ k → C (trace.take j) → C (trace.take k)) :
    (∃ k, S (trace.take k) ∧ ¬C (trace.take k) ∧ C trace) ↔ (S memory ∧ ¬C memory ∧ C trace) := by
  constructor
  · rintro ⟨k, hs, hnc, hct⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    have hnm : ¬C memory := fun hcm => hnc (hC _ _ hk (hm ▸ hcm))
    refine ⟨?_, hnm, hct⟩
    rcases hc with hc | hc
    · exact hc
    · exact absurd (hc ▸ hct) hnm
  · rintro ⟨hs, hnc, hct⟩
    exact ⟨memory.length, hm ▸ hs, hm ▸ hnc, hct⟩
theorem first_stop_exists_iff {trace memory : List Entry} (S : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) : (∃ k, S (trace.take k)) ↔ S memory := by
  constructor
  · rintro ⟨k, hs⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    rcases hc with hc | hc
    · exact hc
    · have : trace.take k = memory := by
        rw [hc]; exact List.take_of_length_le (by rw [← hc]; exact hk)
      exact this ▸ hs
  · intro hs
    exact ⟨memory.length, hm ▸ hs⟩
end PrefixGame
namespace PrefixGame
variable {adversary : AdversaryP}
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
