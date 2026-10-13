import SigGolfCandidate.T3.Secc.LargeContactEvents
import SigGolfCandidate.T3.Secc.LargeContactInputs
import SigGolfCandidate.T3.Secc.WotsExtractSplit

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem record_events_known {α : Type} (program : M α) (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) :
    ∀ event ∈ result.events, SourceReplay.IsHash event.input →
      SourceReplay.known result.state event.input = some event.answer := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at hr
      subst hr
      intro event he; cases he
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hl, rfl⟩ := hr
      have hext := SourceReplay.run_extends (next middle.1) middle.2 (last.value, last.state)
        (FirstHit.recorded_support _ _ _ hl)
      intro event he hi
      rcases List.mem_cons.mp he with rfl | he
      · exact SourceReplay.known_mono middle.2 last.state hext
          (SourceReplay.hash_query_caches input hi before middle hm)
      · exact ih middle.1 middle.2 last hl event he hi
end SigGolfCandidate.T3.Security.LargeCoupling
