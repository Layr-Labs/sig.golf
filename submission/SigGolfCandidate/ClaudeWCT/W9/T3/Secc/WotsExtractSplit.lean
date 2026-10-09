import SigGolfCandidate.T3.Secc.WotsExtractSplit
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportSplit

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots (Entry entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (recordedEntries entries_recorded)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
theorem verdict_accepting (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    interaction.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.1 = some forgery ∧ PaddedExtraction.Fresh interaction.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
        evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
        ∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message publicKey witness) →
          ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
            result.events := by
  cases hf : interaction.1 with
  | none =>
      simp only [GameWith.verdict, hf, FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
      obtain ⟨checked, hchecked, last, hlast, hvalue, hevents, hstate⟩ :=
        FirstHit.record_bind_support _ _ before result hr
      rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
      subst last
      simp only [List.append_nil] at hevents
      have hand : (decide (interaction.2.length ≤ 2 ^ 32) && checked.value) = true := hvalue.symm.trans hwin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
      obtain ⟨hlength, hcheckedWin⟩ := hand
      have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
        simpa only [hstate] using ha
      have hp := PaddedExtraction.check_hashOnly publicKey interaction.2 forgery
      have hw := (SourceReplay.resolves_of_run _ hp before (checked.value, checked.state)
        (FirstHit.recorded_support _ _ _ hchecked)).eval answers hac
      rw [hcheckedWin] at hw
      obtain ⟨hfresh, message, witness, hof, hv, hsub⟩ :=
        PaddedExtraction.check_accepting answers publicKey interaction.2 forgery hw
      refine ⟨hlength, forgery, rfl, hfresh, message, witness, hof, hv, fun input hq => ?_⟩
      obtain ⟨prior, hev⟩ := PaddedExtraction.public_occurrence _ hp before checked hchecked answers hac input
        (hsub _ hq)
      exact ⟨prior, hevents ▸ hev⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen verifyP expandB
end ClaudeWCT.W9.T3.Security.Wots
