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
def GameCaseWots (adversary : AdversaryP) (answers : Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        evalWithAnswerFn answers (verifyP message generated.value.1 witness) = true ∧
        (∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message generated.value.1 witness) →
          ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
            result.events) ∧
        WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP message generated.value.1 witness)))
theorem GameCaseWots.recordedSrc {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitiveSrc answers (recordedEntries answers result.events) := by
  obtain ⟨_generated, _hg, _interaction, _hi, _hext, _hpk, _hlen, _forgery, _hf, _hfresh, _message, _witness, _hof,
    _hv, hrec, hprim⟩ := h
  exact WotsPrimitiveSrc.mono hprim (entries_recorded hrec)
theorem GameCaseWots.recorded {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitive answers (recordedEntries answers result.events) :=
  h.recordedSrc.toPrimitive
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
