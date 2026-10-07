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
def VerifierWotsSrc (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
theorem VerifierWotsSrc.toVerifierWots {answers : Answers} {publicKey : Digest} {forgery : ForgeryP}
    (h : VerifierWotsSrc answers publicKey forgery) : VerifierWots answers publicKey forgery := by
  obtain ⟨message, witness, hof, hv, hp⟩ := h
  exact ⟨message, witness, hof, hv, hp.toPrimitive⟩
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
theorem game_accepting_linked (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        SourceReplay.Extends interaction.state result.state ∧
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        interaction.value.2.length ≤ 2 ^ 32 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
            evalWithAnswerFn answers (verifyP message generated.value.1 witness) = true ∧
            ∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message generated.value.1 witness) →
              ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
                result.events := by
  unfold GameWith.idealGame at hr
  obtain ⟨generated, hgenerated, rest, hrest, hvalue, hevents, hstate⟩ :=
    FirstHit.record_bind_support _ _ (∅, ∅) result hr
  obtain ⟨interaction, hinteraction, checked, hchecked, hrestValue, hrestEvents, hrestState⟩ :=
    FirstHit.record_bind_support _ _ generated.state rest hrest
  have hgeneratedState : SourceReplay.Extends generated.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ generated.state (rest.value, rest.state)
      (FirstHit.recorded_support _ _ _ hrest)
  have hinteractionState : SourceReplay.Extends interaction.state result.state := by
    rw [hstate, hrestState]
    exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
      (FirstHit.recorded_support _ _ _ hchecked)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.hashOnly_keygen (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hgenerated)).eval answers
        (fun input answer hk => ha input answer
          (SourceReplay.known_mono generated.state result.state hgeneratedState hk))
  have hpk : generated.value.1 = Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk answers
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
    simpa only [hstate, hrestState] using ha
  have hw : checked.value = true := hrestValue.symm.trans (hvalue.symm.trans hwin)
  obtain ⟨hlength, forgery, hforgery, hfresh, message, witness, hof, hv, hrec⟩ :=
    verdict_accepting generated.value.1 interaction.value interaction.state checked hchecked answers hac hw
  refine ⟨generated, hgenerated, interaction, hinteraction, hinteractionState, hpk, hlength, forgery, hforgery,
    hfresh, message, witness, hof, hv, fun input hq => ?_⟩
  obtain ⟨prior, hev⟩ := hrec input hq
  refine ⟨prior, ?_⟩
  rw [hevents, hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ hev)
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
theorem GameCaseWots.verifierWots {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          VerifierWots answers generated.value.1 forgery := by
  obtain ⟨generated, hg, interaction, hi, -, hpk, -, forgery, hf, hfresh, message, witness, hof, hv, -, hprim⟩ := h
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, message, witness, hof, hv, hprim.toPrimitive⟩
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
