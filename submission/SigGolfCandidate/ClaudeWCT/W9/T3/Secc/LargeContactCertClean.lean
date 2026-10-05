import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportSplit
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.T3.Secc.LargeContactCertClean

section











namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots (Entry entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (recordedEntries entries_recorded)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
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
theorem game_linked_split (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) (hcomp : BPB.SignerComplete answers) :
    GameCaseWots adversary answers result ∨ BPB.GameCaseC adversary answers Not result ∨
      BPB.GameCaseC adversary answers id result := by
  obtain ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hv, hrec⟩ :=
    game_accepting_linked adversary result hr answers ha hwin
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_wots_cases_src answers message generated.value.1 witness hpk hv
  rcases hcase with hprim | ⟨hgood, hshape⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hv,
      hrec, hprim⟩
  · have hCat : BPB.CaseCAt answers message witness result.events := by
      obtain ⟨prior, hev⟩ := hrec _ hdq
      have hans : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness))))) = N := hN
      exact ⟨N, hdc, hN, ⟨prior, by simpa only [hans] using hev⟩, hS, hgood, hshape, hcomp⟩
    by_cases hsd : BPB.SignedDigest interaction.value.2 message witness
    · exact Or.inr (Or.inr ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)
    · exact Or.inr (Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)
theorem completed_linked_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hcomp : BPB.SignerComplete z.2) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z ∨
      BPB.CaseCSigned adversary z := by
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  exact game_linked_split adversary _ (PaddedExtraction.traced_record_support adversary q hq z.1 hr) z.2 ha hwin.1 hcomp
theorem completed_linked_split_events (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hcomp : BPB.SignerComplete z.2) :
    WotsPrimitiveSrc z.2 (recordedEntries z.2 (QueryRecorded.recordedTrace z.1).events) ∨
      BPB.CaseCFresh adversary z ∨ BPB.CaseCSigned adversary z :=
  (completed_linked_split adversary q hq z hz hwin hcomp).imp_left GameCaseWots.recordedSrc
theorem completed_linked_split_fresh (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hcomp : BPB.SignerComplete z.2) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z := by
  rcases completed_linked_split adversary q hq z hz hwin hcomp with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin h).elim
theorem traced_wots_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult) (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q result) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWotsSrc answers generated.value.1 forgery ∨ VerifierAllGood answers generated.value.1 forgery) := by
  obtain ⟨generated, hgenerated, interaction, hinteraction, -, hpk, -, forgery, hforgery, hfresh, message, witness,
    hof, hv, -⟩ := game_accepting_linked adversary _ (PaddedExtraction.traced_record_support adversary q hq result hr)
      answers ha hwin.1
  refine ⟨generated, hgenerated, interaction, hinteraction, hpk, forgery, hforgery, hfresh, ?_⟩
  obtain ⟨N, -, hN, -, -, hcase⟩ := verifyP_wots_cases_src answers message generated.value.1 witness hpk hv
  rcases hcase with hprim | ⟨hgood, hshape⟩
  · exact Or.inl ⟨message, witness, hof, hv, hprim⟩
  · exact Or.inr ⟨message, witness, N, hof, hN, hgood, hshape⟩
theorem completed_wots_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot z.2 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWotsSrc z.2 generated.value.1 forgery ∨ VerifierAllGood z.2 generated.value.1 forgery) := by
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  exact traced_wots_split_src adversary q hq z.1 hr hwin z.2 ha
theorem completed_wots_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot z.2 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWots z.2 generated.value.1 forgery ∨ VerifierAllGood z.2 generated.value.1 forgery) := by
  obtain ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase⟩ :=
    completed_wots_split_src adversary q hq z hz hwin
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase.imp_left VerifierWotsSrc.toVerifierWots⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen verifyP expandB
theorem traced_wots_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult) (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q result) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWots answers generated.value.1 forgery ∨ VerifierAllGood answers generated.value.1 forgery) := by
  obtain ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase⟩ :=
    traced_wots_split_src adversary q hq result hr hwin answers ha
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase.imp_left VerifierWotsSrc.toVerifierWots⟩
end ClaudeWCT.W9.T3.Security.Wots
end

section











section
namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wrho wdc layerP wchainPads wchainHeaderPad wmerklePad wpath wvalue)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveRoute (index : Nat) (answers : Answers) (trace : List Entry) : Prop :=
  (∃ lay, EncodingMatchAt answers trace (routeLeaf index lay)) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
theorem WotsPrimitiveRoute.mono {index : Nat} {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitiveRoute index answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveRoute index answers trace' := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨lay, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
theorem frame_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hmerkle : ∀ j, j < height lay →
      wpath w lay (route index lay).1 j =
          treeValue (WCT9.wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay j = 0))
    (hchains : ∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalue w lay i = WCT9.wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (low (answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay)))))) = some digits :=
    hframe.2
  have hfit' : Extract.msgFits (routeLeaf index lay).lay msg := hfit
  have hencE : (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay),
      answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay))))) ∈
        entriesOf answers qs :=
    mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  · have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · by_cases hp : lay.val < 3 → wbcPad w lay = 0
      · exact Or.inr ⟨hm, ⟨digits, hm ▸ hframe, hshape⟩, hp⟩
      · have hlay : lay.val < 3 := by by_contra h3; exact hp (fun h => absurd h h3)
        have hpad : wbcPad w lay ≠ 0 := fun h0 => hp (fun _ => h0)
        obtain ⟨l, r, hlr⟩ : ∃ l r, msg = .pair l r := by
          cases msg with
          | forest root => exact absurd hfit (by change ¬(lay.val = 3); omega)
          | pair l r => exact ⟨l, r, rfl⟩
        subst hlr
        refine Or.inl (Or.inl ⟨lay, _, wbcCtr w lay, wbcPad w lay, _, hfit', hencE, ?_, ?_⟩)
        · exact referenceInput_ne_pad answers _ l r _ _ hfit' hpad
        · rw [← heq]; exact hdec
    · refine Or.inl (Or.inl ⟨lay, msg, wbcCtr w lay, wbcPad w lay, _, hfit', hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inl (by rw [leafMsg_route _ _ _ hidx]; exact hm))
      · rw [← heq]; exact hdec
  · have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wbcCtr w lay, wbcPad w lay, _, digits, hfit', hencE,
        referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact ((hchains i.val i.isLt).2 hlt).2 h2
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)
theorem layer_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots_route answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun _ => (hmerkle j hj).2⟩)
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layerPair_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay : lay.val ≠ 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerPairP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerPairP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots_route answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun h => (hmerkle j hj).2 (h.resolve_right hlay)⟩)
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layersBC_wots_walk_route (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, Extract.msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (Extract.honestRoot answers 0 0) →
    WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index n msg))) ∨
    ((∀ l : Layer, l.val < n → BC.GoodZ answers w index l) ∧
      msg = Extract.honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := Extract.layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := Extract.ofNat_val n (by omega)
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          (msg = Extract.honestMsg answers index (Fin.ofNat 4 n) ∧ BC.GoodZ answers w index (Fin.ofNat 4 n)) →
          (∀ l : Layer, l.val < n → BC.GoodZ answers w index l) →
          WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersBC w index (n + 1) msg))) ∨
          ((∀ l : Layer, l.val < n + 1 → BC.GoodZ answers w index l) ∧
            msg = Extract.honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          refine ⟨fun l hl => ?_, hmsg⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            Extract.honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        exact finish (layer_wots_route answers w index (Fin.ofNat 4 0) msg digits hidx hfit hframe _ henc hq hroot)
          (fun l hl => absurd hl (by omega))
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : Extract.msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := by
          show (Fin.ofNat 4 (n - 1) : Layer).val < 3
          rw [Extract.ofNat_val _ (by omega)]; omega
        rcases layersBC_wots_walk_route answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hprim | ⟨hgood, hmsg⟩
        · exact Or.inl (hprim.mono (entriesOf_mono hqR))
        · rw [Extract.honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          exact finish (layerPair_wots_route answers w index (Fin.ofNat 4 n) msg digits hidx
            (by rw [hval]; exact hn0) hfit hframe _ henc hqP hpair) hgood
theorem verifyP_walk_wots_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
            Extract.honestForest answers (N.toNat % 2 ^ 31) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rcases layersBC_wots_walk_route answers w (N.toNat % 2 ^ 31) hidx 4 (by decide) le_rfl (.forest _)
      (show (Fin.ofNat 4 (4 - 1) : Layer).val = 3 from rfl) (by rw [hlay, hpk]) with
    hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [show (4 - 1 : Nat) = 3 from rfl, Extract.honestMsg_three] at hroot
    simpa using hroot
theorem verifyP_wots_cases_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, BC.GoodZ answers w (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N w ∧
         ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots_route answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape, hqV⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactChain : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem known_secret {D : Coord → Prop} {s : CanonGraph.SecretIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem known_chain_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ p : ChainGraph.Point, c = .inl (.chain p) →
      (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl (CanonGraph.seedIdx p.1))) := by
  induction h with
  | base hc =>
      intro p hp
      subst hp
      exact Or.inl ⟨p.2, le_rfl, hc⟩
  | @node N hall ih =>
      intro p hp
      simp only [Sum.inl.injEq] at hp
      subst hp
      have hmem : (chainChild p, 3) ∈ childSlots (.chain p) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      unfold chainChild at hk hih
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0] at hk
        exact Or.inr (known_secret hk)
      · rw [if_neg h0] at hih
        rcases hih (ChainGraph.predecessor p) rfl with ⟨s, hs, hd⟩ | hd
        · refine Or.inl ⟨s, ?_, hd⟩
          simp only [ChainGraph.predecessor] at hs
          omega
        · exact Or.inr hd
theorem known_chain {D : Coord → Prop} {p : ChainGraph.Point} (h : Known D (.inl (.chain p))) :
    (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl (CanonGraph.seedIdx p.1))) :=
  known_chain_aux h p rfl
theorem wctItem_zero (a : CanonGraph.WctAddr) : wctItem a 0 = .inr (.inr a) := rfl
theorem wctItem_succ (a : CanonGraph.WctAddr) (s : Fin 3) :
    wctItem a (s.val + 1) = .inl (.wctChain (a, s)) := by
  have h : (⟨(s.val + 1 - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = s :=
    Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt s.isLt)
  unfold wctItem
  rw [if_neg (Nat.succ_ne_zero _), h]
theorem wctItem_pos (a : CanonGraph.WctAddr) (p : Nat) (h0 : p ≠ 0) (hp : p ≤ 3) :
    wctItem a p = .inl (.wctChain (a, ⟨p - 1, by omega⟩)) := by
  have h : (⟨(p - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = ⟨p - 1, by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  unfold wctItem
  rw [if_neg h0, h]
theorem known_wct_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ (a : CanonGraph.WctAddr) (s : Fin 3), c = .inl (.wctChain (a, s)) →
      ∃ p' ≤ s.val + 1, D (wctItem a p') := by
  induction h with
  | base hc =>
      intro a s hs
      subst hs
      exact ⟨s.val + 1, le_rfl, by rw [wctItem_succ]; exact hc⟩
  | @node N hall ih =>
      intro a s hN
      simp only [Sum.inl.injEq] at hN
      subst hN
      have hmem : (wctItem a s.val, 3) ∈ childSlots (.wctChain (a, s)) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      by_cases h0 : s.val = 0
      · rw [h0, wctItem_zero] at hk
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [wctItem_zero]
        exact known_secret hk
      · have hs1 : s.val - 1 < 3 := by omega
        have he := wctItem_pos a s.val h0 (by omega)
        obtain ⟨p', hp', hd⟩ := hih a ⟨s.val - 1, hs1⟩ he
        exact ⟨p', by simp only at hp'; omega, hd⟩
theorem known_wctItem {D : Coord → Prop} {a : CanonGraph.WctAddr} {p : Nat} (hp : p ≤ 3)
    (h : Known D (wctItem a p)) : ∃ p' ≤ p, D (wctItem a p') := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero] at h
    exact ⟨0, le_rfl, by rw [wctItem_zero]; exact known_secret h⟩
  · have hs : p - 1 < 3 := by omega
    have he := wctItem_pos a p h0 hp
    rw [he] at h
    obtain ⟨p', hp', hd⟩ := known_wct_aux h a ⟨p - 1, hs⟩ rfl
    exact ⟨p', by simp only at hp'; omega, hd⟩
theorem wctItem_injective {a b : CanonGraph.WctAddr} {p q : Nat} (hp : p ≤ 3) (hq : q ≤ 3)
    (h : wctItem a p = wctItem b q) : a = b ∧ p = q := by
  unfold wctItem at h
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0
  · rw [if_pos hp0, if_pos hq0] at h
    simp only [Sum.inr.injEq] at h
    exact ⟨h, by omega⟩
  · rw [if_pos hp0, if_neg hq0] at h; cases h
  · rw [if_neg hp0, if_pos hq0] at h; cases h
  · rw [if_neg hp0, if_neg hq0] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.wctChain.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := congrArg Fin.val h2
    simp only at h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact ⟨h1, by omega⟩
theorem chainItem_chain {L : CanonGraph.LeafPos} {i d : Nat} {p : ChainGraph.Point}
    (h : chainItem L i d = .inl (.chain p)) :
    p.1 = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d ≠ 0 ∧ p.2.val = (d - 1) % 7 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    cases h
  · rw [if_neg hd] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.chain.injEq] at h
    subst h
    exact ⟨rfl, hd, rfl⟩
theorem chainItem_seed {L : CanonGraph.LeafPos} {i d : Nat} {a : ChainGraph.Address}
    (h : chainItem L i d = .inr (.inl a)) :
    a = CanonGraph.seedIdx ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d = 0 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h.symm, hd⟩
  · rw [if_neg hd] at h
    cases h
def NotChain (c : Coord) : Prop := (∀ p, c ≠ .inl (.chain p)) ∧ (∀ a, c ≠ .inr (.inl a))
theorem treeChild_not_chain {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) : NotChain d := by
  unfold treeChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 4096
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsChild_not_chain {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) : NotChain d := by
  unfold ftsChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem wctItem_not_chain (a : CanonGraph.WctAddr) (p : Nat) : NotChain (wctItem a p) := by
  unfold wctItem
  split_ifs
  · exact ⟨fun p => by simp, fun a => by simp⟩
  · exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsItems_not_chain (index : Fin (2^31)) (N : HashOutput) (c : Coord)
    (hc : c ∈ ftsItems index N) : NotChain c := by
  unfold ftsItems wctOpened wctPath at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
    List.mem_filterMap, List.mem_range] at hc
  obtain ⟨k, hc | ⟨l, _, hl⟩⟩ := hc
  · obtain ⟨t, rfl⟩ := hc
    exact wctItem_not_chain _ _
  · exact ftsChild_not_chain hl
theorem keygen_not_chain (c : Coord) (hc : c ∈ keygenDisclosed) : NotChain c := by
  unfold keygenDisclosed at hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨_, _, _, _, h⟩ := hc
  exact treeChild_not_chain h
theorem layerItems_chain (A : Answers) (index : Fin (2^31)) (c : Coord)
    (hc : c ∈ layerItems (Wots.referenceDigits A) index) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      have hfin : (CanonGraph.fin58 i).val = i := Nat.mod_eq_of_lt hi58
      have hdepth : ∀ a : ChainGraph.Address,
          a = ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ →
          Wots.depth A (wotsAddr a) = (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 := by
        intro a ha
        subst ha
        simp only [Wots.depth, wotsAddr, hfin, routeAddr]
      constructor
      · intro p hp
        obtain ⟨h1, hd, h2⟩ := chainItem_chain hp
        rw [hdepth p.1 h1, h2]
        have hle : (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
          WotsExtract.depth_le A ⟨routeAddr index.val lay, i⟩ hi
        have hw : maxDigit lay i ≤ 7 := by
          unfold maxDigit; split_ifs <;> norm_num
        omega
      · intro a ha
        obtain ⟨h1, hd⟩ := chainItem_seed ha
        have hin : CanonGraph.seedIdx (⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩,
            CanonGraph.fin58 i⟩ : ChainGraph.Address) =
            ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ := by
          unfold CanonGraph.seedIdx
          rw [dif_neg]
          rintro ⟨-, h, -⟩
          change chainCount lay ≤ (CanonGraph.fin58 i).val at h
          omega
        rw [hin] at h1
        rw [hdepth a h1, hd]
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      have := treeChild_not_chain hj
      exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
    · cases hc
theorem signDisclosed_chain (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (c : Coord) (hc : c ∈ signDisclosed A published request) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold signDisclosed at hc
  split_ifs at hc with hcache
  · split at hc
    · split_ifs at hc with hok
      · unfold signItems signItemsWith at hc
        rcases List.mem_append.mp hc with hc | hc
        · have := ftsItems_not_chain _ _ c hc
          exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
        · exact layerItems_chain A _ c hc
      · cases hc
    · cases hc
  · cases hc
def Disclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
theorem seedIdx_of_depth (A : Answers) (a : ChainGraph.Address) (hd : 1 ≤ Wots.depth A (wotsAddr a)) :
    CanonGraph.seedIdx a = a := by
  have hc := Wots.Mask.chain_lt_of_depth A (wotsAddr a) hd
  unfold CanonGraph.seedIdx
  rw [dif_neg]
  rintro ⟨-, h, -⟩
  exact absurd hc (by change ¬(a.chain.val < chainCount a.layer); omega)
theorem frontier_child_unknown (A : Answers) (published : SigGolfCandidate.T3.Cache) (a : ChainGraph.Address)
    (s : Fin 7) (hs : s.val + 1 = Wots.depth A (wotsAddr a)) :
    ¬Known (Disclosed A published) (chainChild (a, s)) := by
  intro hk
  unfold chainChild at hk
  by_cases h0 : s.val = 0
  · rw [if_pos h0, seedIdx_of_depth A a (by omega)] at hk
    rcases known_secret hk with hd | ⟨request, hd⟩
    · exact (keygen_not_chain _ hd).2 a rfl
    · have := (signDisclosed_chain A published request _ hd).2 a rfl
      omega
  · rw [if_neg h0] at hk
    rcases known_chain hk with ⟨t, ht, hd⟩ | hd
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).1 _ rfl
      · have := (signDisclosed_chain A published request _ hd).1 _ rfl
        simp only [ChainGraph.predecessor] at ht this
        omega
    · simp only [ChainGraph.predecessor] at hd
      rw [seedIdx_of_depth A a (by omega)] at hd
      rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).2 _ rfl
      · have := (signDisclosed_chain A published request _ hd).2 _ rfl
        omega
theorem treeChild_ne_wctItem {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold treeChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 4096
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem ftsChild_ne_wctItem {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold ftsChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem keygen_not_wct (a : CanonGraph.WctAddr) (p : Nat) : wctItem a p ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨_, _, _, _, h⟩ := hc
  exact treeChild_ne_wctItem h a p rfl
theorem layerItems_not_wct (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (a : CanonGraph.WctAddr)
    (p : Nat) : wctItem a p ∉ layerItems digitsOf index := by
  intro hc
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, -, hi⟩ := hc
      unfold chainItem wctItem at hi
      split_ifs at hi <;> simp at hi
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact treeChild_ne_wctItem hj a p rfl
    · cases hc
theorem wctItem_mem_signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) (a : CanonGraph.WctAddr)
    (p : Nat) (hp : p ≤ 3) (h : wctItem a p ∈ signItemsWith digitsOf N) :
    a.1 = digestIndex N ∧ a.2.2.1 = WCT9.child N a.2.1 ∧ p = 3 - WCT9.wordDigit (WCT9.rank N a.2.1) a.2.2.2 := by
  unfold signItemsWith at h
  rcases List.mem_append.mp h with h | h
  · unfold ftsItems wctOpened wctPath at h
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
      List.mem_filterMap, List.mem_range] at h
    obtain ⟨k, ⟨t, ht⟩ | ⟨l, _, hl⟩⟩ := h
    · have hle : 3 - WCT9.wordDigit (WCT9.rank N k) t ≤ 3 := Nat.sub_le _ _
      obtain ⟨hab, hpq⟩ := wctItem_injective hle hp ht
      subst hab
      exact ⟨rfl, rfl, hpq.symm⟩
    · exact (ftsChild_ne_wctItem hl a p rfl).elim
  · exact (layerItems_not_wct digitsOf _ a p h).elim
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr gAddr wotsAddr_gAddr chainCount_le58 chainRow_block4
  slotValue_chainRow slotValue_block4_three honestChainValue_zero')
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → Clear A K X (A (.inl (.inr X)))
theorem posOf_chainRow (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (s : Nat) (hs : s < 7) (v : Digest) :
    Extract.posOf (Wots.chainRow a s v) = some (CanonGraph.Node.chain (gAddr a ha, ⟨s, hs⟩)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  unfold Wots.chainRow
  rw [Extract.hdrBlock_wotsChainInput]
  rfl
theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRow (wotsAddr p.1) p.2.val (honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [chainInput_padded]
  rfl
theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    honestValue A (.inl (.chain p)) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  rw [← honestChainValue_succ, eval_shortHash]
  rfl
theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    honestValue A (chainChild p) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (WCT9.wotsSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, honestChainValue_zero']
    exact CanonGraph.seedsOf_secretsOf A p.1
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega
theorem childSlots_chain (p : ChainGraph.Point) : childSlots (.chain p) = [(chainChild p, 3)] := rfl
theorem contactAt_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (hc : Wots.ContactAt A (Wots.entriesOf A qs) a)
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  obtain ⟨hd, value, answer, hmem, hlow⟩ := hc
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hd7 : Wots.depth A a ≤ 7 := by
    have := WotsExtract.depth_le A a ha.2
    have hw : maxDigit a.key.lay a.chain ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  set s := Wots.depth A a - 1 with hsdef
  have hs7 : s < 7 := by omega
  let p : ChainGraph.Point := (gAddr a ha, ⟨s, hs7⟩)
  have hpos := posOf_chainRow a ha s hs7 value
  obtain ⟨hhit, hsingle, -⟩ := hclear _ hq
  have hcv : honestValue A (chainChild p) = honestChainValue A a.key.lay a.key.tree a.key.leaf a.chain
      (WCT9.wotsSeed A a.key.lay a.key.tree a.key.leaf a.chain) s := honestValue_chainChild A p
  by_cases hv : value = honestValue A (chainChild p)
  · have hk := hsingle (.chain p) hpos (chainChild p) 3 (childSlots_chain p) (by rw [slotValue_chainRow]; exact hv)
    exact frontier_child_unknown A published (gAddr a ha) ⟨s, hs7⟩ (by
      change s + 1 = Wots.depth A (wotsAddr (gAddr a ha))
      rw [wotsAddr_gAddr]; omega) hk
  · apply hhit (.chain p) hpos
    refine ⟨fun heq => hv ?_, ?_⟩
    · have := congrArg (fun X => slotValue X 3) heq
      simp only [slotValue_chainRow] at this
      rw [this, honestInput_chainNode, slotValue_chainRow, hcv]
      rfl
    · rw [hans]
      change Wots.low answer = _
      rw [hlow, honestValue_chainNode]
      unfold Wots.frontierValue
      congr 1
      change Wots.depth A a = s + 1
      omega
theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : WotsExtract.StructuralHitSrc A (Wots.entriesOf A qs)) (hclear : AllClear A K qs) : False := by
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, -, hne, hlow⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hsp : CanonGraph.SourcePos position := by
    cases position with
    | chain lay tree leaf i step =>
        obtain ⟨h1, h2, h3, h4⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 (chainCount_le58 lay), ?_⟩
        · calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
            _ = 4096 := by norm_num
        · have hw : 2 ^ width lay i ≤ 8 := by unfold width; split_ifs <;> norm_num
          omega
    | leaf lay tree leaf =>
        obtain ⟨h1, h2⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
          _ = 4096 := by norm_num
    | node lay tree level nd => exact hsrc
    | forest index => exact hsrc
    | wctChain index coord child t step => exact hsrc
    | wctLeaf index coord child => exact hsrc
    | wctNode index coord level nd => exact hsrc
  obtain ⟨N, rfl⟩ := CanonGraph.exists_toPos hsp
  exact (hclear _ hq).1 N hpos ⟨hne, hlow⟩
theorem encodingMatch_route_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (lay : Layer)
    (h : Wots.EncodingMatchAt A (Wots.entriesOf A qs) (WotsExtract.routeLeaf index lay))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m, ctr, pad, answer, hfit, hmem, hne, hdec⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  obtain ⟨L, hL⟩ := CanonEncoding.route_source index hidx lay
  have hL' : L.toWots = WotsExtract.routeLeaf index lay := hL
  have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL'
  refine (hclear _ hq).2.2 L m ctr pad (by rw [hlay]; exact hfit) (by rw [hL']) ⟨?_, ?_⟩
  · rw [hL']; exact hne
  · rw [hans, hL', hlay]; exact hdec
theorem wotsPrimitiveRoute_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (index : Nat) (hidx : index < 2 ^ 31) (h : WotsExtract.WotsPrimitiveRoute index A (Wots.entriesOf A qs))
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, -, -, h, -⟩ | ⟨a, ha, -, h⟩
  · exact encodingMatch_route_false A _ qs index hidx lay h hclear
  · exact structuralHitSrc_false A _ qs h hclear
  · obtain ⟨hd, start, middle, -, hrow⟩ := h
    exact contactAt_false A published qs a ha ⟨by omega, middle, hrow⟩ hclear
  · exact contactAt_false A published qs a ha h hclear
  · exact contactAt_false A published qs a ha h hclear
theorem posOf_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 3) :
    Extract.posOf (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) =
      some (CanonGraph.Node.wctChain (a, s)).toPos :=
  Extract.posOf_eq (CanonGraph.toPos_bounded _) (Extract.hdrBlock_honestInput A _)
theorem honestValue_wctItem (A : Answers) (a : CanonGraph.WctAddr) (p : Nat) (hp : p ≤ 3) :
    honestValue A (wctItem a p) = Extract.wctValue A a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero]
    change CanonGraph.secretsOf A (.inr a) = _
    rw [← CanonGraph.wctSeed_secrets]
    simp [Extract.wctValue, WCT9.chain]
  · rw [wctItem_pos a p h0 hp]
    obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
    change (A (.inl (.inr (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val
      (s + 1 - 1)))))).extractLsb' 0 128 = _
    rw [← WctExtract.wctValue_succ, eval_shortHash, Extract.pad64_wctChainInput, WctExtract.honestInput_wctChain]
    rfl
theorem slotValue_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 3) :
    slotValue (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) 3 = honestValue A (wctItem a s.val) := by
  rw [honestValue_wctItem A a s.val (by omega)]
  change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 3 = _
  rw [WctExtract.honestInput_wctChain, WctExtract.wctChainInput_block4']
  exact slotValue_block4_three _ _ _ _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_inputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem trace_inputs (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support) :
    ∀ e ∈ (QueryRecorded.recordedTrace result).events, ∀ x, e.input = .inl (.inr x) →
      x ∈ Wots.referenceInputs adversary :=
  record_inputs _ _ (∅, ∅) (Wots.Ref.referenceInputs_inputsIn adversary) _
    (PaddedExtraction.traced_record_support adversary q hq result hr)
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem noContact_caseC (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) (hcomp : BPB.SignerComplete z.2) :
    BPB.CaseCFresh adversary z := by
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).contact = false := by
    simpa using hmon
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have hpk : g.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  obtain ⟨hlen, forgery, hf, hfresh, m, w, hof, hv, hsub⟩ :=
    WotsExtract.verdict_accepting g.value.1 t.value t.state c hc z.2 hac hcval
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_route z.2 m g.value.1 w hpk hv
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    have hseen := events_seen (Wots.referenceInputs adversary) z.2 q c.events _ hmon' _ hev X rfl
    have hXU : X ∈ Wots.referenceInputs adversary := by
      have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
      have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
      rw [← hev'] at hmem
      exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
    have hcl := monitorRun_clear (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events hsteps hverdict
      hmon' hcalls X hseen hXU
    exact hcl.mono fun d hd => monitorRun_known (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, -⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgood, hfts, hcomp⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  by_cases hsd : BPB.SignedDigest t.value.2 m w
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩).elim
  · exact ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩
theorem wct_noContact_caseC (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) (hcomp : BPB.SignerComplete z.2) :
    BPB.CaseCFresh adversary z :=
  noContact_caseC adversary q hq z hz hwin hno hcomp
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
end

section






section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertFold : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CoverOk (st : RouterState) : Prop :=
  ∀ m c N, st.memo.lookup m = some (some (c, N)) → N ∈ st.exposures ∨ st.reused = true
def signCount : List TaggedStep → Nat
  | [] => 0
  | .world _ :: rest => signCount rest
  | .sign _ _ _ :: rest => signCount rest + 1
def stepLog : List TaggedStep → QueryLog Requests
  | [] => []
  | .world _ :: rest => stepLog rest
  | .sign request output _ :: rest => ⟨request, output⟩ :: stepLog rest
theorem signCount_eq_length (steps : List TaggedStep) : signCount steps = (stepLog steps).length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [signCount, stepLog, ih]
theorem taggedRecord_log {α : Type} (program : OracleComp LazyPrivate.Interaction α) (published : SigGolfCandidate.T3.Cache)
    (state : LazyPrivate.State) (t : Tagged α) (ht : t ∈ support (taggedRecord published program state)) :
    t.value.2 = stepLog t.steps := by
  induction program using OracleComp.inductionOn generalizing state t with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at ht
      subst ht
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at ht
          obtain ⟨middle, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          exact ih middle.1 middle.2 last hl
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at ht
          obtain ⟨block, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          change ⟨request, block.value⟩ :: last.value.2 = ⟨request, block.value⟩ :: stepLog last.steps
          rw [ih block.value block.state last hl]
theorem sign_mem_stepLog {steps : List TaggedStep} {request : Security.Request} {output : Option Signature}
    {events : List FirstHit.QueryEvent} (h : TaggedStep.sign request output events ∈ steps) :
    (⟨request, output⟩ : (r : Requests.Domain) × Requests.Range r) ∈ stepLog steps := by
  induction steps with
  | nil => cases h
  | cons s rest ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · cases s with
        | world e => exact ih h'
        | sign r o ev => exact List.mem_cons_of_mem _ (ih h')
section Fold
variable (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
theorem routerEvent_fields (st : RouterState) (e : FirstHit.QueryEvent) :
    (routerEvent U st e).exposures = st.exposures ∧ (routerEvent U st e).reused = st.reused ∧
      (routerEvent U st e).memo = st.memo ∧ (routerEvent U st e).trials = st.trials := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · change (st.next U X y).exposures = _ ∧ (st.next U X y).reused = _ ∧ (st.next U X y).memo = _ ∧
      (st.next U X y).trials = _
    unfold RouterState.next
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
theorem routerEvents_fields (events : List FirstHit.QueryEvent) (st : RouterState) :
    (events.foldl (routerEvent U) st).exposures = st.exposures ∧ (events.foldl (routerEvent U) st).reused = st.reused ∧
      (events.foldl (routerEvent U) st).memo = st.memo ∧ (events.foldl (routerEvent U) st).trials = st.trials := by
  induction events generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := ih (routerEvent U st e)
      obtain ⟨g1, g2, g3, g4⟩ := routerEvent_fields U st e
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
theorem finishState_bank (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState A st1 found).exposures = st1.exposures ∧ (finishState A st1 found).reused = st1.reused ∧
      (finishState A st1 found).memo = st1.memo ∧ (finishState A st1 found).trials = st1.trials := by
  unfold finishState
  cases found with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem signedState_bank (nv : Message → Digest) (st : RouterState) (request : Security.Request) :
    (request.cache = published →
      (signedState A nv published st request).exposures = (startState A nv st request.message).exposures ∧
      (signedState A nv published st request).reused = (startState A nv st request.message).reused ∧
      (signedState A nv published st request).memo = (startState A nv st request.message).memo ∧
      (signedState A nv published st request).trials = (startState A nv st request.message).trials) ∧
    (request.cache ≠ published → signedState A nv published st request = st) := by
  rw [signedState_eq]
  constructor
  · intro hc
    rw [if_pos hc]
    exact finishState_bank A _ _
  · intro hc
    rw [if_neg hc]
theorem signed_memo_lookup (st : RouterState) (rho : Digest) (m m' : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).memo.lookup m' = if m' = m then some found else st.memo.lookup m' := by
  rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons]
  by_cases h : m' = m
  · subst h; simp
  · have hne : (m' == m) = false := by simpa using h
    rw [hne, if_neg h]
theorem signed_exposures_reused (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (∀ N, N ∈ st.exposures → N ∈ (st.signed rho m found).exposures) ∧
      (st.reused = true → (st.signed rho m found).reused = true) ∧
      (∀ c N, found = some (c, N) → N ∈ (st.signed rho m found).exposures ∨ (st.signed rho m found).reused = true) := by
  unfold RouterState.signed
  split_ifs
  · exact ⟨fun N h => h, fun _ => rfl, fun _ _ _ => Or.inr rfl⟩
  · refine ⟨fun N h => List.mem_append_left _ h, fun h => h, fun c N hf => Or.inl ?_⟩
    subst hf
    simp
theorem coverOk_startState (nv : Message → Digest) (st : RouterState) (m : Message) (h : CoverOk st)
    (hmemo : MemoOk A st) : CoverOk (startState A nv st m) ∧ MemoOk A (startState A nv st m) := by
  unfold startState
  split_ifs with hs
  · exact ⟨h, hmemo⟩
  · obtain ⟨hx, hr, hnew⟩ := signed_exposures_reused st (nv m) m (LargeResidual.signDigest A m)
    constructor
    · intro m' c N hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · exact hnew c N (Option.some.inj hl)
      · rcases h m' c N hl with h1 | h1
        · exact Or.inl (hx N h1)
        · exact Or.inr (hr h1)
    · intro m' f hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · subst hm; exact (Option.some.inj hl).symm
      · exact hmemo m' f hl
theorem coverOk_signedState (st : RouterState) (request : Security.Request) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (signedState A (honestNonce A) published st request) := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · obtain ⟨h1, h2, h3, -⟩ := hpub hc
    intro m c N hl
    rw [h1, h2]
    rw [h3] at hl
    exact (coverOk_startState A (honestNonce A) st request.message h hmemo).1 m c N hl
  · rw [hnpub hc]; exact h
theorem coverOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : CoverOk st) : CoverOk (routerEvent U st e) := by
  obtain ⟨h1, h2, h3, -⟩ := routerEvent_fields U st e
  intro m c N hl
  rw [h1, h2]
  rw [h3] at hl
  exact h m c N hl
theorem memoOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : MemoOk A st) : MemoOk A (routerEvent U st e) := by
  intro m f hl
  rw [(routerEvent_fields U st e).2.2.1] at hl
  exact h m f hl
theorem invariants_steps (steps : List TaggedStep) (st : RouterState) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (steps.foldl (routerStep U A (honestNonce A) published) st) ∧
      MemoOk A (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact coverOk_event U st e h
        | sign request out evs => exact coverOk_signedState A published st request h hmemo
      · cases s with
        | world e => exact memoOk_event U A st e hmemo
        | sign request out evs => exact signedState_memo A (honestNonce A) published st request hmemo
theorem invariants_events (events : List FirstHit.QueryEvent) (st : RouterState) (h : CoverOk st)
    (hmemo : MemoOk A st) :
    CoverOk (events.foldl (routerEvent U) st) ∧ MemoOk A (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      exact ih _ (coverOk_event U st e h) (memoOk_event U A st e hmemo)
theorem memo_isSome_event (st : RouterState) (e : FirstHit.QueryEvent) (m : Message)
    (h : (st.memo.lookup m).isSome) : ((routerEvent U st e).memo.lookup m).isSome := by
  rw [(routerEvent_fields U st e).2.2.1]; exact h
theorem memo_isSome_sign (st : RouterState) (request : Security.Request) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((signedState A (honestNonce A) published st request).memo.lookup m).isSome := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.1]
    unfold startState
    split_ifs with hs
    · exact h
    · rw [signed_memo_lookup]
      split_ifs <;> simp_all
  · rw [hnpub hc]; exact h
theorem memo_isSome_signed_self (st : RouterState) (request : Security.Request) (hc : request.cache = published) :
    ((signedState A (honestNonce A) published st request).memo.lookup request.message).isSome := by
  rw [((signedState_bank A published (honestNonce A) st request).1 hc).2.2.1]
  unfold startState
  split_ifs with hs
  · exact hs
  · rw [signed_memo_lookup, if_pos rfl]; rfl
theorem memo_isSome_steps (steps : List TaggedStep) (st : RouterState) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup m).isSome := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact memo_isSome_event U st e m h
      | sign request out evs => exact memo_isSome_sign A published st request m h
theorem sign_memo_steps (steps : List TaggedStep) (st : RouterState) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup request.message).isSome := by
  induction steps generalizing st with
  | nil => cases hmem
  | cons s rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact memo_isSome_steps U A published rest _ _ (memo_isSome_signed_self A published st request hc)
      · exact ih _ hmem
theorem covered_fold (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) (c : BitVec 32) (N : HashOutput)
    (hN : LargeResidual.signDigest A request.message = some (c, N)) :
    N ∈ (routerFold U A published steps verdict).exposures ∨ (routerFold U A published steps verdict).reused = true := by
  unfold routerFold
  have hinv0 : CoverOk RouterState.initial ∧ MemoOk A RouterState.initial :=
    ⟨fun m c N h => by simp [RouterState.initial] at h, fun m f h => by simp [RouterState.initial] at h⟩
  obtain ⟨h1, h2⟩ := invariants_steps U A published steps _ hinv0.1 hinv0.2
  obtain ⟨h3, h4⟩ := invariants_events U A verdict _ h1 h2
  have hs := sign_memo_steps U A published steps RouterState.initial request out evs hmem hc
  have hs' : ((verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published)
      RouterState.initial)).memo.lookup request.message).isSome := by
    rw [(routerEvents_fields U verdict _).2.2.1]; exact hs
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs'
  have hfe := h4 _ _ hf
  rw [hN] at hfe
  subst hfe
  exact h3 _ c N hf
theorem exposures_signedState_le (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).exposures.length ≤ st.exposures.length + 1 := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).1]
    unfold startState
    split_ifs
    · omega
    · unfold RouterState.signed
      split_ifs
      · dsimp only; omega
      · dsimp only
        rw [List.length_append]
        have : ((LargeResidual.signDigest A request.message).map Prod.snd).toList.length ≤ 1 := by
          cases LargeResidual.signDigest A request.message <;> simp
        omega
  · rw [hnpub hc]; omega
theorem exposures_steps_le (steps : List TaggedStep) (st : RouterState) :
    (steps.foldl (routerStep U A (honestNonce A) published) st).exposures.length ≤
      st.exposures.length + signCount steps := by
  induction steps generalizing st with
  | nil => simp [signCount]
  | cons s rest ih =>
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      cases s with
      | world e =>
          change (routerEvent U st e).exposures.length + signCount rest ≤ st.exposures.length + signCount rest
          rw [(routerEvent_fields U st e).1]
      | sign request out evs =>
          have := exposures_signedState_le A published st request
          change (signedState A (honestNonce A) published st request).exposures.length + signCount rest ≤
            st.exposures.length + (signCount rest + 1)
          omega
theorem exposures_fold_le (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) :
    (routerFold U A published steps verdict).exposures.length ≤ signCount steps := by
  unfold routerFold
  rw [(routerEvents_fields U verdict _).1]
  have := exposures_steps_le U A published steps RouterState.initial
  simpa [RouterState.initial] using this
theorem trials_steps (steps : List TaggedStep) (st : RouterState) (X : HashInput)
    (hX : X ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials) :
    X ∈ st.trials ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧ request.cache = published ∧
      X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message) := by
  induction steps generalizing st with
  | nil => exact Or.inl hX
  | cons s rest ih =>
      rw [List.foldl_cons] at hX
      rcases ih _ hX with h | ⟨r, o, e, hm, hc, hr⟩
      · cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials at h
            rw [(routerEvent_fields U st e).2.2.2] at h
            exact Or.inl h
        | sign request out evs =>
            change X ∈ (signedState A (honestNonce A) published st request).trials at h
            obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
            by_cases hc : request.cache = published
            · rw [(hpub hc).2.2.2] at h
              unfold startState at h
              split_ifs at h
              · exact Or.inl h
              · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1, List.mem_append] at h
                rcases h with h | h
                · exact Or.inl h
                · exact Or.inr ⟨request, out, evs, List.mem_cons_self, hc, h⟩
            · rw [hnpub hc] at h; exact Or.inl h
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hc, hr⟩
theorem seen_event_mono' (st : RouterState) (e : FirstHit.QueryEvent) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (routerEvent U st e).seen := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact h
  · change Y ∈ (st.next U X y).seen
    unfold RouterState.next
    split_ifs <;> exact List.mem_cons_of_mem _ h
  · exact h
theorem seen_event_self (st : RouterState) (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) :
    X ∈ (routerEvent U st ⟨b, .inl (.inr X), y⟩).seen := by
  change X ∈ (st.next U X y).seen
  unfold RouterState.next
  split_ifs <;> exact List.mem_cons_self
theorem seen_events_mono' (events : List FirstHit.QueryEvent) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih => exact ih _ (seen_event_mono' U st e Y h)
theorem seen_signed (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).seen = st.seen ∧
      (signedState A (honestNonce A) published st request).births = st.births := by
  refine ⟨(signedState_seen A (honestNonce A) published st request).1, ?_⟩
  rw [signedState_eq]
  split_ifs
  · rw [(finishState_fields _ _ _).2.2.2.1, (startState_fields _ _ _ _).2.2.2]
  · rfl
theorem seen_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).seen := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact seen_event_mono' U st e Y h
      | sign request out evs =>
          change Y ∈ (signedState A (honestNonce A) published st request).seen
          rw [(seen_signed A published st request).1]; exact h
def BirthInv (X : HashInput) (N : HashOutput) (st : RouterState) : Prop := X ∈ st.seen → (X, N) ∈ st.births
theorem birthInv_event (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (st : RouterState) (e : FirstHit.QueryEvent) (hans : ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (htr : X ∉ st.trials) (h : BirthInv X N st) : BirthInv X N (routerEvent U st e) := by
  rcases e with ⟨b, (n | Y) | c, y⟩
  · exact h
  · change X ∈ (st.next U Y y).seen → (X, N) ∈ (st.next U Y y).births
    intro hs
    unfold RouterState.next at hs ⊢
    by_cases hY : Y = X
    · subst hY
      have hy : y = N := hans b y rfl
      subst hy
      by_cases hf : st.Fresh Y
      · rw [if_pos ⟨hXU, hXd, hf⟩]
        exact List.mem_cons_self
      · have hfr : ¬(Y ∈ U ∧ IsDigestRow Y ∧ st.Fresh Y) := fun h' => hf h'.2.2
        rw [if_neg hfr]
        have hseen : Y ∈ st.seen := by
          by_contra hn
          exact hf ⟨hn, htr⟩
        exact h hseen
    · have hs' : X ∈ st.seen := by
        split_ifs at hs <;>
        · rcases List.mem_cons.mp hs with h1 | h1
          · exact absurd h1.symm hY
          · exact h1
      split_ifs
      · exact List.mem_cons_of_mem _ (h hs')
      · exact h hs'
  · exact h
theorem birthInv_events (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (events : List FirstHit.QueryEvent) (hans : ∀ e ∈ events, ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ st.trials) (h : BirthInv X N st) :
    BirthInv X N (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih =>
      rw [List.foldl_cons]
      apply ih (fun e' he' => hans e' (List.mem_cons_of_mem _ he'))
      · rw [(routerEvent_fields U st e).2.2.2]; exact htr
      · exact birthInv_event U X N hXU hXd st e (hans e List.mem_cons_self) htr h
theorem trials_sign_mono (st : RouterState) (request : Security.Request) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (signedState A (honestNonce A) published st request).trials := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.2]
    unfold startState
    split_ifs
    · exact h
    · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1]; exact List.mem_append_left _ h
  · rw [hnpub hc]; exact h
theorem trials_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e =>
          change Y ∈ (routerEvent U st e).trials
          rw [(routerEvent_fields U st e).2.2.2]; exact h
      | sign request out evs => exact trials_sign_mono A published st request Y h
theorem birthInv_steps (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (steps : List TaggedStep)
    (hans : ∀ s ∈ steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ (steps.foldl (routerStep U A (honestNonce A) published) st).trials)
    (h : BirthInv X N st) :
    BirthInv X N (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons] at htr ⊢
      have hrest := fun s' hs' => hans s' (List.mem_cons_of_mem _ hs')
      apply ih hrest _ htr
      have hst : X ∉ st.trials := fun hm => htr (trials_steps_mono U A published rest _ X (by
        cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials
            rw [(routerEvent_fields U st e).2.2.2]; exact hm
        | sign request out evs => exact trials_sign_mono A published st request X hm))
      cases s with
      | world e => exact birthInv_event U X N hXU hXd st e (hans _ List.mem_cons_self e rfl) hst h
      | sign request out evs =>
          change X ∈ (signedState A (honestNonce A) published st request).seen →
            (X, N) ∈ (signedState A (honestNonce A) published st request).births
          rw [(seen_signed A published st request).1, (seen_signed A published st request).2]
          exact h
end Fold
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCert : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem treeChild_inl {lay : Layer} {tree : Fin (2 ^ 31)} {level c : Nat} {x : Coord}
    (h : treeChild lay tree level c = some x) : ∃ n, x = .inl n := by
  unfold treeChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem ftsChild_inl {index : Fin (2 ^ 31)} {coord : Fin 9} {level c : Nat} {x : Coord}
    (h : ftsChild index coord level c = some x) : ∃ n, x = .inl n := by
  unfold ftsChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem not_inr_keygenDisclosed (s : CanonGraph.SecretIndex) : (.inr s : Coord) ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨_, _, _, _, hc⟩ := h
  obtain ⟨n, hn⟩ := treeChild_inl hc
  cases hn
theorem disclosed_steps_mem (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (mon : Monitor) (d : Coord)
    (hd : d ∈ (steps.foldl (Monitor.step U A q published) mon).disclosed) :
    d ∈ mon.disclosed ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧
      d ∈ signDisclosed A published request := by
  induction steps generalizing mon with
  | nil => exact Or.inl hd
  | cons s rest ih =>
      rw [List.foldl_cons] at hd
      rcases ih _ hd with h | ⟨r, o, e, hm, hr⟩
      · cases s with
        | world e =>
            change d ∈ (mon.event U A q e).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request out evs =>
            change d ∈ (mon.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, out, evs, List.mem_cons_self, h⟩
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hr⟩
theorem search_queried (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start k, start ≤ k → k < start + fuel →
      (∀ c', start ≤ c' → c' < k →
        WCT9.producerAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) →
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (WCT9.digestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start k h1 h2; omega
  | succ fuel ih =>
      intro start k h1 h2 hrej
      rw [BPB.digestSearch_succ, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest]
      by_cases hk : k = start
      · subst hk
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) k (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2')
theorem search_result (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start,
      (∀ c N, evalWithAnswerFn A (WCT9.digestSearch rho m start fuel) = some (c, N) →
        ∃ k, start ≤ k ∧ k < start + fuel ∧ c = BitVec.ofNat 32 k ∧ ∀ c', start ≤ c' → c' < k →
          WCT9.producerAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) ∧
      (evalWithAnswerFn A (WCT9.digestSearch rho m start fuel) = none → ∀ c', start ≤ c' → c' < start + fuel →
          WCT9.producerAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      refine ⟨fun c N h => ?_, fun _ c' h1 h2 => by omega⟩
      simp [WCT9.digestSearch] at h
  | succ fuel ih =>
      intro start
      rw [BPB.digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hadm : WCT9.producerAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure]
        refine ⟨fun c N h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨start, le_rfl, by omega, h.1.symm, fun c' h1 h2 => by omega⟩
      · rw [if_neg hadm]
        have hrej : WCT9.producerAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = false := by
          simpa using hadm
        obtain ⟨ih1, ih2⟩ := ih (start + 1)
        refine ⟨fun c N h => ?_, fun h c' h1 h2 => ?_⟩
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih1 c N h
          refine ⟨k, by omega, by omega, hk3, fun c' h1 h2 => ?_⟩
          by_cases hc : c' = start
          · subst hc; exact hrej
          · exact hk4 c' (by omega) h2
        · by_cases hc : c' = start
          · subst hc; exact hrej
          · exact ih2 h c' (by omega) (by omega)
theorem trialRows_queried (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (hc : request.cache = published) (X : HashInput)
    (hX : X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message)) :
    (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published request) := by
  set rho := honestNonce A request.message with hrho
  have hsd : LargeResidual.signDigest A request.message =
      evalWithAnswerFn A (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) := rfl
  have hq : (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈
      queried A (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) := by
    obtain ⟨r1, r2⟩ := search_result A rho request.message WCT9.digestAttemptLimit 0
    cases hfound : LargeResidual.signDigest A request.message with
    | none =>
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => r2 (hsd ▸ hfound) c' (Nat.zero_le _) (by omega))
    | some found =>
        obtain ⟨c, N⟩ := found
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        obtain ⟨k0, -, hk0, hck, hrej⟩ := r1 c N (hsd ▸ hfound)
        have hlim : WCT9.digestAttemptLimit = 2 ^ 21 := rfl
        have hct : c.toNat = k0 := by
          rw [hck, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        exact search_queried A rho request.message WCT9.digestAttemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => hrej c' (Nat.zero_le _) (by omega))
  unfold FullGame.authenticatedSign
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc]
  change (.inl (.inr X) : SigGolfCandidate.T3.Spec.Domain) ∈ queried A (WCT9.Rev3.signPayload request.cache request.message)
  rw [BPB.signPayload_nonce, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateNonce]
  apply List.mem_append_right
  unfold BPB.payloadForNonce
  rw [queried_bind]
  exact List.mem_append_left _ hq
theorem seen_events_self (U : Finset HashInput) (events : List FirstHit.QueryEvent) (st : RouterState)
    (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) (he : (⟨b, .inl (.inr X), y⟩ : FirstHit.QueryEvent) ∈ events) :
    X ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => cases he
  | cons e rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact seen_events_mono' U rest _ X (seen_event_self U st b X y)
      · exact ih _ he
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (digestIndex IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactCertClean : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem exists_pos_digit (r : WCT9.Rank) : ∃ t : Fin 7, 1 ≤ WCT9.wordDigit r t := by
  by_contra h
  push Not at h
  have hz : ∀ t ∈ (Finset.univ : Finset (Fin 7)), WCT9.wordDigit r t = 0 := fun t _ => by have := h t; omega
  have := WCT9.wordStep_count r
  rw [Finset.sum_eq_zero hz] at this
  omega
theorem cert_of_clean (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) (hcomp : BPB.SignerComplete z.2) :
    CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  set U := Wots.referenceInputs adversary with hUdef
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun U z.2 q g.value.2 t.steps c.events).contact = false := by simpa using hmon
  intro g' t' c' hsplit'
  obtain ⟨rfl, rfl, rfl⟩ := taggedSplit_unique hsplit hsplit'
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have hpk : g.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  obtain ⟨hlen, forgery, hf, hfresh, m, w, hof, hv, hsub⟩ :=
    WotsExtract.verdict_accepting g.value.1 t.value t.state c hc z.2 hac hcval
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_route z.2 m g.value.1 w hpk hv
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun U z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le U z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hXU : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events → X ∈ U := by
    intro X prior hev
    have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
    have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    rw [← hev'] at hmem
    exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
  have hclearV : ∀ X prior, (⟨prior, .inl (.inr X), z.2 (.inl (.inr X))⟩ : FirstHit.QueryEvent) ∈ c.events →
      Clear z.2 (monitorRun U z.2 q g.value.2 t.steps c.events).known X (z.2 (.inl (.inr X))) := by
    intro X prior hev
    have hseen := events_seen U z.2 q c.events _ hmon' _ hev X rfl
    exact monitorRun_clear U z.2 q g.value.2 t.steps c.events hsteps hverdict hmon' hcalls X hseen
      (hXU X prior hev)
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    exact (hclearV X prior hev).mono fun d hd =>
      monitorRun_known U z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, hqF⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgood, hfts, hcomp⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  have hsd : ¬BPB.SignedDigest t.value.2 m w := fun hsd =>
    BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩
  refine ⟨hcval, hmon', hcalls, ?_⟩
  set st := routerFold U z.2 g.value.2 t.steps c.events with hst
  have hlog : t.value.2 = stepLog t.steps := taggedRecord_log _ _ _ t ht
  have halive : st.exposures.length ≤ CaseC.horizon := by
    have h1 : st.exposures.length ≤ signCount t.steps := exposures_fold_le U z.2 g.value.2 t.steps c.events
    rw [signCount_eq_length, ← hlog] at h1
    have : CaseC.horizon = 2 ^ 32 := rfl
    omega
  refine ⟨halive, ?_⟩
  by_cases hr : st.reused = true
  · exact Or.inl hr
  right
  set Xs := pad64 (digestInput (wrho w) m (wdc w)) with hXs
  have hXsU : Xs ∈ U := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    exact hXU Xs prior hev
  have hXsd : IsDigestRow Xs := ⟨wrho w, m, wdc w, rfl⟩
  have hres' := BPB.logged_resolves g.value.2 (adversary g.value.1 g.value.2) g.state (t.untag.value, t.untag.state)
    (FirstHit.recorded_support _ _ _ hu)
  have hagree' : ∀ input answer, SourceReplay.known t.state input = some answer → z.2 input = answer :=
    fun input answer h => hac input answer (SourceReplay.known_mono _ _ htc h)
  have hnot := BPB.caseC_fresh_not_signer z.2 g.value.2 t.value.2 t.state hres' hagree' m w hcomp hsd
  have hnotrial : Xs ∉ (t.steps.foldl (routerStep U z.2 (honestNonce z.2) g.value.2) RouterState.initial).trials := by
    intro hm
    rcases trials_steps U z.2 g.value.2 t.steps RouterState.initial Xs hm with h0 | ⟨r, o, e, hmem, hcr, hrow⟩
    · cases h0
    · have hq' := trialRows_queried z.2 g.value.2 r hcr Xs hrow
      have hlogm : (⟨r, o⟩ : (r : Requests.Domain) × Requests.Range r) ∈ t.value.2 := by
        rw [hlog]; exact sign_mem_stepLog hmem
      exact hnot _ hlogm hq'
  have hansSteps : ∀ s ∈ t.steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro s hs e hse b y he
    have h1 := hsteps s hs e hse (by rw [he]; trivial)
    rw [he] at h1
    exact h1.symm.trans hNz
  have hansV : ∀ e ∈ c.events, ∀ b y, e = ⟨b, .inl (.inr Xs), y⟩ → y = N := by
    intro e he b y hee
    have h1 := hverdict e he (by rw [hee]; trivial)
    rw [hee] at h1
    exact h1.symm.trans hNz
  have hbirth : (Xs, N) ∈ st.births := by
    have hI := birthInv_steps U z.2 g.value.2 Xs N hXsU hXsd t.steps hansSteps RouterState.initial hnotrial
      (fun h => by cases h)
    have hI2 := birthInv_events U Xs N hXsU hXsd c.events hansV _ hnotrial hI
    obtain ⟨prior, hev⟩ := hsub _ hdq
    apply hI2
    exact seen_events_self U c.events _ prior Xs _ hev
  refine ⟨(Xs, N), hbirth, hS, ?_⟩
  have hposCov : ∀ (k : WCT9.Coord) (t : Fin 7), 1 ≤ WCT9.wordDigit (WCT9.rank N k) t →
      ∃ x ∈ st.exposures, ClaudeWCT.Bank.WCT.outIdx x = ClaudeWCT.Bank.WCT.outIdx N ∧
        WCT9.child x k = WCT9.child N k ∧ WCT9.wordDigit (WCT9.rank N k) t ≤ WCT9.wordDigit (WCT9.rank x k) t := by
    intro k tt hu1
    have hu3 : WCT9.wordDigit (WCT9.rank N k) tt ≤ 3 := WCT9.wordDigit_le_three _ _
    set a : CanonGraph.WctAddr := (digestIndex N, k, WCT9.child N k, tt) with ha
    set s : Fin 3 := ⟨3 - WCT9.wordDigit (WCT9.rank N k) tt, by omega⟩ with hs
    have hq0 := CaseC.recoverFtsP_chain_queried z.2 N w k tt hu1
    obtain ⟨hval, hpad⟩ := (hfts.2 k).1 tt
    rw [hval, (hpad hu1).1, (hpad hu1).2] at hq0
    have hX : (.inl (.inr (pad64 (wctChainInputP (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val tt.val
        (3 - WCT9.wordDigit (WCT9.rank N k) tt) ((0, 0) : Digest × Digest).1 0 ((0, 0) : Digest × Digest).2
        (Extract.wctValue z.2 (N.toNat % 2 ^ 31) k.val (WCT9.child N k).val tt.val
          (3 - WCT9.wordDigit (WCT9.rank N k) tt))))) : Spec.Domain) =
        .inl (.inr (Extract.honestInput z.2 (CanonGraph.Node.wctChain (a, s)).toPos)) := by
      rw [wctChainInputP_zero]
      rfl
    rw [hX] at hq0
    obtain ⟨prior, hev⟩ := hsub _ (hqF _ hq0)
    have hcl := hclearV _ prior hev
    have hk := hcl.2.1 (CanonGraph.Node.wctChain (a, s)) (posOf_honest_wctChain z.2 a s) (wctItem a s.val) 3 rfl
      (slotValue_honest_wctChain z.2 a s)
    obtain ⟨p', hp', hd⟩ := known_wctItem (by omega) hk
    rcases hd with hkg | hkd
    · exact (keygen_not_wct a p' hkg).elim
    have hkd' : wctItem a p' ∈ (t.steps.foldl (Monitor.step U z.2 q g.value.2) Monitor.initial).disclosed := by
      unfold monitorRun at hkd
      rwa [disclosed_events] at hkd
    rcases disclosed_steps_mem U z.2 q g.value.2 t.steps Monitor.initial _ hkd' with h0 | ⟨r, o, e, hmem, hdis⟩
    · cases h0
    unfold signDisclosed at hdis
    split_ifs at hdis with hcr
    · rcases hsr : LargeResidual.signDigest z.2 r.message with _ | ⟨c', N'⟩
      · rw [hsr] at hdis; cases hdis
      · rw [hsr] at hdis
        dsimp only at hdis
        split_ifs at hdis with hok
        · have hp3 : p' ≤ 3 := by omega
          obtain ⟨hidx, hchild, hpos⟩ := wctItem_mem_signItemsWith _ N' a p' hp3 hdis
          have hd3 : WCT9.wordDigit (WCT9.rank N' k) tt ≤ 3 := WCT9.wordDigit_le_three _ _
          rcases covered_fold U z.2 g.value.2 t.steps c.events r o e hmem hcr c' N' hsr with hx | hx
          · refine ⟨N', hx, ?_, hchild.symm, ?_⟩
            · exact Fin.ext (congrArg Fin.val hidx).symm
            · simp only [ha] at hpos
              simp only [hs, Fin.val_mk] at hp'
              omega
          · exact (hr hx).elim
        · cases hdis
    · cases hdis
  show ClaudeWCT.Bank.WCT.Covered st.exposures N
  intro k tt
  by_cases hu : 1 ≤ WCT9.wordDigit (WCT9.rank N k) tt
  · exact hposCov k tt hu
  · obtain ⟨t', ht'⟩ := exists_pos_digit (WCT9.rank N k)
    obtain ⟨x, hx, hidx, hch, -⟩ := hposCov k t' ht'
    exact ⟨x, hx, hidx, hch, by omega⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
end
