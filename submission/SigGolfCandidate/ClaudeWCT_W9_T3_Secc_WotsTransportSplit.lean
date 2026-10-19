import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTransportTable
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsExtractVerify
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CaseCSplit
set_option Elab.async false

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem GameSplit.extends {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)}
    {interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem GameSplit.extends {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)}
    {interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem logged_resolves {α : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp (SphincsSecurity.OracleWorld + ClaudeWCT.W9.T3M.Final.Paired.Requests) α)
    (before : LazyPrivate.State) (result : (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)
      before)) :
    ∀ entry ∈ result.1.2, SourceReplay.Resolves result.2 (PairedOuter.FullGame.authenticatedSign published entry.1) entry.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [PairedOuter.FullGame.loggedWith_pure, LazyPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [PairedOuter.FullGame.loggedWith_world, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, _, hr⟩ := hr
          exact ih middle.1 middle.2 result hr
      | inr request =>
          rw [PairedOuter.FullGame.loggedWith_request, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, hm, hr⟩ := hr
          rw [LazyPrivate.run_map, support_map] at hr
          obtain ⟨last, hl, rfl⟩ := hr
          intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            exact (SourceReplay.resolves_of_run _ (Ref.authenticatedSign_hashOnly published request)
              before middle hm).mono (SourceReplay.run_extends _ middle.2 last hl)
          · exact ih middle.1 middle.2 last hl entry he

theorem GameSplit.facts {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (T : Answers)
    (hknown : ∀ input answer, SourceReplay.known result.state input = some answer → T input = answer)
    (hwin : result.value = true) :
    evalWithAnswerFn T keygen = generated.value ∧
    generated.value.1 = Extract.honestRoot T 0 0 ∧
    generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop T) ∧
    (∀ entry ∈ interaction.value.2,
      entry.2 = evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 interaction.value) = true := by
  obtain ⟨hg,hi,hc,heq⟩ := h
  have hstate : result.state = checked.state := by rw [heq]
  have hvalue : result.value = checked.value := by rw [heq]
  have hiext : SourceReplay.Extends interaction.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ interaction.state (checked.value,checked.state)
      (FirstHit.recorded_support _ _ _ hc)
  have hgext : SourceReplay.Extends generated.state result.state :=
    (SourceReplay.run_extends _ generated.state (interaction.value, interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hiext
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → T input = answer :=
    fun input answer hk => hknown input answer (SourceReplay.known_mono _ _ hiext hk)
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → T input = answer := by
    rw [← hstate]; exact hknown
  have hgen : evalWithAnswerFn T keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
      (generated.value,generated.state) (FirstHit.recorded_support _ _ _ hg)).eval T
      (fun input answer hk => hknown input answer (SourceReplay.known_mono _ _ hgext hk))
  refine ⟨hgen,?_,?_,?_,?_⟩
  · rw [← hgen]; exact Extract.keygen_pk T
  · rw [← hgen]; exact (Correctness.keygen_correct T).2.1
  · intro entry he
    exact ((logged_resolves generated.value.2 _ generated.state _
      (FirstHit.recorded_support _ _ _ hi) entry he).eval T hai).symm
  · rw [(SourceReplay.resolves_of_run _ (Ref.verdict_hashOnly _ _) interaction.state
      (checked.value,checked.state) (FirstHit.recorded_support _ _ _ hc)).eval T hac]
    rw [← hvalue]; exact hwin
#print axioms logged_resolves
#print axioms GameSplit.facts
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem GameSplit.checker_event {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (hA : CaseC.Agrees A result.state)
    (forgery : Final.Paired.ForgeryP) (hf : interaction.value.1=some forgery)
    (input : SigGolfCandidate.T3.Spec.Domain)
    (hq : input ∈ queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)) :
    ∃ prior, (⟨prior,input,A input⟩ : FirstHit.QueryEvent) ∈ checked.events := by
  obtain ⟨hg,hi,hc,heq⟩ := h
  have hstate : result.state=checked.state := by rw [heq]
  have hac : CaseC.Agrees A checked.state := by rwa [←hstate]
  have hsub : input ∈ SourceReplay.queried A
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 interaction.value) := by
    unfold PairedOuter.GameWith.verdict
    simp only [hf]
    change input ∈ queried A (_ >>= _)
    rw [SigGolfCandidate.T3M.SecurityExtraction.queried_bind]
    exact List.mem_append_left _ hq
  have hevents := FirstHit.recorded_inputs _ (Ref.verdict_hashOnly _ _) interaction.state checked hc A hac
  rw [←hevents] at hsub
  obtain ⟨event,hevent,heinput⟩ := List.mem_map.mp hsub
  have hk := (FirstHit.recorded_query_known _ (Ref.verdict_hashOnly _ _) interaction.state checked hc event hevent).1
  have ha := hac event.input event.answer hk
  rcases event with ⟨prior,eventInput,answer⟩
  simp only at heinput ha
  subst eventInput
  subst answer
  exact ⟨prior,hevent⟩

theorem GameSplit.checked_mem {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    {event : FirstHit.QueryEvent} (he : event ∈ checked.events) : event ∈ result.events := by
  rw [h.2.2.2]
  exact List.mem_append_right _ (List.mem_append_right _ he)
#print axioms GameSplit.checker_event
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
