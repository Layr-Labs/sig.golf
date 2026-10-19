import SigGolfCandidate.T3_Secc_WotsTransportTable
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTransportR3
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTransportShort
import SigGolfCandidate.ClaudeWCT_W9_New_G3b_Shared
set_option Elab.async false

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem verdict_hashOnly (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) :
    Security.SourceReplay.HashOnly (GameWith.verdict PaddedGame.checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (PaddedExtraction.check_hashOnly publicKey result.2 forgery)
        fun _ => SourceQueries.pure_allowed _ _
noncomputable def verdictCharge (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Nat :=
  (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)).length
theorem verdict_accepts (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests)
    (h : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true) :
    ∃ forgery, result.1 = some forgery ∧
      evalWithAnswerFn T (checkForgeryP publicKey result.2 forgery) = true ∧
      ∀ query ∈ SourceReplay.queried T (checkForgeryP publicKey result.2 forgery),
        query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result) := by
  cases hf : result.1 with
  | none =>
      simp only [GameWith.verdict, hf, evalWithAnswerFn_pure] at h
      exact absurd h (by decide)
  | some forgery =>
      refine ⟨forgery, rfl, ?_, ?_⟩
      · simp only [GameWith.verdict, hf, PaddedGame.checker, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      · intro query hq
        simp only [GameWith.verdict, hf, PaddedGame.checker, SourceReplay.queried_bind, SourceReplay.queried_pure,
          List.append_nil]
        exact hq
theorem witnessOf_unique {answers : Answers} {publicKey : Digest} {forgery : ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : PaddedExtraction.WitnessOf answers publicKey forgery m w)
    (h' : PaddedExtraction.WitnessOf answers publicKey forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨rfl, hw'⟩ := h'
      exact ⟨rfl, Option.some.inj (hw.symm.trans hw')⟩
noncomputable def verdictRecord (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  pureRecord T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) interaction.state
noncomputable def combine (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  ⟨(verdictRecord T interaction).value,
    (pureRecord T keygen (∅, ∅)).events ++ (interaction.events ++ (verdictRecord T interaction).events),
    (verdictRecord T interaction).state⟩
noncomputable def fixedInteraction (adversary : AdversaryP) (T : Answers) :
    ProbComp (FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :=
  fixedRecord T (FullGame.loggedWith (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)) (pureRecord T keygen (∅, ∅)).state
theorem fixed_game_eq (adversary : AdversaryP) (T : Answers) :
    fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) =
      combine T <$> fixedInteraction adversary T := by
  unfold GameWith.idealGame
  rw [fixedRecord_bind, fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, pure_bind]
  simp only [pureRecord_value]
  rw [fixedRecord_bind]
  simp only [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), pure_bind, bind_assoc]
  unfold fixedInteraction combine verdictRecord
  rw [map_eq_bind_pure_comp]
  rfl
end Ref
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF
def GameSplit (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
theorem check_hashOnly (pk : Digest) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) :
    Security.SourceReplay.HashOnly (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP pk log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (PairedOuter.PaddedGame.check_public pk log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem verdict_hashOnly (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :
    Security.SourceReplay.HashOnly (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) := by
  unfold PairedOuter.GameWith.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (check_hashOnly publicKey result.2 forgery)
        fun _ => SourceQueries.pure_allowed _ _
noncomputable def verdictCharge (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Nat :=
  (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result)).length
theorem verdict_accepts (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (h : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true) :
    ∃ forgery, result.1 = some forgery ∧
      evalWithAnswerFn T (checkForgeryP publicKey result.2 forgery) = true ∧
      ∀ query ∈ SourceReplay.queried T (checkForgeryP publicKey result.2 forgery),
        query ∈ SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) := by
  cases hf : result.1 with
  | none =>
      simp only [PairedOuter.GameWith.verdict, hf, evalWithAnswerFn_pure] at h
      exact absurd h (by decide)
  | some forgery =>
      refine ⟨forgery, rfl, ?_, ?_⟩
      · simp only [PairedOuter.GameWith.verdict, hf, PairedOuter.PaddedGame.checker, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      · intro query hq
        simp only [PairedOuter.GameWith.verdict, hf, PairedOuter.PaddedGame.checker, SourceReplay.queried_bind, SourceReplay.queried_pure,
          List.append_nil]
        exact hq
theorem witnessOf_unique {answers : Answers} {publicKey : Digest} {forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : ClaudeWCT.W9.T3M.Final.Paired.WitnessOf answers publicKey forgery m w)
    (h' : ClaudeWCT.W9.T3M.Final.Paired.WitnessOf answers publicKey forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨rfl, hw'⟩ := h'
      exact ⟨rfl, Option.some.inj (hw.symm.trans hw')⟩
noncomputable def verdictRecord (T : Answers) (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :
    FirstHit.Recorded Bool :=
  pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) interaction.state
noncomputable def combine (T : Answers) (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :
    FirstHit.Recorded Bool :=
  ⟨(verdictRecord T interaction).value,
    (pureRecord T keygen (∅, ∅)).events ++ (interaction.events ++ (verdictRecord T interaction).events),
    (verdictRecord T interaction).state⟩
noncomputable def fixedInteraction (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) :
    ProbComp (FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) :=
  fixedRecord T (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)) (pureRecord T keygen (∅, ∅)).state
theorem fixed_game_eq (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) :
    fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅) =
      combine T <$> fixedInteraction adversary T := by
  unfold PairedOuter.GameWith.idealGame
  rw [fixedRecord_bind, fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, pure_bind]
  simp only [pureRecord_value]
  rw [fixedRecord_bind]
  simp only [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), pure_bind, bind_assoc]
  unfold fixedInteraction combine verdictRecord
  rw [map_eq_bind_pure_comp]
  rfl
end Ref
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
