import SigGolfCandidate.ClaudeWCT_W9_T3_BPORS
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEvents
import SigGolfCandidate.T3_Secc_WotsReference

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9WotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_w9WotsReference :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def signCharge (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : SigGolfCandidate.T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + Requests) α) : OracleComp RefWorld (α × QueryLog Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def offlineRun (T : Answers) (adversary : AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)
noncomputable def referenceComp (adversary : AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9WotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_w9WotsReference :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def signCharge (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option SigGolfCandidate.Research.SharedForest.Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : SigGolfCandidate.T3.Cache) :
    QueryImpl (OracleWorld + ClaudeWCT.W9.T3M.Final.Paired.Requests) (WriterT (QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + ClaudeWCT.W9.T3M.Final.Paired.Requests) α) : OracleComp RefWorld (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def offlineRun (T : Answers) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
noncomputable def referenceInputs (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary)
noncomputable def referenceComp (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem referenceGame_congr (T T' : Answers)
    (hkey : evalWithAnswerFn T keygen = evalWithAnswerFn T' keygen)
    (hkeyCharge : (SigGolfCandidate.T3.Security.SourceReplay.queried T keygen).length =
      (SigGolfCandidate.T3.Security.SourceReplay.queried T' keygen).length)
    (hsign : ∀ published request,
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) =
        evalWithAnswerFn T' (PairedOuter.FullGame.authenticatedSign published request))
    (hsignCharge : ∀ published request,
      (SigGolfCandidate.T3.Security.SourceReplay.queried T (PairedOuter.FullGame.authenticatedSign published request)).length =
        (SigGolfCandidate.T3.Security.SourceReplay.queried T' (PairedOuter.FullGame.authenticatedSign published request)).length)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    referenceGame T adversary q = referenceGame T' adversary q := by
  have hs (published : SigGolfCandidate.T3.Cache) (request : Request) :
      offlineSign T published request = offlineSign T' published request := by
    unfold offlineSign signCharge
    rw [hsignCharge published request,hsign published request]
  have hi (published : SigGolfCandidate.T3.Cache) :
      offlineImpl T published = offlineImpl T' published := by
    unfold offlineImpl
    have he : offlineSign T published = offlineSign T' published := funext (hs published)
    rw [he]
  have hk : keygenCharge T = keygenCharge T' := hkeyCharge
  unfold referenceGame offlineGame offlineInteraction
  rw [hk,hkey,hi]
end ClaudeWCT.W9.T3.Security.Wots.PairedReference
