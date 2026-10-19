import SigGolfCandidate.T3_Secc_LargeResidualT3
import SigGolfCandidate.T3_Secc_WotsReference

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
  | world (event : FirstHit.QueryEvent)
  | sign (request : Security.Request) (output : Option Signature) (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
  | .world event => [event]
  | .sign _ _ events => events
structure Tagged (α : Type) where
  value : α × QueryLog Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache)) (tagged : Tagged (Option ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
end SigGolfCandidate.T3.Security.LargeCoupling
